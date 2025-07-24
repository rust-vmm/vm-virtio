// Copyright 2022 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

//! Virtio console chain processing abstraction.
//!
//! This module offers an abstraction for working with the descriptor chains of the receive and
//! transmit queues.
//!  * The transmit queue is used to send data from the driver to the device and it's buffers are
//!    read-only for the device.
//!  * The receive queue is used to send data from the device to the driver and it's buffers are
//!    write-only for the device.

use std::cmp;
use std::fmt::{self, Display};
use std::io::{stdout, Stdout, Write};
use std::ops::Deref;
use std::sync::{Arc, Mutex};
use virtio_queue::DescriptorChain;
use vm_memory::{Bytes, GuestMemory, GuestMemoryError, WriteVolatile};

/// Console device errors.
#[derive(Debug)]
pub enum Error {
    /// Failed to write slice to guest memory.
    WriteToGuestFailed(GuestMemoryError),
    /// Write to output sink failed.
    WriteToOutputFailed(GuestMemoryError),
    /// Transmitq descriptor chain length has overflown
    ChainLengthOverflow,
    /// Input buffer maximum capacity exceeded
    BufferCapacityExceeded,
    /// Read only descriptor that protocol says to write to.
    UnexpectedReadOnlyDescriptor,
    /// Write only descriptor that protocol says to read from.
    UnexpectedWriteOnlyDescriptor,
    /// The capacity passed to the constructor is either 0 or higher than [`MAX_CAPACITY`].
    InvalidBufferCapacity,
    /// Output sink flush has not written all bytes.
    OutputSinkFlushFailed(std::io::Error),
}

impl Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Error::*;

        match self {
            WriteToGuestFailed(ref err) => {
                write!(f, "Console failed to write slice to guest memory: {err}")
            }
            WriteToOutputFailed(ref err) => {
                write!(f, "Console failed to write data to output sink: {err}")
            }
            ChainLengthOverflow => {
                write!(f, "Console transmitq chain length has overflown usize.")
            }
            BufferCapacityExceeded => {
                write!(
                    f,
                    "Console input buffer maximum capacity has been exceeded."
                )
            }
            UnexpectedReadOnlyDescriptor => {
                write!(f, "Unexpected read-only descriptor.")
            }
            UnexpectedWriteOnlyDescriptor => {
                write!(f, "Unexpected write-only descriptor.")
            }
            InvalidBufferCapacity => {
                write!(
                    f,
                    "The capacity should not be 0 or higher than MAX_CAPACITY."
                )
            }
            OutputSinkFlushFailed(ref err) => {
                write!(f, "Output sink flush has not written all bytes: {err}")
            }
        }
    }
}

/// Console struct that implements the abstraction of virtio console descriptor chain handling.
#[derive(Clone, Debug)]
pub struct Console<T: Write + WriteVolatile> {
    /// Buffer that stores data to be sent to the driver.
    input_buffer: Arc<Mutex<Vec<u8>>>,
    /// Capacity of the input buffer.
    capacity: usize,
    /// Output sink.
    output: T,
}

// TODO: Find the optimal DEFAULT_CAPACITY and MAX_CAPACITY through testing
/// Maximum capacity of `input_buffer`.
pub const MAX_CAPACITY: usize = 16384;

/// Default capacity of `input_buffer`.
///
/// The value has been chosen to be the same size as the hvc console that is allocated in the linux
/// [virtio console driver](https://github.com/torvalds/linux/blob/master/drivers/char/virtio_console.c#L1249).
/// The value used in the kernel is `PAGE_SIZE` which is usually 4kB.
pub const DEFAULT_CAPACITY: usize = 4096;

impl Default for Console<Stdout> {
    fn default() -> Self {
        // It is safe to unwrap here since we are using DEFAULT_CAPACITY.
        Self::new_with_capacity(DEFAULT_CAPACITY, stdout()).unwrap()
    }
}

impl<T> Console<T>
where
    T: Write + WriteVolatile,
{
    /// Create new console object with the default `capacity`.
    ///
    /// # Arguments
    ///
    /// * `output` - The output sink where all the data received from the transmitq will be written.
    ///
    /// # Returns
    ///
    /// The console object.
    pub fn new(output: T) -> Self {
        Self::new_with_capacity(DEFAULT_CAPACITY, output).unwrap()
    }

    /// Create new console object with specified `capacity`.
    ///
    /// # Arguments
    ///
    /// * `capacity` - The capacity of the input buffer.
    /// * `output` - The output sink where all the data received from the transmitq will be written.
    ///
    /// # Returns
    ///
    /// The console object or an `Error` if the capacity is 0 or higher than [`MAX_CAPACITY`].
    pub fn new_with_capacity(capacity: usize, output: T) -> Result<Self, Error> {
        // There is no use case for 0 capacity
        if capacity == 0 || capacity > MAX_CAPACITY {
            return Err(Error::InvalidBufferCapacity);
        }
        Ok(Console {
            input_buffer: Arc::new(Mutex::new(Vec::new())),
            capacity,
            output,
        })
    }

    /// Adds data in the form of raw bytes to the input buffer.
    ///
    /// The contents of the `Vec<u8>` sent as parameter will be moved to the input buffer.
    /// If the length of the two combined vectors exceeds the maximum capacity an error will be
    /// returned.
    ///
    /// # Arguments
    ///
    /// * `data` - A mutable reference to a `Vec<u8>` containing the raw bytes that will be sent to the driver when the `process_receiveq_chain` method is called.
    pub fn enqueue_data(&self, data: &mut Vec<u8>) -> Result<(), Error> {
        let mut input_buffer = self.input_buffer.lock().unwrap();
        let total_length = input_buffer
            .len()
            .checked_add(data.len())
            .ok_or(Error::BufferCapacityExceeded)?;
        if total_length > self.capacity {
            return Err(Error::BufferCapacityExceeded);
        }
        input_buffer.append(data);

        Ok(())
    }

    /// Returns the maximum number of bytes that can be added to the buffer.
    pub fn available_capacity(&self) -> usize {
        let input_buffer = self.input_buffer.lock().unwrap();
        // Operation cannot underflow because any addition to the `input_buffer`
        // is checked against `capacity`.
        self.capacity - input_buffer.len()
    }

    /// Clear the input buffer.
    pub fn clear_input_buffer(&self) {
        let mut input_buffer = self.input_buffer.lock().unwrap();
        input_buffer.clear();
    }

    /// Checks if input buffer is empty.
    pub fn is_input_buffer_empty(&self) -> bool {
        let input_buffer = self.input_buffer.lock().unwrap();
        input_buffer.is_empty()
    }

    /// Read data from a `desc_chain` of the transmit queue and write it to the output sink.
    ///
    /// # Arguments
    ///
    /// * `desc_chain` - A mutable reference to the descriptor chain that should point to the buffers that the virtio console driver has sent to the device.
    pub fn process_transmitq_chain<M>(
        &mut self,
        desc_chain: &mut DescriptorChain<M>,
    ) -> Result<(), Error>
    where
        M: Deref,
        M::Target: GuestMemory,
    {
        // Iterate through all the buffers in the chain and write the data to output.
        while let Some(desc) = desc_chain.next() {
            if desc.is_write_only() {
                return Err(Error::UnexpectedWriteOnlyDescriptor);
            }
            desc_chain
                .memory()
                .write_volatile_to(desc.addr(), &mut self.output, desc.len() as usize)
                .map_err(Error::WriteToOutputFailed)?;

            self.output.flush().map_err(Error::OutputSinkFlushFailed)?;
        }

        Ok(())
    }

    /// Takes data from the input buffer and writes it to guest memory in the specified
    /// descriptor chain.
    ///
    /// The empty descriptor chain in which the data is written has previously
    /// been added to the receive queue by the driver.
    /// If there are not enough buffers to hold all the data, we stop and wait for the driver to
    /// add more.
    ///
    /// # Arguments
    ///
    /// * `desc_chain` - A mutable reference to the descriptor chain that should point to the empty buffers that the virtio driver has offered the device.
    ///
    /// # Returns
    ///
    /// The number of raw bytes written to guest memory.
    pub fn process_receiveq_chain<M>(
        &self,
        desc_chain: &mut DescriptorChain<M>,
    ) -> Result<u32, Error>
    where
        M: Deref,
        M::Target: GuestMemory,
    {
        // Acquire lock on buffer to make sure no other thread is adding data to it while it is
        // being processed.
        let mut input_buffer = self.input_buffer.lock().unwrap();
        let mut sent_bytes: u32 = 0;

        // When the driver adds a new descriptor chain to the receive queue this method will be
        // called to write the remaining data to the newly provided buffers. If there is no
        // remaining data waiting to be sent it can return 0.
        if input_buffer.is_empty() {
            return Ok(0);
        }

        // Break up the data from the "input_buffer" into chunks that fit into the buffers of the
        // receive queue descriptor chain and write it to guest memory.
        while let Some(desc) = desc_chain.next() {
            if !desc.is_write_only() {
                return Err(Error::UnexpectedReadOnlyDescriptor);
            }
            // Length of the input_buffer is lower than MAX_CAPACITY so it is safe to cast to u32.
            let len_write = cmp::min(desc.len(), input_buffer.len() as u32);
            let buffer_slice = input_buffer
                .drain(..len_write as usize)
                .collect::<Vec<u8>>();

            desc_chain
                .memory()
                .write_slice(&buffer_slice, desc.addr())
                .map_err(Error::WriteToGuestFailed)?;

            // Should not overflow since "input_buffer" can hold a maximum of MAX_CAPACITY which is
            // lower than u32::MAX elements.
            sent_bytes += len_write;

            if input_buffer.is_empty() {
                break;
            }
        }

        Ok(sent_bytes)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use virtio_bindings::bindings::virtio_ring::VRING_DESC_F_WRITE;
    use virtio_queue::desc::{split::Descriptor as SplitDescriptor, RawDescriptor};
    use virtio_queue::mock::MockSplitQueue;
    use vm_memory::{GuestAddress, GuestMemoryMmap};

    impl PartialEq for Error {
        fn eq(&self, other: &Self) -> bool {
            use self::Error::*;
            match (self, other) {
                (WriteToGuestFailed(ref e), WriteToGuestFailed(ref other_e)) => {
                    format!("{e}").eq(&format!("{other_e}"))
                }
                (WriteToOutputFailed(ref e), WriteToOutputFailed(ref other_e)) => {
                    format!("{e}").eq(&format!("{other_e}"))
                }
                (ChainLengthOverflow, ChainLengthOverflow) => true,
                (BufferCapacityExceeded, BufferCapacityExceeded) => true,
                (UnexpectedReadOnlyDescriptor, UnexpectedReadOnlyDescriptor) => true,
                (UnexpectedWriteOnlyDescriptor, UnexpectedWriteOnlyDescriptor) => true,
                (InvalidBufferCapacity, InvalidBufferCapacity) => true,
                _ => false,
            }
        }
    }

    const INPUT_VALUE: u8 = 42;
    const INPUT_SIZE: u32 = 256;

    #[test]
    fn test_default_console() {
        // Default console
        let console1 = Console::default();
        assert_eq!(console1.capacity, DEFAULT_CAPACITY);
    }

    #[test]
    fn test_input_buffer_operations() {
        assert_eq!(
            Console::new_with_capacity(0, vec![0; DEFAULT_CAPACITY]).unwrap_err(),
            Error::InvalidBufferCapacity
        );

        assert_eq!(
            Console::new_with_capacity(MAX_CAPACITY + 1, vec![0; DEFAULT_CAPACITY]).unwrap_err(),
            Error::InvalidBufferCapacity
        );

        let console =
            Console::new_with_capacity(DEFAULT_CAPACITY, vec![0; DEFAULT_CAPACITY]).unwrap();
        console
            .enqueue_data(&mut vec![INPUT_VALUE; DEFAULT_CAPACITY])
            .unwrap();
        assert_eq!(
            console.enqueue_data(&mut vec![INPUT_VALUE; 1]).unwrap_err(),
            Error::BufferCapacityExceeded
        );

        console.clear_input_buffer();
        assert!(console.is_input_buffer_empty());
    }

    #[test]
    fn test_process_transmitq_chain() {
        let output: Vec<u8> = Vec::new();
        let mut console = Console::new_with_capacity(DEFAULT_CAPACITY, output).unwrap();

        let mem: GuestMemoryMmap =
            GuestMemoryMmap::from_ranges(&[(GuestAddress(0), 0x0001_0000)]).unwrap();

        // One descriptor is write only
        let v = [
            RawDescriptor::from(SplitDescriptor::new(0x1000, INPUT_SIZE, 0, 0)),
            RawDescriptor::from(SplitDescriptor::new(
                0x2000,
                INPUT_SIZE,
                VRING_DESC_F_WRITE as u16,
                0,
            )),
        ];

        let queue = MockSplitQueue::new(&mem, 16);
        // The `build_desc_chain` function will populate the `NEXT` related flags and field.
        let mut chain = queue.build_desc_chain(&v[..2]).unwrap();
        assert_eq!(
            console.process_transmitq_chain(&mut chain).unwrap_err(),
            Error::UnexpectedWriteOnlyDescriptor
        );

        // Descriptor is outside of the memory bounds
        let v = [
            RawDescriptor::from(SplitDescriptor::new(0x0001_0000, INPUT_SIZE, 0, 0)),
            RawDescriptor::from(SplitDescriptor::new(0x0002_0000, INPUT_SIZE, 0, 0)),
        ];
        let mut chain = queue.build_desc_chain(&v[..2]).unwrap();
        assert_eq!(
            console.process_transmitq_chain(&mut chain).unwrap_err(),
            Error::WriteToOutputFailed(GuestMemoryError::InvalidGuestAddress(GuestAddress(
                0x0001_0000
            )))
        );

        // Test normal functionality.
        let v = [
            RawDescriptor::from(SplitDescriptor::new(0x3000, INPUT_SIZE, 0, 0)),
            RawDescriptor::from(SplitDescriptor::new(0x4000, INPUT_SIZE, 0, 0)),
        ];
        let mut chain = queue.build_desc_chain(&v[..2]).unwrap();
        mem.write_slice(
            &vec![INPUT_VALUE; INPUT_SIZE as usize],
            GuestAddress(0x3000),
        )
        .unwrap();
        mem.write_slice(
            &vec![INPUT_VALUE * 2; INPUT_SIZE as usize],
            GuestAddress(0x4000),
        )
        .unwrap();
        console.output.clear();
        console.process_transmitq_chain(&mut chain).unwrap();
        assert_eq!(
            console.output[..INPUT_SIZE as usize],
            vec![INPUT_VALUE; INPUT_SIZE as usize]
        );
        assert_eq!(
            console.output[INPUT_SIZE as usize..],
            vec![INPUT_VALUE * 2; INPUT_SIZE as usize]
        );
    }

    #[test]
    fn test_process_receiveq_chain() {
        let buf = &mut [0u8; INPUT_SIZE as usize];
        let console = Console::new_with_capacity(DEFAULT_CAPACITY, Vec::new()).unwrap();

        console
            .enqueue_data(&mut vec![INPUT_VALUE; INPUT_SIZE as usize])
            .unwrap();

        let mem: GuestMemoryMmap =
            GuestMemoryMmap::from_ranges(&[(GuestAddress(0), 0x0001_0000)]).unwrap();

        // One descriptor is read only
        let v = [
            RawDescriptor::from(SplitDescriptor::new(
                0x1000,
                0x10,
                VRING_DESC_F_WRITE as u16,
                0,
            )),
            RawDescriptor::from(SplitDescriptor::new(0x2000, INPUT_SIZE, 0, 0)),
        ];

        let queue = MockSplitQueue::new(&mem, 16);
        // The `build_desc_chain` function will populate the `NEXT` related flags and field.
        let mut chain = queue.build_desc_chain(&v[..2]).unwrap();
        assert_eq!(
            console.process_receiveq_chain(&mut chain).unwrap_err(),
            Error::UnexpectedReadOnlyDescriptor
        );

        // Descriptor is out of memory bounds
        let v = [
            RawDescriptor::from(SplitDescriptor::new(
                0x0001_0000,
                INPUT_SIZE,
                VRING_DESC_F_WRITE as u16,
                0,
            )),
            RawDescriptor::from(SplitDescriptor::new(
                0x0002_0000,
                INPUT_SIZE,
                VRING_DESC_F_WRITE as u16,
                0,
            )),
        ];

        let queue = MockSplitQueue::new(&mem, 16);
        let mut chain = queue.build_desc_chain(&v[..2]).unwrap();
        assert_eq!(
            console.process_receiveq_chain(&mut chain).unwrap_err(),
            Error::WriteToGuestFailed(GuestMemoryError::InvalidGuestAddress(GuestAddress(
                0x0001_0000
            )))
        );

        // Test normal functionality
        console.clear_input_buffer();
        console
            .enqueue_data(&mut vec![INPUT_VALUE; INPUT_SIZE as usize])
            .unwrap();
        console
            .enqueue_data(&mut vec![INPUT_VALUE * 2; INPUT_SIZE as usize])
            .unwrap();
        let v = [
            RawDescriptor::from(SplitDescriptor::new(
                0x3000,
                INPUT_SIZE,
                VRING_DESC_F_WRITE as u16,
                0,
            )),
            RawDescriptor::from(SplitDescriptor::new(
                0x4000,
                INPUT_SIZE,
                VRING_DESC_F_WRITE as u16,
                0,
            )),
        ];

        let queue = MockSplitQueue::new(&mem, 16);
        let mut chain = queue.build_desc_chain(&v[..2]).unwrap();
        assert_eq!(
            console.process_receiveq_chain(&mut chain).unwrap(),
            2 * INPUT_SIZE
        );

        mem.read_slice(buf, GuestAddress(0x3000)).unwrap();
        assert_eq!(buf, &mut [INPUT_VALUE; INPUT_SIZE as usize]);

        mem.read_slice(buf, GuestAddress(0x4000)).unwrap();
        assert_eq!(buf, &mut [INPUT_VALUE * 2; INPUT_SIZE as usize]);

        // Cannot write all the content of input buffer into guest memory
        console.clear_input_buffer();
        console
            .enqueue_data(&mut vec![INPUT_VALUE; 2 * INPUT_SIZE as usize])
            .unwrap();
        let v = [RawDescriptor::from(SplitDescriptor::new(
            0x5000,
            INPUT_SIZE,
            VRING_DESC_F_WRITE as u16,
            0,
        ))];

        let queue = MockSplitQueue::new(&mem, 16);
        let mut chain = queue.build_desc_chain(&v[..1]).unwrap();

        assert_eq!(
            console.process_receiveq_chain(&mut chain).unwrap(),
            INPUT_SIZE
        );

        mem.read_slice(buf, GuestAddress(0x5000)).unwrap();
        assert_eq!(buf, &mut [INPUT_VALUE; INPUT_SIZE as usize]);

        assert!(!console.is_input_buffer_empty());

        let v = [RawDescriptor::from(SplitDescriptor::new(
            0x6000,
            INPUT_SIZE,
            VRING_DESC_F_WRITE as u16,
            0,
        ))];
        let mut chain = queue.build_desc_chain(&v[..1]).unwrap();

        assert_eq!(
            console.process_receiveq_chain(&mut chain).unwrap(),
            INPUT_SIZE
        );

        mem.read_slice(buf, GuestAddress(0x6000)).unwrap();
        assert_eq!(buf, &mut [INPUT_VALUE; INPUT_SIZE as usize]);

        assert!(console.is_input_buffer_empty());

        // Input buffer is empty.
        let v = [RawDescriptor::from(SplitDescriptor::new(
            0x7000,
            INPUT_SIZE,
            VRING_DESC_F_WRITE as u16,
            0,
        ))];
        let mut chain = queue.build_desc_chain(&v[..1]).unwrap();

        assert_eq!(console.process_receiveq_chain(&mut chain).unwrap(), 0);
    }
}
