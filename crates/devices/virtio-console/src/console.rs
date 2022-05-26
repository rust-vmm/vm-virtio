// Copyright 2022 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause
use std::cmp;
use std::fmt::{self, Display};
use std::io::Write;
use std::ops::Deref;
use std::sync::{Arc, Mutex};
use virtio_queue::DescriptorChain;
use vm_memory::{Bytes, GuestMemory, GuestMemoryError};

/// Virtio console chain processing abstraction.
///
/// This module offers an abstraction for working with the descriptor chains of the receive and
/// transmit queues.
///  * The transmit queue is used to send data from the driver to the device and it's buffers are
///    read-only for the device.
///  * The receive queue is used to send data from the device to the driver and it's buffers are
///    write-only for the device.
///
/// To implement this abstraction the [`Console`](struct.Console.html)  structure is provided which
/// consists of the `input_buffer` member and exposes several methods.
/// * The [`input_buffer`](struct.Console.html#field.input_buffer) is a buffer used to store data
///   before sending it to the driver. The following methods are provided to interact with it:
///   - [`enqueue_data`](struct.Console.html#method.enqueue_data) which is used to add data to the
///     end of the buffer.
///   - [`is_input_buffer_empty`](struct.Console.html#method.is_input_buffer_empty) which is used
///     assess if there is any data waiting to be sent.
///
/// The methods for processing a descriptor chain are the following:
/// *  [`process_transmitq_chain`](struct.Console.html#method.process_transmitq_chain) which is
///    used to read the data from a descriptor chain of the transmit queue.
/// * [`process_receiveq_chain`](struct.Console.html#method.process_receiveq_chain) which is used
///   to send the data to the driver by writing it into the buffers of a receive queue descriptor
///   chain.

/// Console device errors.
#[derive(Debug)]
pub enum Error {
    /// Failed to write slice to guest memory.
    WriteToGuestFailed(GuestMemoryError),
}

impl Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Error::*;

        match self {
            WriteToGuestFailed(ref err) => {
                write!(f, "console failed to write slice to guest memory: {}", err)
            }
        }
    }
}

/// Console struct that implements the abstraction of virtio console descriptor chain handling.
pub struct Console {
    /// Buffer that stores data to be sent to the driver.
    input_buffer: Arc<Mutex<Vec<u8>>>,
}

impl Console {
    /// Create new console object.
    pub fn new() -> Self {
        Console {
            input_buffer: Arc::new(Mutex::new(Vec::new())),
        }
    }

    /// Adds data in the form of raw bytes to the input buffer.
    ///
    /// # Arguments
    ///
    /// * `data` - A mutable reference to a `Vec<u8>` containing the raw bytes that will be
    ///            sent to the driver when the `process_receiveq_chian` method is called.
    pub fn enqueue_data(&self, data: &mut Vec<u8>) {
        let mut input_buffer = self.input_buffer.lock().unwrap();
        input_buffer.append(data);
    }

    /// Checks if input buffer is empty.
    pub fn is_input_buffer_empty(&self) -> bool {
        let input_buffer = self.input_buffer.lock().unwrap();
        input_buffer.is_empty()
    }

    /// Read data from a `desc_chain` of the transmit queue and write it to a specified output.
    ///
    /// # Arguments
    /// * `desc_chain` - A mutable reference to the descriptor chain that should point to the
    ///                  buffers that the virtio console driver has sent to the device.
    /// * `output` - An object that implements the `Write` trait and specifies where the data
    ///              should be written to (usually `stdout`). The `output` object is not included
    ///              as part of the [`Console`](struct.Console.html) struct and rather passed as an
    ///              argument to enable more flexibility in choosing and changing the output sink
    ///              from a higher level without having to reinitialize the
    ///              [`Console`](struct.Console.html) structure.
    ///
    /// # Returns
    /// The length in bytes of the processes data.
    pub fn process_transmitq_chain<M, T>(
        &self,
        desc_chain: &mut DescriptorChain<M>,
        output: &mut T,
    ) -> usize
    where
        M: Deref,
        M::Target: GuestMemory,
        T: Write,
    {
        // Iterate through all the buffers in the chain and write the data to output.
        let mut len = 0;
        while let Some(desc) = desc_chain.next() {
            len += desc_chain
                .memory()
                .write_to(desc.addr(), output, desc.len() as usize)
                .unwrap();
            let _ = output.flush();
        }

        len
    }

    /// Takes data from the input buffer and writes it to guest memory in the specified
    /// descriptor chain. The empty descriptor chain in which the data is written has previously
    /// been added to the receive queue by the driver.
    /// If there are not enough buffers to hold all the data, we stop and wait for the driver to
    /// add more.
    ///
    /// # Arguments
    /// * `desc_chain` - A mutable reference to the descriptor chain that should point to the
    ///                  empty buffers that the virtio driver has offered the device.
    ///
    /// # Returns
    /// The number of raw bytes written to guest memory.
    pub fn process_receiveq_chain<M>(
        &self,
        desc_chain: &mut DescriptorChain<M>,
    ) -> Result<usize, Error>
    where
        M: Deref,
        M::Target: GuestMemory,
    {
        // Acquire lock on buffer to make sure no other thread is adding data to it while it is
        // being processed.
        let mut input_buffer = self.input_buffer.lock().unwrap();
        let mut sent_bytes: usize = 0;

        // When the driver adds a new descriptor chain to the receive queue this method will be
        // called to write the remaining data to the newly provided buffers. If there is no
        // remaining data waiting to be sent it can return 0.
        if input_buffer.is_empty() {
            return Ok(0);
        }

        // Break up the data from the "input_buffer" into chunks that fit into the buffers of the
        // receive queue descriptor chain and write it to guest memory.
        while let Some(desc) = desc_chain.next() {
            let len_write = cmp::min(desc.len() as usize, input_buffer.len());
            let buffer_slice = input_buffer.drain(..len_write).collect::<Vec<u8>>();

            desc_chain
                .memory()
                .write_slice(&buffer_slice, desc.addr())
                .map_err(Error::WriteToGuestFailed)?;

            sent_bytes += len_write;

            if input_buffer.is_empty() {
                break;
            }
        }

        Ok(sent_bytes)
    }
}
