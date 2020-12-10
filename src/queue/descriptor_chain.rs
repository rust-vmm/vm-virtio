// Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Portions Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// Copyright © 2019 Intel Corporation
//
// Copyright (C) 2020 Alibaba Cloud. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0 AND BSD-3-Clause
use std::cmp;
use std::io::{self, Read, Write};
use std::mem::{size_of, MaybeUninit};
use std::ptr::copy_nonoverlapping;

use vm_memory::{
    Address, ByteValued, Bytes, GuestAddress, GuestAddressSpace, GuestMemory, GuestMemoryRegion,
    MemoryRegionAddress, VolatileMemory, VolatileSlice,
};

use crate::{Descriptor, Error, Result, VIRTQ_DESCRIPTOR_SIZE};

/// A virtio descriptor chain.
#[derive(Clone)]
pub struct DescriptorChain<M: GuestAddressSpace> {
    pub(crate) mem: M::T,
    pub(crate) desc_table: GuestAddress,
    pub(crate) queue_size: u16,
    pub(crate) head_index: u16,
    pub(crate) next_index: u16,
    pub(crate) ttl: u16,
    pub(crate) is_indirect: bool,
}

impl<M: GuestAddressSpace> DescriptorChain<M> {
    fn with_ttl(
        mem: M::T,
        desc_table: GuestAddress,
        queue_size: u16,
        ttl: u16,
        head_index: u16,
    ) -> Self {
        DescriptorChain {
            mem,
            desc_table,
            queue_size,
            head_index,
            next_index: head_index,
            ttl,
            is_indirect: false,
        }
    }

    /// Create a new `DescriptorChain` instance.
    pub(crate) fn new(
        mem: M::T,
        desc_table: GuestAddress,
        queue_size: u16,
        head_index: u16,
    ) -> Self {
        Self::with_ttl(mem, desc_table, queue_size, queue_size, head_index)
    }

    /// Get the descriptor index of the chain header
    pub fn head_index(&self) -> u16 {
        self.head_index
    }

    /// Return a `GuestMemory` object that can be used to access the buffers
    /// pointed to by the descriptor chain.
    pub fn memory(&self) -> &M::M {
        &*self.mem
    }

    /// Returns an iterator that only yields the readable descriptors in the chain.
    pub fn readable(self) -> DescriptorChainRwIter<M> {
        DescriptorChainRwIter {
            chain: self,
            writable: false,
        }
    }

    /// Returns an iterator that only yields the writable descriptors in the chain.
    pub fn writable(self) -> DescriptorChainRwIter<M> {
        DescriptorChainRwIter {
            chain: self,
            writable: true,
        }
    }

    // Alters the internal state of the `DescriptorChain` to switch iterating over an
    // indirect descriptor table defined by `desc`.
    fn process_indirect_descriptor(&mut self, desc: Descriptor) -> Result<()> {
        if self.is_indirect {
            return Err(Error::InvalidIndirectDescriptor);
        }

        let table_len = (desc.len as usize) / VIRTQ_DESCRIPTOR_SIZE;
        // Check the target indirect descriptor table is correctly aligned.
        if desc.addr().raw_value() & (VIRTQ_DESCRIPTOR_SIZE as u64 - 1) != 0
            || (desc.len as usize) & (VIRTQ_DESCRIPTOR_SIZE - 1) != 0
            || table_len > usize::from(std::u16::MAX)
        {
            return Err(Error::InvalidIndirectDescriptorTable);
        }

        self.desc_table = desc.addr();
        self.queue_size = table_len as u16;
        self.next_index = 0;
        self.ttl = self.queue_size;
        self.is_indirect = true;

        Ok(())
    }
}

impl<M: GuestAddressSpace> Iterator for DescriptorChain<M> {
    type Item = Descriptor;

    /// Returns the next descriptor in this descriptor chain, if there is one.
    ///
    /// Note that this is distinct from the next descriptor chain returned by
    /// [`AvailIter`](struct.AvailIter.html), which is the head of the next
    /// _available_ descriptor chain.
    fn next(&mut self) -> Option<Self::Item> {
        if self.ttl == 0 || self.next_index >= self.queue_size {
            return None;
        }

        // It's ok to use `unchecked_add` here because we previously verify the index does not
        // exceed the queue size, and the descriptor table location is expected to have been
        // validate before (for example, before activating a device). Moreover, this cannot
        // lead to unsafety because the actual memory accesses are always checked.
        let desc_addr = self
            .desc_table
            .unchecked_add(self.next_index as u64 * size_of::<Descriptor>() as u64);

        let desc = self.mem.read_obj::<Descriptor>(desc_addr).ok()?;

        if desc.is_indirect() {
            self.process_indirect_descriptor(desc).ok()?;
            return self.next();
        }

        if desc.has_next() {
            self.next_index = desc.next();
            // It's ok to decrement `self.ttl` here because we check at the start of the method
            // that it's greater than 0.
            self.ttl -= 1;
        } else {
            self.ttl = 0;
        }

        Some(desc)
    }
}

/// An iterator for readable or writable descriptors.
pub struct DescriptorChainRwIter<M: GuestAddressSpace> {
    chain: DescriptorChain<M>,
    writable: bool,
}

impl<M: GuestAddressSpace> Iterator for DescriptorChainRwIter<M> {
    type Item = Descriptor;

    /// Returns the next descriptor in this descriptor chain, if there is one.
    ///
    /// Note that this is distinct from the next descriptor chain returned by
    /// [`AvailIter`](struct.AvailIter.html), which is the head of the next
    /// _available_ descriptor chain.
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.chain.next() {
                Some(v) => {
                    if v.is_write_only() == self.writable {
                        return Some(v);
                    }
                }
                None => return None,
            }
        }
    }
}

#[derive(Clone, Debug)]
struct DescriptorChainConsumer<'a> {
    buffers: Vec<VolatileSlice<'a>>,
    bytes_consumed: usize,
    index: usize,
}

impl<'a> DescriptorChainConsumer<'a> {
    fn available_bytes(&self) -> usize {
        // This is guaranteed not to overflow because the total length of the chain
        // is checked during all creations of `DescriptorChainConsumer` (see
        // `Reader::new()` and `Writer::new()`).
        self.buffers[self.index..]
            .iter()
            .fold(0usize, |count, vs| count + vs.len() as usize)
    }

    fn bytes_consumed(&self) -> usize {
        self.bytes_consumed
    }

    // Given a DescriptorChain offset, return the index in self.buffers, and the
    // offset within, or ChainOverflow error.
    fn position(&self, offset: usize) -> Option<(usize, usize)> {
        let mut rem = offset;
        for (pos, vs) in self.buffers[self.index..].iter().enumerate() {
            if rem <= vs.len() {
                return Some((self.index + pos, rem));
            }
            rem -= vs.len();
        }
        None
    }

    /// Callers must provide a function that takes a `&[VolatileSlice]` and
    /// returns the total number of bytes consumed.
    ///
    /// # Errors
    ///
    /// If the provided function returns any error then no bytes are consumed from the buffer and
    /// the error is returned to the caller.
    fn consume<F>(&mut self, f: F) -> io::Result<usize>
    where
        F: FnOnce(&[VolatileSlice]) -> io::Result<usize>,
    {
        if self.buffers[self.index..].is_empty() {
            return Ok(0);
        }

        let bytes_consumed = f(&self.buffers[self.index..])?;
        // This can happen if a driver tricks a device into reading/writing more data than
        // fits in a `usize`.
        let total_bytes_consumed =
            self.bytes_consumed
                .checked_add(bytes_consumed)
                .ok_or_else(|| {
                    io::Error::new(io::ErrorKind::InvalidData, Error::DescriptorChainOverflow)
                })?;

        let position = self.position(bytes_consumed);
        let (at, offset) = position.ok_or_else(|| {
            io::Error::new(io::ErrorKind::InvalidData, Error::DescriptorChainOverflow)
        })?;
        // safe because we already checked the bounds
        self.buffers[at] = self.buffers[at].offset(offset).unwrap();
        self.index = at;

        self.bytes_consumed = total_bytes_consumed;

        Ok(bytes_consumed)
    }

    fn split_at(&mut self, offset: usize) -> Result<DescriptorChainConsumer<'a>> {
        let (at, offset) = self
            .position(offset)
            .ok_or(Error::DescriptorChainSplitOOB(offset))?;

        let (tail, head) = self.buffers[at].split_at(offset).unwrap();
        // let's make a copy for self
        let mut buffers = self.buffers[self.index..at].to_vec();
        buffers.push(tail);
        std::mem::swap(&mut self.buffers, &mut buffers);
        self.index = 0;
        // update the returned head
        buffers[at] = head;
        Ok(DescriptorChainConsumer {
            buffers,
            bytes_consumed: 0,
            index: at,
        })
    }
}

fn collect_desc_chain_buffers<M: GuestAddressSpace>(
    mem: &M::M,
    desc_chain_iter: DescriptorChainRwIter<M>,
) -> Result<Vec<VolatileSlice<'_>>> {
    let mut total_len: usize = 0;
    let mut buffers = Vec::new();
    for desc in desc_chain_iter {
        // Verify that summing the descriptor sizes does not overflow.
        // This can happen if a driver tricks a device into reading more data than
        // fits in a `usize`.
        total_len = total_len
            .checked_add(desc.len() as usize)
            .ok_or(Error::DescriptorChainOverflow)?;

        let mut len = desc.len() as usize;
        let mut addr = desc.addr();
        while len > 0 {
            let region = mem.find_region(addr).ok_or(Error::FindMemoryRegion)?;
            let offset = addr
                .checked_sub(region.start_addr().raw_value())
                .unwrap()
                .raw_value() as usize;
            let buf_len = cmp::min(region.len() as usize - offset, len);
            let buf = region
                .get_slice(MemoryRegionAddress(offset as u64), buf_len as usize)
                .map_err(Error::GuestMemory)?;
            buffers.push(buf);
            len -= buf_len;
            addr = addr
                .checked_add(buf_len as _)
                .ok_or(Error::DescriptorChainOverflow)?;
        }
    }

    Ok(buffers)
}

/// Provides high-level interface over the sequence of memory regions
/// defined by readable descriptors in the descriptor chain.
///
/// Note that virtio spec requires driver to place any device-writable
/// descriptors after any device-readable descriptors (2.6.4.2 in Virtio Spec v1.1).
/// Reader will skip iterating over descriptor chain when first writable
/// descriptor is encountered.
#[derive(Clone, Debug)]
pub struct Reader<'a> {
    buffer: DescriptorChainConsumer<'a>,
}

impl<'a> Reader<'a> {
    /// Construct a new Reader wrapper over `desc_chain`.
    pub fn new<M: GuestAddressSpace>(
        mem: &'a M::M,
        desc_chain: DescriptorChain<M>,
    ) -> Result<Reader<'a>> {
        Ok(Reader {
            buffer: DescriptorChainConsumer {
                buffers: collect_desc_chain_buffers(mem, desc_chain.readable())?,
                bytes_consumed: 0,
                index: 0,
            },
        })
    }

    /// Reads an object from the descriptor chain buffer.
    pub fn read_obj<T: ByteValued>(&mut self) -> io::Result<T> {
        let mut obj = MaybeUninit::<T>::uninit();

        // Safe because `MaybeUninit` guarantees that the pointer is valid for
        // `size_of::<T>()` bytes.
        let buf = unsafe {
            ::std::slice::from_raw_parts_mut(obj.as_mut_ptr() as *mut u8, size_of::<T>())
        };

        self.read_exact(buf)?;

        // Safe because any type that implements `ByteValued` can be considered initialized
        // even if it is filled with random data.
        Ok(unsafe { obj.assume_init() })
    }

    /// Returns number of bytes available for reading.  May return an error if the combined
    /// lengths of all the buffers in the DescriptorChain would cause an integer overflow.
    pub fn available_bytes(&self) -> usize {
        self.buffer.available_bytes()
    }

    /// Returns number of bytes already read from the descriptor chain buffer.
    pub fn bytes_read(&self) -> usize {
        self.buffer.bytes_consumed()
    }

    /// Splits this `Reader` into two at the given offset in the `DescriptorChain` buffer.
    /// After the split, `self` will be able to read up to `offset` bytes while the returned
    /// `Reader` can read up to `available_bytes() - offset` bytes.  Returns an error if
    /// `offset > self.available_bytes()`.
    pub fn split_at(&mut self, offset: usize) -> Result<Reader<'a>> {
        self.buffer.split_at(offset).map(|buffer| Reader { buffer })
    }
}

impl<'a> io::Read for Reader<'a> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        self.buffer.consume(|bufs| {
            let mut rem = buf;
            let mut total = 0;
            for vs in bufs {
                let copy_len = cmp::min(rem.len(), vs.len());

                // Safe because we have already verified that `vs` points to valid memory.
                unsafe {
                    copy_nonoverlapping(vs.as_ptr() as *const u8, rem.as_mut_ptr(), copy_len);
                }
                rem = &mut rem[copy_len..];
                total += copy_len;
                if rem.is_empty() {
                    break;
                }
            }
            Ok(total)
        })
    }
}

/// Provides high-level interface over the sequence of memory regions
/// defined by writable descriptors in the descriptor chain.
///
/// Note that virtio spec requires driver to place any device-writable
/// descriptors after any device-readable descriptors (2.6.4.2 in Virtio Spec v1.1).
/// Writer will start iterating the descriptors from the first writable one and will
/// assume that all following descriptors are writable.
#[derive(Clone, Debug)]
pub struct Writer<'a> {
    buffer: DescriptorChainConsumer<'a>,
}

impl<'a> Writer<'a> {
    /// Construct a new Writer wrapper over `desc_chain`.
    pub fn new<M: GuestAddressSpace>(
        mem: &'a M::M,
        desc_chain: DescriptorChain<M>,
    ) -> Result<Writer<'a>> {
        Ok(Writer {
            buffer: DescriptorChainConsumer {
                buffers: collect_desc_chain_buffers(mem, desc_chain.writable())?,
                bytes_consumed: 0,
                index: 0,
            },
        })
    }

    /// Writes an object to the descriptor chain buffer.
    pub fn write_obj<T: ByteValued>(&mut self, val: T) -> io::Result<()> {
        self.write_all(val.as_slice())
    }

    /// Returns number of bytes available for writing.  May return an error if the combined
    /// lengths of all the buffers in the DescriptorChain would cause an overflow.
    pub fn available_bytes(&self) -> usize {
        self.buffer.available_bytes()
    }

    /// Returns number of bytes already written to the descriptor chain buffer.
    pub fn bytes_written(&self) -> usize {
        self.buffer.bytes_consumed()
    }

    /// Splits this `Writer` into two at the given offset in the `DescriptorChain` buffer.
    /// After the split, `self` will be able to write up to `offset` bytes while the returned
    /// `Writer` can write up to `available_bytes() - offset` bytes.  Returns an error if
    /// `offset > self.available_bytes()`.
    pub fn split_at(&mut self, offset: usize) -> Result<Writer<'a>> {
        self.buffer.split_at(offset).map(|buffer| Writer { buffer })
    }
}

impl<'a> io::Write for Writer<'a> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.buffer.consume(|bufs| {
            let mut rem = buf;
            let mut total = 0;
            for vs in bufs {
                let copy_len = cmp::min(rem.len(), vs.len());

                // Safe because we have already verified that `vs` points to valid memory.
                unsafe {
                    copy_nonoverlapping(rem.as_ptr(), vs.as_ptr(), copy_len);
                }
                rem = &rem[copy_len..];
                total += copy_len;
                if rem.is_empty() {
                    break;
                }
            }
            Ok(total)
        })
    }

    fn flush(&mut self) -> io::Result<()> {
        // Nothing to flush since the writes go straight into the buffer.
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::*;
    use std::io::{self, Read, Write};
    use vm_memory::{Address, Bytes, GuestAddress, GuestAddressSpace, GuestMemoryMmap};

    #[derive(Copy, Clone, PartialEq, Eq)]
    enum DescriptorType {
        Readable,
        Writable,
    }

    /// Test utility function to create a descriptor chain in guest memory.
    fn create_descriptor_chain<M: GuestAddressSpace>(
        memory: M::T,
        descriptor_array_addr: GuestAddress,
        mut buffers_start_addr: GuestAddress,
        descriptors: Vec<(DescriptorType, u32)>,
        spaces_between_regions: u32,
    ) -> DescriptorChain<M> {
        let descriptors_len = descriptors.len();
        for (index, (type_, size)) in descriptors.into_iter().enumerate() {
            let mut flags = 0;
            if let DescriptorType::Writable = type_ {
                flags |= VIRTQ_DESC_F_WRITE;
            }
            if index + 1 < descriptors_len {
                flags |= VIRTQ_DESC_F_NEXT;
            }

            let index = index as u16;
            let desc = Descriptor {
                addr: buffers_start_addr.raw_value().into(),
                len: size.into(),
                flags: flags.into(),
                next: (index + 1).into(),
            };

            let offset = size + spaces_between_regions;
            buffers_start_addr = buffers_start_addr.checked_add(u64::from(offset)).unwrap();

            let _ = memory.write_obj(
                desc,
                descriptor_array_addr
                    .checked_add(u64::from(index) * std::mem::size_of::<Descriptor>() as u64)
                    .unwrap(),
            );
        }
        DescriptorChain::new(memory, descriptor_array_addr, 0x100, 0)
    }

    #[test]
    fn reader_test_simple_chain() {
        use DescriptorType::*;

        let memory_start_addr = GuestAddress(0x0);
        let memory = GuestMemoryMmap::from_ranges(&[(memory_start_addr, 0x10000)]).unwrap();

        let chain = create_descriptor_chain::<&GuestMemoryMmap>(
            &memory,
            GuestAddress(0x0),
            GuestAddress(0x100),
            vec![
                (Readable, 8),
                (Readable, 16),
                (Readable, 18),
                (Readable, 64),
            ],
            0,
        );
        let mut reader = Reader::new(&memory, chain).expect("failed to create Reader");
        assert_eq!(reader.available_bytes(), 106);
        assert_eq!(reader.bytes_read(), 0);

        let mut buffer = [0 as u8; 64];
        if let Err(e) = reader.read_exact(&mut buffer) {
            panic!("read_exact should not fail here: {:?}", e);
        }

        assert_eq!(reader.available_bytes(), 42);
        assert_eq!(reader.bytes_read(), 64);

        match reader.read(&mut buffer) {
            Err(e) => panic!("read should not fail here: {:?}", e),
            Ok(length) => assert_eq!(length, 42),
        }

        assert_eq!(reader.available_bytes(), 0);
        assert_eq!(reader.bytes_read(), 106);
    }

    #[test]
    fn writer_test_simple_chain() {
        use DescriptorType::*;

        let memory_start_addr = GuestAddress(0x0);
        let memory = GuestMemoryMmap::from_ranges(&[(memory_start_addr, 0x10000)]).unwrap();

        let chain = create_descriptor_chain::<&GuestMemoryMmap>(
            &memory,
            GuestAddress(0x0),
            GuestAddress(0x100),
            vec![
                (Writable, 8),
                (Writable, 16),
                (Writable, 18),
                (Writable, 64),
            ],
            0,
        );
        let mut writer = Writer::new(&memory, chain).expect("failed to create Writer");
        assert_eq!(writer.available_bytes(), 106);
        assert_eq!(writer.bytes_written(), 0);

        let buffer = [0 as u8; 64];
        if let Err(e) = writer.write_all(&buffer) {
            panic!("write_all should not fail here: {:?}", e);
        }

        assert_eq!(writer.available_bytes(), 42);
        assert_eq!(writer.bytes_written(), 64);

        match writer.write(&buffer) {
            Err(e) => panic!("write should not fail here {:?}", e),
            Ok(length) => assert_eq!(length, 42),
        }

        assert_eq!(writer.available_bytes(), 0);
        assert_eq!(writer.bytes_written(), 106);
    }

    #[test]
    fn reader_test_incompatible_chain() {
        use DescriptorType::*;

        let memory_start_addr = GuestAddress(0x0);
        let memory = GuestMemoryMmap::from_ranges(&[(memory_start_addr, 0x10000)]).unwrap();

        let chain = create_descriptor_chain::<&GuestMemoryMmap>(
            &memory,
            GuestAddress(0x0),
            GuestAddress(0x100),
            vec![(Writable, 8)],
            0,
        );
        let mut reader = Reader::new(&memory, chain).expect("failed to create Reader");
        assert_eq!(reader.available_bytes(), 0);
        assert_eq!(reader.bytes_read(), 0);

        assert!(reader.read_obj::<u8>().is_err());

        assert_eq!(reader.available_bytes(), 0);
        assert_eq!(reader.bytes_read(), 0);
    }

    #[test]
    fn writer_test_incompatible_chain() {
        use DescriptorType::*;

        let memory_start_addr = GuestAddress(0x0);
        let memory = GuestMemoryMmap::from_ranges(&[(memory_start_addr, 0x10000)]).unwrap();

        let chain = create_descriptor_chain::<&GuestMemoryMmap>(
            &memory,
            GuestAddress(0x0),
            GuestAddress(0x100),
            vec![(Readable, 8)],
            0,
        );
        let mut writer = Writer::new(&memory, chain).expect("failed to create Writer");
        assert_eq!(writer.available_bytes(), 0);
        assert_eq!(writer.bytes_written(), 0);

        assert!(writer.write_obj(0u8).is_err());

        assert_eq!(writer.available_bytes(), 0);
        assert_eq!(writer.bytes_written(), 0);
    }

    #[test]
    fn reader_writer_shared_chain() {
        use DescriptorType::*;

        let memory_start_addr = GuestAddress(0x0);
        let memory = GuestMemoryMmap::from_ranges(&[(memory_start_addr, 0x10000)]).unwrap();

        let chain = create_descriptor_chain::<&GuestMemoryMmap>(
            &memory,
            GuestAddress(0x0),
            GuestAddress(0x100),
            vec![
                (Readable, 16),
                (Readable, 16),
                (Readable, 96),
                (Writable, 64),
                (Writable, 1),
                (Writable, 3),
            ],
            0,
        );
        let mut reader = Reader::new(&memory, chain.clone()).expect("failed to create Reader");
        let mut writer = Writer::new(&memory, chain).expect("failed to create Writer");

        assert_eq!(reader.bytes_read(), 0);
        assert_eq!(writer.bytes_written(), 0);

        let mut buffer = Vec::with_capacity(200);

        assert_eq!(
            reader
                .read_to_end(&mut buffer)
                .expect("read should not fail here"),
            128
        );

        // The writable descriptors are only 68 bytes long.
        writer
            .write_all(&buffer[..68])
            .expect("write should not fail here");

        assert_eq!(reader.available_bytes(), 0);
        assert_eq!(reader.bytes_read(), 128);
        assert_eq!(writer.available_bytes(), 0);
        assert_eq!(writer.bytes_written(), 68);
    }

    #[test]
    fn reader_writer_shattered_object() {
        use DescriptorType::*;

        let memory_start_addr = GuestAddress(0x0);
        let memory = GuestMemoryMmap::from_ranges(&[(memory_start_addr, 0x10000)]).unwrap();

        let secret = 0x1234_5678;

        // Create a descriptor chain with memory regions that are properly separated.
        let chain_writer = create_descriptor_chain::<&GuestMemoryMmap>(
            &memory,
            GuestAddress(0x0),
            GuestAddress(0x100),
            vec![(Writable, 1), (Writable, 1), (Writable, 1), (Writable, 1)],
            123,
        );
        let mut writer = Writer::new(&memory, chain_writer).expect("failed to create Writer");
        if let Err(e) = writer.write_obj(secret) {
            panic!("write_obj should not fail here: {:?}", e);
        }

        // Now create new descriptor chain pointing to the same memory and try to read it.
        let chain_reader = create_descriptor_chain::<&GuestMemoryMmap>(
            &memory,
            GuestAddress(0x0),
            GuestAddress(0x100),
            vec![(Readable, 1), (Readable, 1), (Readable, 1), (Readable, 1)],
            123,
        );
        let mut reader = Reader::new(&memory, chain_reader).expect("failed to create Reader");
        match reader.read_obj::<u32>() {
            Err(e) => panic!("read_obj should not fail here: {:?}", e),
            Ok(read_secret) => assert_eq!(read_secret, secret),
        }
    }

    #[test]
    fn reader_unexpected_eof() {
        use DescriptorType::*;

        let memory_start_addr = GuestAddress(0x0);
        let memory = GuestMemoryMmap::from_ranges(&[(memory_start_addr, 0x10000)]).unwrap();

        let chain = create_descriptor_chain::<&GuestMemoryMmap>(
            &memory,
            GuestAddress(0x0),
            GuestAddress(0x100),
            vec![(Readable, 256), (Readable, 256)],
            0,
        );

        let mut reader = Reader::new(&memory, chain).expect("failed to create Reader");

        let mut buf = vec![0; 1024];

        assert_eq!(
            reader
                .read_exact(&mut buf[..])
                .expect_err("read more bytes than available")
                .kind(),
            io::ErrorKind::UnexpectedEof
        );
    }

    #[test]
    fn split_border() {
        use DescriptorType::*;

        let memory_start_addr = GuestAddress(0x0);
        let memory = GuestMemoryMmap::from_ranges(&[(memory_start_addr, 0x10000)]).unwrap();

        let chain = create_descriptor_chain::<&GuestMemoryMmap>(
            &memory,
            GuestAddress(0x0),
            GuestAddress(0x100),
            vec![
                (Readable, 16),
                (Readable, 16),
                (Readable, 96),
                (Writable, 64),
                (Writable, 1),
                (Writable, 3),
            ],
            0,
        );
        let mut reader = Reader::new(&memory, chain.clone()).expect("failed to create Reader");
        let other = reader.split_at(32).expect("failed to split Reader");
        assert_eq!(reader.available_bytes(), 32);
        assert_eq!(other.available_bytes(), 96);

        let mut writer = Writer::new(&memory, chain).expect("failed to create Writer");
        let other = writer.split_at(64).expect("failed to split Writer");
        assert_eq!(writer.available_bytes(), 64);
        assert_eq!(other.available_bytes(), 4);
    }

    #[test]
    fn split_middle() {
        use DescriptorType::*;

        let memory_start_addr = GuestAddress(0x0);
        let memory = GuestMemoryMmap::from_ranges(&[(memory_start_addr, 0x10000)]).unwrap();

        let chain = create_descriptor_chain::<&GuestMemoryMmap>(
            &memory,
            GuestAddress(0x0),
            GuestAddress(0x100),
            vec![
                (Readable, 16),
                (Readable, 16),
                (Readable, 96),
                (Writable, 64),
                (Writable, 1),
                (Writable, 3),
            ],
            0,
        );
        let mut reader = Reader::new(&memory, chain.clone()).expect("failed to create Reader");
        let other = reader.split_at(24).expect("failed to split Reader");
        assert_eq!(reader.available_bytes(), 24);
        assert_eq!(other.available_bytes(), 104);

        let mut writer = Writer::new(&memory, chain).expect("failed to create Writer");
        let other = writer.split_at(66).expect("failed to split Writer");
        assert_eq!(writer.available_bytes(), 66);
        assert_eq!(other.available_bytes(), 2);
    }

    #[test]
    fn split_end() {
        use DescriptorType::*;

        let memory_start_addr = GuestAddress(0x0);
        let memory = GuestMemoryMmap::from_ranges(&[(memory_start_addr, 0x10000)]).unwrap();

        let chain = create_descriptor_chain::<&GuestMemoryMmap>(
            &memory,
            GuestAddress(0x0),
            GuestAddress(0x100),
            vec![
                (Readable, 16),
                (Readable, 16),
                (Readable, 96),
                (Writable, 64),
                (Writable, 1),
                (Writable, 3),
            ],
            0,
        );
        let mut reader = Reader::new(&memory, chain.clone()).expect("failed to create Reader");
        let other = reader.split_at(128).expect("failed to split Reader");
        assert_eq!(reader.available_bytes(), 128);
        assert_eq!(other.available_bytes(), 0);

        let mut writer = Writer::new(&memory, chain).expect("failed to create Writer");
        let other = writer.split_at(68).expect("failed to split Writer");
        assert_eq!(writer.available_bytes(), 68);
        assert_eq!(other.available_bytes(), 0);
    }

    #[test]
    fn split_beginning() {
        use DescriptorType::*;

        let memory_start_addr = GuestAddress(0x0);
        let memory = GuestMemoryMmap::from_ranges(&[(memory_start_addr, 0x10000)]).unwrap();

        let chain = create_descriptor_chain::<&GuestMemoryMmap>(
            &memory,
            GuestAddress(0x0),
            GuestAddress(0x100),
            vec![
                (Readable, 16),
                (Readable, 16),
                (Readable, 96),
                (Writable, 64),
                (Writable, 1),
                (Writable, 3),
            ],
            0,
        );
        let mut reader = Reader::new(&memory, chain).expect("failed to create Reader");

        let other = reader.split_at(0).expect("failed to split Reader");
        assert_eq!(reader.available_bytes(), 0);
        assert_eq!(other.available_bytes(), 128);
    }

    #[test]
    fn split_outofbounds() {
        use DescriptorType::*;

        let memory_start_addr = GuestAddress(0x0);
        let memory = GuestMemoryMmap::from_ranges(&[(memory_start_addr, 0x10000)]).unwrap();

        let chain = create_descriptor_chain::<&GuestMemoryMmap>(
            &memory,
            GuestAddress(0x0),
            GuestAddress(0x100),
            vec![
                (Readable, 16),
                (Readable, 16),
                (Readable, 96),
                (Writable, 64),
                (Writable, 1),
                (Writable, 3),
            ],
            0,
        );
        let mut reader = Reader::new(&memory, chain).expect("failed to create Reader");
        let err = reader.split_at(256).unwrap_err();
        assert!(matches!(err, Error::DescriptorChainSplitOOB(256)));
    }

    #[test]
    fn read_full() {
        use DescriptorType::*;

        let memory_start_addr = GuestAddress(0x0);
        let memory = GuestMemoryMmap::from_ranges(&[(memory_start_addr, 0x10000)]).unwrap();

        let chain = create_descriptor_chain::<&GuestMemoryMmap>(
            &memory,
            GuestAddress(0x0),
            GuestAddress(0x100),
            vec![(Readable, 16), (Readable, 16), (Readable, 16)],
            0,
        );
        let mut reader = Reader::new(&memory, chain).expect("failed to create Reader");

        let mut buf = vec![0u8; 64];
        assert_eq!(
            reader.read(&mut buf[..]).expect("failed to read to buffer"),
            48
        );
    }

    #[test]
    fn write_full() {
        use DescriptorType::*;

        let memory_start_addr = GuestAddress(0x0);
        let memory = GuestMemoryMmap::from_ranges(&[(memory_start_addr, 0x10000)]).unwrap();

        let chain = create_descriptor_chain::<&GuestMemoryMmap>(
            &memory,
            GuestAddress(0x0),
            GuestAddress(0x100),
            vec![(Writable, 16), (Writable, 16), (Writable, 16)],
            0,
        );
        let mut writer = Writer::new(&memory, chain).expect("failed to create Writer");

        let buf = vec![0xdeu8; 64];
        assert_eq!(
            writer.write(&buf[..]).expect("failed to write from buffer"),
            48
        );
        writer.flush().expect("failed to flush");
    }

    #[test]
    fn split_host_memory() {
        use DescriptorType::*;

        let memory = GuestMemoryMmap::from_ranges(&[
            (GuestAddress(0x0), 0x200),
            (GuestAddress(0x200), 0x200),
        ])
        .unwrap();

        let chain = create_descriptor_chain::<&GuestMemoryMmap>(
            &memory,
            GuestAddress(0x0),
            GuestAddress(0x100),
            vec![(Writable, 0x200)],
            0,
        );
        let mut writer = Writer::new(&memory, chain).expect("failed to create Writer");

        let buf = vec![0xde; 0x200];
        assert_eq!(
            writer.write(&buf[..]).expect("failed to write from buffer"),
            0x200
        );
        writer.flush().expect("failed to flush");
    }
}
