// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

//! Utilities used by unit tests and benchmarks for mocking the driver side
//! of the virtio protocol.

#![allow(missing_docs)]

use std::cmp::min;
use std::marker::PhantomData;
use std::mem::size_of;

use vm_memory::guest_memory::Error as GuestMemError;
use vm_memory::{
    Address, ByteValued, Bytes, GuestAddress, GuestAddressSpace, GuestMemory, GuestUsize,
};

use crate::defs::{VIRTQ_DESC_F_INDIRECT, VIRTQ_DESC_F_NEXT, VIRTQ_DESC_F_WRITE};
use crate::{Descriptor, Queue};

/// Wrapper struct used for accesing a particular address of a GuestMemory area.
pub struct Ref<'a, M, T> {
    mem: &'a M,
    addr: GuestAddress,
    phantom: PhantomData<*const T>,
}

impl<'a, M: GuestMemory, T: ByteValued> Ref<'a, M, T> {
    fn new(mem: &'a M, addr: GuestAddress) -> Self {
        Ref {
            mem,
            addr,
            phantom: PhantomData,
        }
    }

    /// Read an object of type T from the underlying memory found at self.addr.
    pub fn load(&self) -> T {
        self.mem.read_obj(self.addr).unwrap()
    }

    /// Write an object of type T from the underlying memory found at self.addr.
    pub fn store(&self, val: T) {
        self.mem.write_obj(val, self.addr).unwrap()
    }
}

/// Wrapper struct used for accesing a subregion of a GuestMemory area.
pub struct ArrayRef<'a, M, T> {
    mem: &'a M,
    addr: GuestAddress,
    len: usize,
    phantom: PhantomData<*const T>,
}

impl<'a, M: GuestMemory, T: ByteValued> ArrayRef<'a, M, T> {
    fn new(mem: &'a M, addr: GuestAddress, len: usize) -> Self {
        ArrayRef {
            mem,
            addr,
            len,
            phantom: PhantomData,
        }
    }

    /// Return a `Ref` object pointing to an address defined by a particular
    /// index offset in the region.
    pub fn ref_at(&self, index: usize) -> Ref<'a, M, T> {
        // TODO: add better error handling to the mock logic.
        assert!(index < self.len);

        let addr = self
            .addr
            .checked_add((index * size_of::<T>()) as u64)
            .unwrap();

        Ref::new(self.mem, addr)
    }
}

/// Represents one element of a used ring.
#[repr(C)]
#[derive(Clone, Copy, Default)]
pub struct UsedRingElement {
    /// Starting index of the used descriptor chain.
    pub id: u32,
    /// Total length of the descriptor chain which was written to.
    pub len: u32,
}

unsafe impl ByteValued for UsedRingElement {}

/// Represents a virtio queue ring. The only difference between the used and available rings,
/// is the ring element type.
pub struct SplitQueueRing<'a, M, T: ByteValued> {
    flags: Ref<'a, M, u16>,
    idx: Ref<'a, M, u16>,
    ring: ArrayRef<'a, M, T>,
    // `used_event` for `AvailRing`, `avail_event` for `UsedRing`.
    event: Ref<'a, M, u16>,
}

impl<'a, M: GuestMemory, T: ByteValued> SplitQueueRing<'a, M, T> {
    /// Create a new `SplitQueueRing` instance
    pub fn new(mem: &'a M, base: GuestAddress, len: u16) -> Self {
        let event_addr = base
            .checked_add(4)
            .and_then(|a| a.checked_add((size_of::<u16>() * len as usize) as u64))
            .unwrap();

        let split_queue_ring = SplitQueueRing {
            flags: Ref::new(mem, base),
            idx: Ref::new(mem, base.checked_add(2).unwrap()),
            ring: ArrayRef::new(mem, base.checked_add(4).unwrap(), len as usize),
            event: Ref::new(mem, event_addr),
        };

        split_queue_ring.flags.store(0);
        split_queue_ring.idx.store(0);
        split_queue_ring.event.store(0);

        split_queue_ring
    }

    /// Return the starting address of the `SplitQueueRing`.
    pub fn start(&self) -> GuestAddress {
        self.ring.addr
    }

    /// Return the end address of the `SplitQueueRing`.
    pub fn end(&self) -> GuestAddress {
        self.start().unchecked_add(self.ring.len as GuestUsize)
    }

    /// Return a reference to the idx field.
    pub fn idx(&self) -> &Ref<'a, M, u16> {
        &self.idx
    }

    /// Return a reference to the ring field.
    pub fn ring(&self) -> &ArrayRef<'a, M, T> {
        &self.ring
    }
}

/// The available ring is used by the driver to offer buffers to the device.
pub type AvailRing<'a, M> = SplitQueueRing<'a, M, u16>;
/// The used ring is where the device returns buffers once it is done with them.
pub type UsedRing<'a, M> = SplitQueueRing<'a, M, UsedRingElement>;

/// Refers to the buffers the driver is using for the device.
pub struct DescriptorTable<'a, M> {
    table: ArrayRef<'a, M, Descriptor>,
    len: u16,
    free_descriptors: Vec<u16>,
}

impl<'a, M: GuestMemory> DescriptorTable<'a, M> {
    /// Create a new `DescriptorTable` instance
    pub fn new(mem: &'a M, addr: GuestAddress, len: u16) -> Self {
        let table = ArrayRef::new(mem, addr, len as usize);
        let free_descriptors = (0..len).rev().collect();

        DescriptorTable {
            table,
            len,
            free_descriptors,
        }
    }

    /// Read one descriptor from the specified index.
    pub fn load(&self, index: u16) -> Descriptor {
        self.table.ref_at(index as usize).load()
    }

    /// Write one descriptor at the specified index.
    pub fn store(&self, index: u16, value: Descriptor) {
        self.table.ref_at(index as usize).store(value)
    }

    /// Return the total size of the DescriptorTable in bytes.
    pub fn total_size(&self) -> u64 {
        (self.len as usize * size_of::<Descriptor>()) as u64
    }

    /// Takes a vector of MockDescriptors, converts them to real descriptors by adding
    /// all the missing fields and stores them in the descriptor table.
    ///
    /// # Example:
    /// ```
    /// use vm_memory::{GuestAddress, GuestMemoryMmap};
    /// use virtio_queue::mock::{DescriptorTable, MockDescriptor, MockDescriptorChain};
    ///
    /// // This creates the descriptor chain: [2, 4, 10, 11].
    /// let v = vec![MockDescriptor::new().with_index(2).with_addr(0x1000).with_len(0x1000),
    ///              MockDescriptor::new().with_index(4).with_len(0x100),
    ///              MockDescriptor::new().with_index(10).with_addr(0x3000).with_len(0x1000).indirect(),
    ///              MockDescriptor::new().with_len(0x100).writeable()];
    ///
    /// let direct_chain = MockDescriptorChain::new(v);
    ///
    /// let m = &GuestMemoryMmap::<()>::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap();
    /// let dt = DescriptorTable::new(m, GuestAddress(0x1000), 11);
    /// dt.add_chain(direct_chain);
    /// ```
    pub fn add_chain(&self, mdc: MockDescriptorChain) -> u16 {
        let mut prev = MockDescriptor::new();
        for (i, md) in mdc.chain.iter().enumerate() {
            let addr = md.addr().unwrap_or_else(|| match i {
                0 => 0,
                _ => prev.addr().unwrap() + prev.len().unwrap() as u64,
            });

            let len = md.len().unwrap_or(0x1000);

            let mut flags: u16;
            if i == (mdc.len() - 1) as usize {
                flags = 0;
            } else {
                flags = VIRTQ_DESC_F_NEXT;
            }

            if md.is_indirect() {
                flags |= VIRTQ_DESC_F_INDIRECT;
            }

            if md.is_writeable() {
                flags |= VIRTQ_DESC_F_WRITE;
            }

            let index = md.index().unwrap_or_else(|| match i {
                0 => 0,
                _ => prev.index().unwrap(),
            });

            let next = if i == (mdc.len() - 1) as usize {
                0
            } else {
                mdc.chain[i + 1].index().unwrap_or(index + 1)
            };

            let desc = Descriptor::new(addr, len, flags, next);
            self.store(index, desc);

            prev = MockDescriptor {
                addr: Some(addr),
                index: Some(index),
                len: Some(len),
                ..*md
            };
        }

        // Returns the index of the first descriptor
        mdc.chain[0].index().unwrap_or(0)
    }

    /// Create a chain of descriptors
    pub fn build_chain(&mut self, len: u16) -> u16 {
        let indices = self
            .free_descriptors
            .iter()
            .copied()
            .rev()
            .take(usize::from(len))
            .collect::<Vec<_>>();

        assert_eq!(indices.len(), len as usize);

        for (pos, index_value) in indices.iter().copied().enumerate() {
            // Addresses and lens constant for now.
            let mut desc = Descriptor {
                addr: 0x1000,
                len: 0x1000,
                ..Descriptor::default()
            };

            // It's not the last descriptor in the chain.
            if pos < indices.len() - 1 {
                desc.flags = VIRTQ_DESC_F_NEXT;
                desc.next = indices[pos + 1];
            } else {
                desc.flags = 0;
            }
            self.store(index_value, desc);
        }

        indices[0]
    }
}

trait GuestAddressExt {
    fn align_up(&self, x: GuestUsize) -> GuestAddress;
}

impl GuestAddressExt for GuestAddress {
    fn align_up(&self, x: GuestUsize) -> GuestAddress {
        Self((self.0 + (x - 1)) & !(x - 1))
    }
}

/// A mock version of the virtio queue implemented from the perspective of the driver.
pub struct MockSplitQueue<'a, M> {
    mem: &'a M,
    len: u16,
    desc_table_addr: GuestAddress,
    desc_table: DescriptorTable<'a, M>,
    avail_addr: GuestAddress,
    avail: AvailRing<'a, M>,
    used_addr: GuestAddress,
    used: UsedRing<'a, M>,
    indirect_addr: GuestAddress,
}

impl<'a, M: GuestMemory> MockSplitQueue<'a, M> {
    /// Create a new `MockSplitQueue` instance with 0 as the default guest
    /// physical starting address.
    pub fn new(mem: &'a M, len: u16) -> Self {
        Self::create(mem, GuestAddress(0), len)
    }

    /// Create a new `MockSplitQueue` instance.
    pub fn create(mem: &'a M, start: GuestAddress, len: u16) -> Self {
        const AVAIL_ALIGN: GuestUsize = 2;
        const USED_ALIGN: GuestUsize = 4;

        let desc_table_addr = start;
        let desc_table = DescriptorTable::new(mem, desc_table_addr, len);

        let avail_addr = start
            .unchecked_add(16 * len as GuestUsize)
            .align_up(AVAIL_ALIGN);
        let avail = AvailRing::new(mem, avail_addr, len);

        let used_addr = avail.end().align_up(USED_ALIGN);
        let used = UsedRing::new(mem, used_addr, len);

        let indirect_addr = GuestAddress(0x3000_0000);

        MockSplitQueue {
            mem,
            len,
            desc_table_addr,
            desc_table,
            avail_addr,
            avail,
            used_addr,
            used,
            indirect_addr,
        }
    }

    /// Return the starting address of the queue.
    pub fn start(&self) -> GuestAddress {
        self.desc_table_addr
    }

    /// Return the end address of the queue.
    pub fn end(&self) -> GuestAddress {
        self.used.end()
    }

    /// Descriptor table accesor.
    pub fn desc_table(&self) -> &DescriptorTable<'a, M> {
        &self.desc_table
    }

    /// Available ring accesor.
    pub fn avail(&self) -> &AvailRing<M> {
        &self.avail
    }

    /// Used ring accesor.
    pub fn used(&self) -> &UsedRing<M> {
        &self.used
    }

    /// Return the starting address of the descriptor table.
    pub fn desc_table_addr(&self) -> GuestAddress {
        self.desc_table_addr
    }

    /// Return the starting address of the available ring.
    pub fn avail_addr(&self) -> GuestAddress {
        self.avail_addr
    }

    /// Return the starting address of the used ring.
    pub fn used_addr(&self) -> GuestAddress {
        self.used_addr
    }

    fn update_avail_idx(&mut self, value: u16) {
        let avail_idx = self.avail.idx.load();
        self.avail.ring.ref_at(avail_idx as usize).store(value);
        self.avail.idx.store(avail_idx.wrapping_add(1));
    }

    fn alloc_indirect_chain(&mut self, len: u16) -> GuestAddress {
        // To simplify things for now, we round up the table len as a multiple of 16. When this is
        // no longer the case, we should make sure the starting address of the descriptor table
        // we're  creating below is properly aligned.

        let table_len = if len % 16 == 0 {
            len
        } else {
            16 * (len / 16 + 1)
        };

        let mut table = DescriptorTable::new(self.mem, self.indirect_addr, table_len);
        let head_decriptor_index = table.build_chain(len);
        // When building indirect descriptor tables, the descriptor at index 0 is supposed to be
        // first in the resulting chain. Just making sure our logic actually makes that happen.
        assert_eq!(head_decriptor_index, 0);

        let table_addr = self.indirect_addr;
        self.indirect_addr = self.indirect_addr.checked_add(table.total_size()).unwrap();
        table_addr
    }

    /// Add a descriptor chain to the table.
    pub fn add_chain(&mut self, len: u16) {
        let head_idx = self.desc_table.build_chain(len);
        self.update_avail_idx(head_idx);
    }

    /// Add an indirect descriptor chain to the table.
    pub fn add_indirect_chain(&mut self, len: u16) {
        let head_idx = self.desc_table.build_chain(1);

        // We just allocate the indirect table and forget about it for now.
        let indirect_addr = self.alloc_indirect_chain(len);

        let mut desc = self.desc_table.load(head_idx);
        desc.flags = VIRTQ_DESC_F_INDIRECT;
        desc.addr = indirect_addr.raw_value();
        desc.len = u32::from(len) * size_of::<Descriptor>() as u32;

        self.desc_table.store(head_idx, desc);
        self.update_avail_idx(head_idx);
    }

    /// Creates a new `Queue`, using the underlying memory regions represented
    /// by the `MockSplitQueue`.
    pub fn create_queue<A: GuestAddressSpace>(&self, a: A) -> Queue<A> {
        let mut q = Queue::new(a, self.len);

        q.size = self.len;
        q.ready = true;
        q.desc_table = self.desc_table_addr;
        q.avail_ring = self.avail_addr;
        q.used_ring = self.used_addr;
        q
    }
}

pub struct MockDescriptorChain {
    pub chain: Vec<MockDescriptor>,
}

impl MockDescriptorChain {
    pub fn new(chain: Vec<MockDescriptor>) -> Self {
        Self { chain }
    }

    pub fn with_len(len: u16) -> Self {
        let mut chain = Vec::with_capacity(len as usize);
        for i in 0..len {
            let md = MockDescriptor::new()
                .with_index(i)
                .with_addr((0x1000 * i) as u64)
                .with_len(0x1000);

            chain.push(md);
        }

        MockDescriptorChain::new(chain)
    }

    pub fn len(&self) -> u16 {
        self.chain.len() as u16
    }

    pub fn write_slice<M: GuestMemory>(&self, buffer: &[u8], mem: &M) -> Result<(), GuestMemError> {
        let mut prev = MockDescriptor::new();
        let (mut start, mut end) = (0, 0);
        let mut to_write = buffer.len();

        for (index, md) in self.chain.iter().enumerate() {
            if to_write == 0 {
                return Ok(());
            }

            let addr = md.addr().unwrap_or_else(|| match index {
                0 => 0,
                _ => prev.addr().unwrap() + prev.len().unwrap() as u64,
            });
            let len = md.len().unwrap_or(0x1000);

            start = match index {
                0 => addr as usize,
                _ => end,
            };
            end = min(start + len as usize, start + to_write);

            mem.write(&buffer[start..end], GuestAddress(addr))?;
            to_write -= end - start;

            prev = MockDescriptor {
                addr: Some(addr),
                len: Some(len),
                ..*md
            };
        }

        Ok(())
    }
}

#[derive(Clone, Copy)]
pub struct MockDescriptor {
    index: Option<u16>,
    addr: Option<u64>,
    len: Option<u32>,
    writeable: bool,
    indirect: bool,
}

impl MockDescriptor {
    pub fn new() -> Self {
        Self {
            index: None,
            addr: None,
            len: None,
            writeable: false,
            indirect: false,
        }
    }

    pub fn with_index(self, index: u16) -> Self {
        Self {
            index: Some(index),
            ..self
        }
    }

    pub fn with_addr(self, addr: u64) -> Self {
        Self {
            addr: Some(addr),
            ..self
        }
    }

    pub fn with_len(self, len: u32) -> Self {
        Self {
            len: Some(len),
            ..self
        }
    }

    pub fn writeable(self) -> Self {
        Self {
            writeable: true,
            ..self
        }
    }

    pub fn indirect(self) -> Self {
        Self {
            indirect: true,
            ..self
        }
    }

    pub fn index(&self) -> Option<u16> {
        self.index
    }

    pub fn addr(&self) -> Option<u64> {
        self.addr
    }

    pub fn len(&self) -> Option<u32> {
        self.len
    }

    pub fn is_writeable(&self) -> bool {
        self.writeable
    }

    pub fn is_indirect(&self) -> bool {
        self.indirect
    }
}

impl Default for MockDescriptor {
    fn default() -> Self {
        Self::new()
    }
}
