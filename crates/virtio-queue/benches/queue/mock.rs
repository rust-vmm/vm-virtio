// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

use std::marker::PhantomData;
use std::mem::size_of;

use vm_memory::{Address, ByteValued, Bytes, GuestAddress, GuestAddressSpace, GuestMemory};

use virtio_queue::defs::{VIRTQ_DESC_F_INDIRECT, VIRTQ_DESC_F_NEXT};
use virtio_queue::Queue;

struct Ref<'a, M, T> {
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

    fn load(&self) -> T {
        self.mem.read_obj(self.addr).unwrap()
    }

    fn store(&self, val: T) {
        self.mem.write_obj(val, self.addr).unwrap()
    }
}

struct ArrayRef<'a, M, T> {
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

    fn ref_at(&self, index: usize) -> Ref<'a, M, T> {
        // TODO: add better error handling to the mock logic.
        assert!(index < self.len);

        let addr = self
            .addr
            .checked_add((index * size_of::<T>()) as u64)
            .unwrap();
        Ref::new(self.mem, addr)
    }
}

#[repr(C)]
#[derive(Clone, Copy, Default)]
pub struct Descriptor {
    pub addr: u64,
    pub len: u32,
    pub flags: u16,
    pub next: u16,
}

unsafe impl ByteValued for Descriptor {}

#[repr(C)]
#[derive(Clone, Copy, Default)]
pub struct UsedRingElement {
    pub id: u32,
    pub len: u32,
}

unsafe impl ByteValued for UsedRingElement {}

pub struct SplitQueueRing<'a, M, T: ByteValued> {
    flags: Ref<'a, M, u16>,
    idx: Ref<'a, M, u16>,
    ring: ArrayRef<'a, M, T>,
    // `used_event` for `AvailRing`, `avail_event` for `UsedRing`.
    event: Ref<'a, M, u16>,
}

impl<'a, M: GuestMemory, T: ByteValued> SplitQueueRing<'a, M, T> {
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
}

pub type AvailRing<'a, M> = SplitQueueRing<'a, M, u16>;
pub type UsedRing<'a, M> = SplitQueueRing<'a, M, UsedRingElement>;

pub struct DescriptorTable<'a, M> {
    table: ArrayRef<'a, M, Descriptor>,
    len: u16,
    free_descriptors: Vec<u16>,
}

impl<'a, M: GuestMemory> DescriptorTable<'a, M> {
    pub fn new(mem: &'a M, addr: GuestAddress, len: u16) -> Self {
        let table = ArrayRef::new(mem, addr, len as usize);
        let free_descriptors = (0..len).rev().collect();

        DescriptorTable {
            table,
            len,
            free_descriptors,
        }
    }

    pub fn load(&self, index: u16) -> Descriptor {
        self.table.ref_at(index as usize).load()
    }

    pub fn store(&self, index: u16, value: Descriptor) {
        self.table.ref_at(index as usize).store(value)
    }

    pub fn total_size(&self) -> u64 {
        (self.len as usize * size_of::<Descriptor>()) as u64
    }

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

pub struct MockSplitQueue<'a, M> {
    mem: &'a M,
    len: u16,
    desc_table_addr: GuestAddress,
    desc_table: DescriptorTable<'a, M>,
    avail_addr: GuestAddress,
    avail: AvailRing<'a, M>,
    used_addr: GuestAddress,
    _used: UsedRing<'a, M>,
    indirect_addr: GuestAddress,
}

impl<'a, M: GuestMemory> MockSplitQueue<'a, M> {
    pub fn new(mem: &'a M, len: u16) -> Self {
        // Use these hard-coded addresses for now.
        let desc_table_addr = GuestAddress(0);
        let avail_addr = GuestAddress(0x1000_0000);
        let used_addr = GuestAddress(0x2000_0000);
        let indirect_addr = GuestAddress(0x3000_0000);

        MockSplitQueue {
            mem,
            len,
            desc_table_addr,
            desc_table: DescriptorTable::new(mem, desc_table_addr, len),
            avail_addr,
            avail: AvailRing::new(mem, avail_addr, len),
            used_addr,
            _used: UsedRing::new(mem, used_addr, len),
            indirect_addr,
        }
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

    pub fn add_chain(&mut self, len: u16) {
        let head_idx = self.desc_table.build_chain(len);
        self.update_avail_idx(head_idx);
    }

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

    pub fn create_queue<A: GuestAddressSpace>(&self, a: A) -> Queue<A> {
        let mut q = Queue::new(a, self.len);
        q.desc_table = self.desc_table_addr;
        q.avail_ring = self.avail_addr;
        q.used_ring = self.used_addr;
        q
    }
}
