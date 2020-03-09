// Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Portions Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// SPDX-License-Identifier: Apache-2.0 AND BSD-3-Clause

use std::cmp::min;
use std::mem::size_of;
use std::num::Wrapping;
use std::sync::atomic::{fence, Ordering};

use vm_memory::{Address, ByteValued, Bytes, GuestAddress, GuestMemory, GuestUsize};

pub(super) const VIRTQ_DESC_F_NEXT: u16 = 0x1;
pub(super) const VIRTQ_DESC_F_WRITE: u16 = 0x2;

const VIRTQ_USED_ELEMENT_SIZE: usize = 8;
// Used ring header: flags (u16) + idx (u16)
const VIRTQ_USED_RING_HEADER_SIZE: usize = 4;
// This is the size of the used ring metadata: header + used_event (u16).
// The total size of the used ring is:
// VIRTQ_USED_RING_HMETA_SIZE + VIRTQ_USED_ELEMENT_SIZE * queue_size
const VIRTQ_USED_RING_META_SIZE: usize = VIRTQ_USED_RING_HEADER_SIZE + 2;

const VIRTQ_AVAIL_ELEMENT_SIZE: usize = 2;
// Avail ring header: flags(u16) + idx(u16)
const VIRTQ_AVAIL_RING_HEADER_SIZE: usize = 4;
// This is the size of the available ring metadata: header + avail_event (u16).
// The total size of the available ring is:
// VIRTQ_AVAIL_RING_META_SIZE + VIRTQ_AVAIL_ELEMENT_SIZE * queue_size
const VIRTQ_AVAIL_RING_META_SIZE: usize = VIRTQ_AVAIL_RING_HEADER_SIZE + 2;

// GuestMemory::read_obj() will be used to fetch the descriptor,
// which has an explicit constraint that the entire descriptor doesn't
// cross the page boundary. Otherwise the descriptor may be splitted into
// two mmap regions which causes failure of GuestMemory::read_obj().
//
// The Virtio Spec 1.0 defines the alignment of VirtIO descriptor is 16 bytes,
// which fulfills the explicit constraint of GuestMemory::read_obj().

/// A virtio descriptor constraints with C representation
#[repr(C)]
#[derive(Default, Clone, Copy)]
struct Descriptor {
    addr: u64,
    len: u32,
    flags: u16,
    next: u16,
}

unsafe impl ByteValued for Descriptor {}

/// A virtio descriptor chain.
pub struct DescriptorChain<'a, M: GuestMemory> {
    mem: &'a M,
    desc_table: GuestAddress,
    queue_size: u16,
    ttl: u16, // used to prevent infinite chain cycles

    /// Index into the descriptor table
    pub index: u16,

    /// Guest physical address of device specific data
    pub addr: GuestAddress,

    /// Length of device specific data
    pub len: u32,

    /// Includes next, write, and indirect bits
    pub flags: u16,

    /// Index into the descriptor table of the next descriptor if flags has
    /// the next bit set
    pub next: u16,
}

impl<'a, M: GuestMemory> DescriptorChain<'a, M> {
    fn checked_new(
        mem: &M,
        desc_table: GuestAddress,
        queue_size: u16,
        index: u16,
    ) -> Option<DescriptorChain<M>> {
        if index >= queue_size {
            return None;
        }

        let desc_size = size_of::<Descriptor>();
        let desc_head = match mem.checked_offset(desc_table, (index as usize) * desc_size) {
            Some(a) => a,
            None => return None,
        };
        mem.checked_offset(desc_head, desc_size)?;

        // These reads can't fail unless Guest memory is hopelessly broken.
        let desc = match mem.read_obj::<Descriptor>(desc_head) {
            Ok(ret) => ret,
            Err(_) => {
                // TODO log address
                error!("Failed to read from memory");
                return None;
            }
        };
        let chain = DescriptorChain {
            mem,
            desc_table,
            queue_size,
            ttl: queue_size,
            index,
            addr: GuestAddress(desc.addr),
            len: desc.len,
            flags: desc.flags,
            next: desc.next,
        };

        if chain.is_valid() {
            Some(chain)
        } else {
            None
        }
    }

    fn is_valid(&self) -> bool {
        !(self
            .mem
            .checked_offset(self.addr, self.len as usize)
            .is_none()
            || (self.has_next() && self.next >= self.queue_size))
    }

    /// Checks if this descriptor chain has another descriptor chain linked after it.
    pub fn has_next(&self) -> bool {
        self.flags & VIRTQ_DESC_F_NEXT != 0 && self.ttl > 1
    }

    /// Checks if the driver designated this as a write only descriptor.
    ///
    /// If this is false, this descriptor is read only.
    /// Write only means the the emulated device can write and the driver can read.
    pub fn is_write_only(&self) -> bool {
        self.flags & VIRTQ_DESC_F_WRITE != 0
    }

    /// Returns the next descriptor in this descriptor chain, if there is one.
    ///
    /// Note that this is distinct from the next descriptor chain returned by
    /// [`AvailIter`](struct.AvailIter.html), which is the head of the next
    /// _available_ descriptor chain.
    pub fn next_descriptor(&self) -> Option<DescriptorChain<'a, M>> {
        if self.has_next() {
            DescriptorChain::checked_new(self.mem, self.desc_table, self.queue_size, self.next).map(
                |mut desc| {
                    desc.ttl = self.ttl - 1;
                    desc
                },
            )
        } else {
            None
        }
    }
}

/// Consuming iterator over all available descriptor chain heads in the queue.
pub struct AvailIter<'a, 'b, M: GuestMemory> {
    mem: &'a M,
    desc_table: GuestAddress,
    avail_ring: GuestAddress,
    next_index: Wrapping<u16>,
    last_index: Wrapping<u16>,
    queue_size: u16,
    next_avail: &'b mut Wrapping<u16>,
}

impl<'a, 'b, M: GuestMemory> AvailIter<'a, 'b, M> {
    /// Constructs an empty descriptor iterator.
    pub fn new(mem: &'a M, q_next_avail: &'b mut Wrapping<u16>) -> AvailIter<'a, 'b, M> {
        AvailIter {
            mem,
            desc_table: GuestAddress(0),
            avail_ring: GuestAddress(0),
            next_index: Wrapping(0),
            last_index: Wrapping(0),
            queue_size: 0,
            next_avail: q_next_avail,
        }
    }
}

impl<'a, 'b, M: GuestMemory> Iterator for AvailIter<'a, 'b, M> {
    type Item = DescriptorChain<'a, M>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.next_index == self.last_index {
            return None;
        }

        let offset = (VIRTQ_AVAIL_RING_HEADER_SIZE as u16
            + (self.next_index.0 % self.queue_size) * VIRTQ_AVAIL_ELEMENT_SIZE as u16)
            as usize;
        let avail_addr = match self.mem.checked_offset(self.avail_ring, offset) {
            Some(a) => a,
            None => return None,
        };
        // This index is checked below in checked_new
        let desc_index: u16 = match self.mem.read_obj(avail_addr) {
            Ok(ret) => ret,
            Err(_) => {
                // TODO log address
                error!("Failed to read from memory");
                return None;
            }
        };

        self.next_index += Wrapping(1);

        let desc =
            DescriptorChain::checked_new(self.mem, self.desc_table, self.queue_size, desc_index);
        if desc.is_some() {
            *self.next_avail += Wrapping(1);
        }
        desc
    }
}

#[derive(Clone)]
/// A virtio queue's parameters.
pub struct Queue<'a, M: GuestMemory> {
    mem: &'a M,

    /// The maximal size in elements offered by the device
    max_size: u16,

    next_avail: Wrapping<u16>,
    next_used: Wrapping<u16>,

    /// The queue size in elements the driver selected
    pub size: u16,

    /// Indicates if the queue is finished with configuration
    pub ready: bool,

    /// Guest physical address of the descriptor table
    pub desc_table: GuestAddress,

    /// Guest physical address of the available ring
    pub avail_ring: GuestAddress,

    /// Guest physical address of the used ring
    pub used_ring: GuestAddress,
}

impl<'a, M: GuestMemory> Queue<'a, M> {
    /// Constructs an empty virtio queue with the given `max_size`.
    pub fn new(mem: &M, max_size: u16) -> Queue<M> {
        Queue {
            mem,
            max_size,
            size: max_size,
            ready: false,
            desc_table: GuestAddress(0),
            avail_ring: GuestAddress(0),
            used_ring: GuestAddress(0),
            next_avail: Wrapping(0),
            next_used: Wrapping(0),
        }
    }

    /// Gets the virtio queue maximum size.
    pub fn max_size(&self) -> u16 {
        self.max_size
    }

    /// Return the actual size of the queue, as the driver may not set up a
    /// queue as big as the device allows.
    pub fn actual_size(&self) -> u16 {
        min(self.size, self.max_size)
    }

    /// Check if the virtio queue configuration is valid.
    pub fn is_valid(&self) -> bool {
        let queue_size = self.actual_size() as usize;
        let desc_table = self.desc_table;
        let desc_table_size = size_of::<Descriptor>() * queue_size;
        let avail_ring = self.avail_ring;
        let avail_ring_size = VIRTQ_AVAIL_RING_META_SIZE + VIRTQ_AVAIL_ELEMENT_SIZE * queue_size;
        let used_ring = self.used_ring;
        let used_ring_size = VIRTQ_USED_RING_META_SIZE + VIRTQ_USED_ELEMENT_SIZE * queue_size;
        if !self.ready {
            error!("attempt to use virtio queue that is not marked ready");
            false
        } else if self.size > self.max_size || self.size == 0 || (self.size & (self.size - 1)) != 0
        {
            error!("virtio queue with invalid size: {}", self.size);
            false
        } else if desc_table
            .checked_add(desc_table_size as GuestUsize)
            .map_or(true, |v| !self.mem.address_in_range(v))
        {
            error!(
                "virtio queue descriptor table goes out of bounds: start:0x{:08x} size:0x{:08x}",
                desc_table.raw_value(),
                desc_table_size
            );
            false
        } else if avail_ring
            .checked_add(avail_ring_size as GuestUsize)
            .map_or(true, |v| !self.mem.address_in_range(v))
        {
            error!(
                "virtio queue available ring goes out of bounds: start:0x{:08x} size:0x{:08x}",
                avail_ring.raw_value(),
                avail_ring_size
            );
            false
        } else if used_ring
            .checked_add(used_ring_size as GuestUsize)
            .map_or(true, |v| !self.mem.address_in_range(v))
        {
            error!(
                "virtio queue used ring goes out of bounds: start:0x{:08x} size:0x{:08x}",
                used_ring.raw_value(),
                used_ring_size
            );
            false
        } else if desc_table.mask(0xf) != 0 {
            error!("virtio queue descriptor table breaks alignment contraints");
            false
        } else if avail_ring.mask(0x1) != 0 {
            error!("virtio queue available ring breaks alignment contraints");
            false
        } else if used_ring.mask(0x3) != 0 {
            error!("virtio queue used ring breaks alignment contraints");
            false
        } else {
            true
        }
    }

    /// A consuming iterator over all available descriptor chain heads offered by the driver.
    pub fn iter<'b>(&'b mut self) -> AvailIter<'a, 'b, M> {
        let queue_size = self.actual_size();
        let avail_ring = self.avail_ring;

        let index_addr = match self.mem.checked_offset(avail_ring, 2) {
            Some(ret) => ret,
            None => {
                // TODO log address
                warn!("Invalid offset");
                return AvailIter::new(self.mem, &mut self.next_avail);
            }
        };
        // Note that last_index has no invalid values
        let last_index: u16 = match self.mem.read_obj::<u16>(index_addr) {
            Ok(ret) => ret,
            Err(_) => return AvailIter::new(self.mem, &mut self.next_avail),
        };

        AvailIter {
            mem: self.mem,
            desc_table: self.desc_table,
            avail_ring,
            next_index: self.next_avail,
            last_index: Wrapping(last_index),
            queue_size,
            next_avail: &mut self.next_avail,
        }
    }

    /// Puts an available descriptor head into the used ring for use by the guest.
    pub fn add_used(&mut self, desc_index: u16, len: u32) {
        if desc_index >= self.actual_size() {
            error!(
                "attempted to add out of bounds descriptor to used ring: {}",
                desc_index
            );
            return;
        }

        let used_ring = self.used_ring;
        let next_used = u64::from(self.next_used.0 % self.actual_size());
        let used_elem = used_ring.unchecked_add(4 + next_used * 8);

        // These writes can't fail as we are guaranteed to be within the descriptor ring.
        self.mem
            .write_obj(u32::from(desc_index), used_elem)
            .unwrap();
        self.mem
            .write_obj(len as u32, used_elem.unchecked_add(4))
            .unwrap();

        self.next_used += Wrapping(1);

        // This fence ensures all descriptor writes are visible before the index update is.
        fence(Ordering::Release);

        // We are guaranteed to be within the used ring, this write can't fail.
        self.mem
            .write_obj(self.next_used.0 as u16, used_ring.unchecked_add(2))
            .unwrap();
    }

    /// Goes back one position in the available descriptor chain offered by the driver.
    /// Rust does not support bidirectional iterators. This is the only way to revert the effect
    /// of an iterator increment on the queue.
    pub fn go_to_previous_position(&mut self) {
        self.next_avail -= Wrapping(1);
    }
}

#[cfg(test)]
pub(crate) mod tests {
    extern crate vm_memory;

    use std::marker::PhantomData;
    use std::mem;

    pub use super::*;
    use vm_memory::{GuestAddress, GuestMemoryMmap, VolatileMemory, VolatileRef, VolatileSlice};

    // Represents a virtio descriptor in guest memory.
    pub struct VirtqDesc<'a> {
        desc: VolatileSlice<'a>,
    }

    macro_rules! offset_of {
        ($ty:ty, $field:ident) => {
            unsafe { &(*(0 as *const $ty)).$field as *const _ as usize }
        };
    }

    impl<'a> VirtqDesc<'a> {
        fn new(dtable: &'a VolatileSlice<'a>, i: u16) -> Self {
            let desc = dtable
                .get_slice((i as usize) * Self::dtable_len(1), Self::dtable_len(1))
                .unwrap();
            VirtqDesc { desc }
        }

        pub fn addr(&self) -> VolatileRef<u64> {
            self.desc.get_ref(offset_of!(Descriptor, addr)).unwrap()
        }

        pub fn len(&self) -> VolatileRef<u32> {
            self.desc.get_ref(offset_of!(Descriptor, len)).unwrap()
        }

        pub fn flags(&self) -> VolatileRef<u16> {
            self.desc.get_ref(offset_of!(Descriptor, flags)).unwrap()
        }

        pub fn next(&self) -> VolatileRef<u16> {
            self.desc.get_ref(offset_of!(Descriptor, next)).unwrap()
        }

        pub fn set(&self, addr: u64, len: u32, flags: u16, next: u16) {
            self.addr().store(addr);
            self.len().store(len);
            self.flags().store(flags);
            self.next().store(next);
        }

        fn dtable_len(nelem: u16) -> usize {
            16 * nelem as usize
        }
    }

    // Represents a virtio queue ring. The only difference between the used and available rings,
    // is the ring element type.
    pub struct VirtqRing<'a, T> {
        ring: VolatileSlice<'a>,
        start: GuestAddress,
        qsize: u16,
        _marker: PhantomData<*const T>,
    }

    impl<'a, T> VirtqRing<'a, T>
    where
        T: vm_memory::ByteValued,
    {
        fn new(
            start: GuestAddress,
            mem: &'a GuestMemoryMmap,
            qsize: u16,
            alignment: GuestUsize,
        ) -> Self {
            assert_eq!(start.0 & (alignment - 1), 0);

            let (region, addr) = mem.to_region_addr(start).unwrap();
            let size = Self::ring_len(qsize);
            let ring = region.get_slice(addr.raw_value() as usize, size).unwrap();

            let result = VirtqRing {
                ring,
                start,
                qsize,
                _marker: PhantomData,
            };

            result.flags().store(0);
            result.idx().store(0);
            result.event().store(0);
            result
        }

        pub fn start(&self) -> GuestAddress {
            self.start
        }

        pub fn end(&self) -> GuestAddress {
            self.start.unchecked_add(self.ring.len() as GuestUsize)
        }

        pub fn flags(&self) -> VolatileRef<u16> {
            self.ring.get_ref(0).unwrap()
        }

        pub fn idx(&self) -> VolatileRef<u16> {
            self.ring.get_ref(2).unwrap()
        }

        fn ring_offset(i: u16) -> usize {
            4 + mem::size_of::<T>() * (i as usize)
        }

        pub fn ring(&self, i: u16) -> VolatileRef<T> {
            assert!(i < self.qsize);
            self.ring.get_ref(Self::ring_offset(i)).unwrap()
        }

        pub fn event(&self) -> VolatileRef<u16> {
            self.ring.get_ref(Self::ring_offset(self.qsize)).unwrap()
        }

        fn ring_len(qsize: u16) -> usize {
            Self::ring_offset(qsize) + 2
        }
    }

    #[repr(C)]
    #[derive(Clone, Copy, Default)]
    pub struct VirtqUsedElem {
        pub id: u32,
        pub len: u32,
    }

    unsafe impl vm_memory::ByteValued for VirtqUsedElem {}

    pub type VirtqAvail<'a> = VirtqRing<'a, u16>;
    pub type VirtqUsed<'a> = VirtqRing<'a, VirtqUsedElem>;

    trait GuestAddressExt {
        fn align_up(&self, x: GuestUsize) -> GuestAddress;
    }
    impl GuestAddressExt for GuestAddress {
        fn align_up(&self, x: GuestUsize) -> GuestAddress {
            return Self((self.0 + (x - 1)) & !(x - 1));
        }
    }

    pub struct VirtQueue<'a> {
        start: GuestAddress,
        dtable: VolatileSlice<'a>,
        avail: VirtqAvail<'a>,
        used: VirtqUsed<'a>,
    }

    impl<'a> VirtQueue<'a> {
        // We try to make sure things are aligned properly :-s
        pub fn new(start: GuestAddress, mem: &'a GuestMemoryMmap, qsize: u16) -> Self {
            // power of 2?
            assert!(qsize > 0 && qsize & (qsize - 1) == 0);

            let (region, addr) = mem.to_region_addr(start).unwrap();
            let dtable = region
                .get_slice(addr.raw_value() as usize, VirtqDesc::dtable_len(qsize))
                .unwrap();

            const AVAIL_ALIGN: GuestUsize = 2;

            let avail_addr = start
                .unchecked_add(VirtqDesc::dtable_len(qsize) as GuestUsize)
                .align_up(AVAIL_ALIGN);
            let avail = VirtqAvail::new(avail_addr, mem, qsize, AVAIL_ALIGN);

            const USED_ALIGN: GuestUsize = 4;

            let used_addr = avail.end().align_up(USED_ALIGN);
            let used = VirtqUsed::new(used_addr, mem, qsize, USED_ALIGN);

            VirtQueue {
                start,
                dtable,
                avail,
                used,
            }
        }

        fn size(&self) -> u16 {
            (self.dtable.len() / VirtqDesc::dtable_len(1)) as u16
        }

        fn dtable(&self, i: u16) -> VirtqDesc {
            VirtqDesc::new(&self.dtable, i)
        }

        fn dtable_start(&self) -> GuestAddress {
            self.start
        }

        fn avail_start(&self) -> GuestAddress {
            self.avail.start()
        }

        fn used_start(&self) -> GuestAddress {
            self.used.start()
        }

        // Creates a new Queue, using the underlying memory regions represented by the VirtQueue.
        pub fn create_queue(&self, mem: &'a GuestMemoryMmap) -> Queue<GuestMemoryMmap> {
            let mut q = Queue::new(mem, self.size());

            q.size = self.size();
            q.ready = true;
            q.desc_table = self.dtable_start();
            q.avail_ring = self.avail_start();
            q.used_ring = self.used_start();

            q
        }

        pub fn start(&self) -> GuestAddress {
            self.dtable_start()
        }

        pub fn end(&self) -> GuestAddress {
            self.used.end()
        }
    }

    #[test]
    pub fn test_offset() {
        assert_eq!(offset_of!(Descriptor, addr), 0);
        assert_eq!(offset_of!(Descriptor, len), 8);
        assert_eq!(offset_of!(Descriptor, flags), 12);
        assert_eq!(offset_of!(Descriptor, next), 14);
    }

    #[test]
    fn test_checked_new_descriptor_chain() {
        let m = &GuestMemoryMmap::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap();
        let vq = VirtQueue::new(GuestAddress(0), m, 16);

        assert!(vq.end().0 < 0x1000);

        // index >= queue_size
        assert!(DescriptorChain::checked_new(m, vq.start(), 16, 16).is_none());

        // desc_table address is way off
        assert!(DescriptorChain::checked_new(m, GuestAddress(0x00ff_ffff_ffff), 16, 0).is_none());

        // the addr field of the descriptor is way off
        vq.dtable(0).addr().store(0x0fff_ffff_ffff);
        assert!(DescriptorChain::checked_new(m, vq.start(), 16, 0).is_none());

        // let's create some invalid chains

        {
            // the addr field of the desc is ok now
            vq.dtable(0).addr().store(0x1000);
            // ...but the length is too large
            vq.dtable(0).len().store(0xffff_ffff);
            assert!(DescriptorChain::checked_new(m, vq.start(), 16, 0).is_none());
        }

        {
            // the first desc has a normal len now, and the next_descriptor flag is set
            vq.dtable(0).len().store(0x1000);
            vq.dtable(0).flags().store(VIRTQ_DESC_F_NEXT);
            //..but the the index of the next descriptor is too large
            vq.dtable(0).next().store(16);

            assert!(DescriptorChain::checked_new(m, vq.start(), 16, 0).is_none());
        }

        // finally, let's test an ok chain

        {
            vq.dtable(0).next().store(1);
            vq.dtable(1).set(0x2000, 0x1000, 0, 0);

            let c = DescriptorChain::checked_new(m, vq.start(), 16, 0).unwrap();

            assert_eq!(c.mem as *const GuestMemoryMmap, m as *const GuestMemoryMmap);
            assert_eq!(c.desc_table, vq.dtable_start());
            assert_eq!(c.queue_size, 16);
            assert_eq!(c.ttl, c.queue_size);
            assert_eq!(c.index, 0);
            assert_eq!(c.addr, GuestAddress(0x1000));
            assert_eq!(c.len, 0x1000);
            assert_eq!(c.flags, VIRTQ_DESC_F_NEXT);
            assert_eq!(c.next, 1);

            assert!(c.next_descriptor().unwrap().next_descriptor().is_none());
        }
    }

    #[test]
    fn test_queue_and_iterator() {
        let m = &GuestMemoryMmap::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap();
        let vq = VirtQueue::new(GuestAddress(0), m, 16);

        let mut q = vq.create_queue(m);

        // q is currently valid
        assert!(q.is_valid());

        // shouldn't be valid when not marked as ready
        q.ready = false;
        assert!(!q.is_valid());
        q.ready = true;

        // or when size > max_size
        q.size = q.max_size << 1;
        assert!(!q.is_valid());
        q.size = q.max_size;

        // or when size is 0
        q.size = 0;
        assert!(!q.is_valid());
        q.size = q.max_size;

        // or when size is not a power of 2
        q.size = 11;
        assert!(!q.is_valid());
        q.size = q.max_size;

        // or if the various addresses are off

        q.desc_table = GuestAddress(0xffff_ffff);
        assert!(!q.is_valid());
        q.desc_table = GuestAddress(0x1001);
        assert!(!q.is_valid());
        q.desc_table = vq.dtable_start();

        q.avail_ring = GuestAddress(0xffff_ffff);
        assert!(!q.is_valid());
        q.avail_ring = GuestAddress(0x1001);
        assert!(!q.is_valid());
        q.avail_ring = vq.avail_start();

        q.used_ring = GuestAddress(0xffff_ffff);
        assert!(!q.is_valid());
        q.used_ring = GuestAddress(0x1001);
        assert!(!q.is_valid());
        q.used_ring = vq.used_start();

        {
            // an invalid queue should return an iterator with no next
            q.ready = false;
            let mut i = q.iter();
            assert!(i.next().is_none());
        }

        q.ready = true;

        // now let's create two simple descriptor chains

        {
            for j in 0..5 {
                vq.dtable(j).set(
                    0x1000 * (j + 1) as u64,
                    0x1000,
                    VIRTQ_DESC_F_NEXT,
                    (j + 1) as u16,
                );
            }

            // the chains are (0, 1) and (2, 3, 4)
            vq.dtable(1).flags().store(0);
            vq.dtable(4).flags().store(0);
            vq.avail.ring(0).store(0);
            vq.avail.ring(1).store(2);
            vq.avail.idx().store(2);

            let mut i = q.iter();

            {
                let mut c = i.next().unwrap();
                c = c.next_descriptor().unwrap();
                assert!(!c.has_next());
            }

            {
                let mut c = i.next().unwrap();
                c = c.next_descriptor().unwrap();
                c = c.next_descriptor().unwrap();
                assert!(!c.has_next());
            }
        }

        // also test go_to_previous_position() works as expected
        {
            assert!(q.iter().next().is_none());
            q.go_to_previous_position();
            let mut c = q.iter().next().unwrap();
            c = c.next_descriptor().unwrap();
            c = c.next_descriptor().unwrap();
            assert!(!c.has_next());
        }
    }

    #[test]
    fn test_add_used() {
        let m = &GuestMemoryMmap::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap();
        let vq = VirtQueue::new(GuestAddress(0), m, 16);

        let mut q = vq.create_queue(m);
        assert_eq!(vq.used.idx().load(), 0);

        //index too large
        q.add_used(16, 0x1000);
        assert_eq!(vq.used.idx().load(), 0);

        //should be ok
        q.add_used(1, 0x1000);
        assert_eq!(vq.used.idx().load(), 1);
        let x = vq.used.ring(0).load();
        assert_eq!(x.id, 1);
        assert_eq!(x.len, 0x1000);
    }
}
