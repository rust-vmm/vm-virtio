// Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Portions Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// Copyright © 2019 Intel Corporation
//
// Copyright (C) 2021 Alibaba Cloud. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0 AND BSD-3-Clause

use std::mem::size_of;

use vm_memory::{Address, Bytes, GuestAddress, GuestAddressSpace};

use super::{Descriptor, Error, VIRTQ_DESCRIPTOR_SIZE};

/// A virtio descriptor chain.
#[derive(Clone)]
pub struct DescriptorChain<M: GuestAddressSpace> {
    mem: M::T,
    desc_table: GuestAddress,
    queue_size: u16,
    head_index: u16,
    next_index: u16,
    ttl: u16,
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
    pub fn new(mem: M::T, desc_table: GuestAddress, queue_size: u16, head_index: u16) -> Self {
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
    fn process_indirect_descriptor(&mut self, desc: Descriptor) -> Result<(), Error> {
        if self.is_indirect {
            return Err(Error::InvalidIndirectDescriptor);
        }

        let table_len = (desc.len() as usize) / VIRTQ_DESCRIPTOR_SIZE;
        // Check the target indirect descriptor table is correctly aligned.
        if desc.addr().raw_value() & (VIRTQ_DESCRIPTOR_SIZE as u64 - 1) != 0
            || (desc.len() as usize) & (VIRTQ_DESCRIPTOR_SIZE - 1) != 0
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

#[cfg(test)]
mod tests {
    use super::super::tests::{VirtQueue, VirtqDesc};
    use super::super::{VIRTQ_DESC_F_INDIRECT, VIRTQ_DESC_F_NEXT, VIRTQ_DESC_F_WRITE};
    use super::*;

    use std::ops::Deref;
    use std::sync::Arc;
    use vm_memory::{GuestMemory, GuestMemoryMmap, GuestMemoryRegion, MemoryRegionAddress};

    #[test]
    fn test_checked_new_descriptor_chain() {
        let m = Arc::new(GuestMemoryMmap::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap());
        let vq = VirtQueue::new(GuestAddress(0), &m, 16);

        assert!(vq.end().0 < 0x1000);

        // index >= queue_size
        assert!(
            DescriptorChain::<Arc<GuestMemoryMmap>>::new(m.clone(), vq.start(), 16, 16)
                .next()
                .is_none()
        );

        // desc_table address is way off
        assert!(DescriptorChain::<Arc<GuestMemoryMmap>>::new(
            m.clone(),
            GuestAddress(0x00ff_ffff_ffff),
            16,
            0
        )
        .next()
        .is_none());

        {
            // the first desc has a normal len, and the next_descriptor flag is set
            vq.dtable(0).addr().store(0x1000);
            vq.dtable(0).len().store(0x1000);
            vq.dtable(0).flags().store(VIRTQ_DESC_F_NEXT);
            //..but the the index of the next descriptor is too large
            vq.dtable(0).next().store(16);

            let mut c = DescriptorChain::<Arc<GuestMemoryMmap>>::new(m.clone(), vq.start(), 16, 0);
            c.next().unwrap();
            assert!(c.next().is_none());
        }

        // finally, let's test an ok chain
        {
            vq.dtable(0).next().store(1);
            vq.dtable(1).set(0x2000, 0x1000, 0, 0);

            let mut c = DescriptorChain::<Arc<GuestMemoryMmap>>::new(m.clone(), vq.start(), 16, 0);

            assert_eq!(
                c.memory() as *const GuestMemoryMmap,
                m.deref() as *const GuestMemoryMmap
            );
            assert_eq!(c.desc_table, vq.dtable_start());
            assert_eq!(c.queue_size, 16);
            assert_eq!(c.ttl, c.queue_size);
            let desc = c.next().unwrap();
            assert_eq!(desc.addr(), GuestAddress(0x1000));
            assert_eq!(desc.len(), 0x1000);
            assert_eq!(desc.flags(), VIRTQ_DESC_F_NEXT);
            assert_eq!(desc.next(), 1);

            assert!(c.next().is_some());
            assert!(c.next().is_none());
        }
    }

    #[test]
    fn test_new_from_indirect_descriptor() {
        let m = Arc::new(GuestMemoryMmap::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap());
        let vq = VirtQueue::new(GuestAddress(0), &m, 16);

        // create a chain with two descriptor pointing to an indirect tables
        let desc = vq.dtable(0);
        desc.set(0x1000, 0x1000, VIRTQ_DESC_F_INDIRECT | VIRTQ_DESC_F_NEXT, 1);
        let desc = vq.dtable(1);
        desc.set(0x2000, 0x1000, VIRTQ_DESC_F_INDIRECT | VIRTQ_DESC_F_NEXT, 2);
        let desc = vq.dtable(2);
        desc.set(0x3000, 0x1000, 0, 0);

        let mut c: DescriptorChain<Arc<GuestMemoryMmap>> =
            DescriptorChain::new(m.clone(), vq.start(), 16, 0);

        // The chain logic hasn't parsed the indirect descriptor yet.
        assert!(!c.is_indirect);

        let region = m.find_region(GuestAddress(0)).unwrap();
        let dtable = region
            .get_slice(MemoryRegionAddress(0x1000u64), VirtqDesc::dtable_len(4))
            .unwrap();
        // create an indirect table with 4 chained descriptors
        let mut indirect_table = Vec::with_capacity(4 as usize);
        for j in 0..4 {
            let desc = VirtqDesc::new(&dtable, j);
            if j < 3 {
                desc.set(0x1000, 0x1000, VIRTQ_DESC_F_NEXT, (j + 1) as u16);
            } else {
                desc.set(0x1000, 0x1000, 0, 0 as u16);
            }
            indirect_table.push(desc);
        }

        let dtable2 = region
            .get_slice(MemoryRegionAddress(0x2000u64), VirtqDesc::dtable_len(1))
            .unwrap();
        let desc2 = VirtqDesc::new(&dtable2, 0);
        desc2.set(0x8000, 0x1000, 0, 0);

        assert_eq!(c.head_index(), 0);
        // try to iterate through the first indirect descriptor chain
        for j in 0..4 {
            let desc = c.next().unwrap();
            assert!(c.is_indirect);
            if j < 3 {
                assert_eq!(desc.flags(), VIRTQ_DESC_F_NEXT);
                assert_eq!(desc.next(), j + 1);
            }
        }
    }

    #[test]
    fn test_indirect_descriptor_err() {
        {
            let m = Arc::new(GuestMemoryMmap::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap());
            let vq = VirtQueue::new(GuestAddress(0), &m, 16);

            // create a chain with a descriptor pointing to an indirect table
            let desc = vq.dtable(0);
            desc.set(0x1001, 0x1000, VIRTQ_DESC_F_INDIRECT, 0);

            let mut c: DescriptorChain<Arc<GuestMemoryMmap>> =
                DescriptorChain::new(m.clone(), vq.start(), 16, 0);

            assert!(c.next().is_none());
        }

        {
            let m = Arc::new(GuestMemoryMmap::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap());
            let vq = VirtQueue::new(GuestAddress(0), &m, 16);

            // create a chain with a descriptor pointing to an indirect table
            let desc = vq.dtable(0);
            desc.set(0x1000, 0x1001, VIRTQ_DESC_F_INDIRECT, 0);

            let mut c: DescriptorChain<Arc<GuestMemoryMmap>> =
                DescriptorChain::new(m.clone(), vq.start(), 16, 0);

            assert!(c.next().is_none());
        }
    }

    #[test]
    fn test_descriptor_chain_readable() {
        let m = Arc::new(GuestMemoryMmap::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap());
        let vq = VirtQueue::new(GuestAddress(0), &m, 16);

        assert!(vq.end().0 < 0x1000);

        vq.dtable(0).set(0x1000, 0x1000, VIRTQ_DESC_F_NEXT, 1);
        vq.dtable(1).set(0x2000, 0x1000, VIRTQ_DESC_F_NEXT, 2);
        vq.dtable(2).set(0x3000, 0x1000, VIRTQ_DESC_F_WRITE, 0);

        let c: DescriptorChain<Arc<GuestMemoryMmap>> =
            DescriptorChain::new(m.clone(), vq.start(), 16, 0);
        let mut readable = c.readable();
        assert!(readable.next().is_some());
        assert!(readable.next().is_some());
        assert!(readable.next().is_none());
    }

    #[test]
    fn test_descriptor_chain_writable() {
        let m = Arc::new(GuestMemoryMmap::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap());
        let vq = VirtQueue::new(GuestAddress(0), &m, 16);

        assert!(vq.end().0 < 0x1000);

        vq.dtable(0).set(0x1000, 0x1000, VIRTQ_DESC_F_NEXT, 1);
        vq.dtable(1).set(0x2000, 0x1000, VIRTQ_DESC_F_NEXT, 2);
        vq.dtable(2)
            .set(0x3000, 0x1000, VIRTQ_DESC_F_WRITE | VIRTQ_DESC_F_NEXT, 3);
        vq.dtable(3).set(0x4000, 0x1000, VIRTQ_DESC_F_WRITE, 0);

        let c: DescriptorChain<Arc<GuestMemoryMmap>> =
            DescriptorChain::new(m.clone(), vq.start(), 16, 0);
        let mut writable = c.writable();
        assert!(writable.next().is_some());
        assert!(writable.next().is_some());
        assert!(writable.next().is_none());
    }
}
