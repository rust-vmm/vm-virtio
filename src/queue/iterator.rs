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

use std::num::Wrapping;

use vm_memory::{Address, Bytes, GuestAddress, GuestAddressSpace};

use super::{
    DescriptorChain, Position, Queue, VIRTQ_AVAIL_ELEMENT_SIZE, VIRTQ_AVAIL_RING_HEADER_SIZE,
};

/// Consuming iterator over all available descriptor chain heads in the queue.
pub struct AvailIter<M: GuestAddressSpace> {
    pub(crate) mem: M::T,
    pub(crate) desc_table: GuestAddress,
    pub(crate) avail_ring: GuestAddress,
    pub(crate) last_index: Wrapping<u16>,
    pub(crate) queue_size: u16,
    pub(crate) next_avail: Position,
}

impl<M: GuestAddressSpace> AvailIter<M> {
    /// Create a available descriptor iterator, starting at `idx`.
    pub fn new(queue: &mut Queue<M>, idx: Wrapping<u16>) -> Self {
        AvailIter {
            mem: queue.mem.memory(),
            desc_table: queue.desc_table,
            avail_ring: queue.avail_ring,
            last_index: idx,
            queue_size: queue.actual_size(),
            next_avail: queue.next_avail.clone(),
        }
    }
}

impl<M: GuestAddressSpace> Iterator for AvailIter<M> {
    type Item = DescriptorChain<M>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.next_avail.get() == self.last_index.0 {
            return None;
        }

        // This computation cannot overflow because all the values involved are actually
        // `u16`s cast to `u64`.
        let offset = VIRTQ_AVAIL_RING_HEADER_SIZE
            + (self.next_avail.get() % self.queue_size) as u64 * VIRTQ_AVAIL_ELEMENT_SIZE;

        // The logic in `Queue::is_valid` ensures it's ok to use `unchecked_add` as long
        // as the index is within bounds. We do not currently enforce that a queue is only used
        // after checking `is_valid`, but rather expect the device implementations to do so
        // before activation. The standard also forbids drivers to change queue parameters
        // while the device is "running". A warp-around cannot lead to unsafe memory accesses
        // because the memory model performs its own validations.
        let addr = self.avail_ring.unchecked_add(offset);
        let head_index: u16 = self
            .mem
            .read_obj(addr)
            .map_err(|_| error!("Failed to read from memory {:x}", addr.raw_value()))
            .ok()?;

        self.next_avail.inc();

        Some(DescriptorChain::new(
            self.mem.clone(),
            self.desc_table,
            self.queue_size,
            head_index,
        ))
    }
}
