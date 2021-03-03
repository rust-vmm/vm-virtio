// Portions Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Copyright © 2019 Intel Corporation
//
// Copyright (C) 2021 Alibaba Cloud. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0 AND BSD-3-Clause

use std::cell::RefCell;
use std::ops::Deref;
use std::sync::Mutex;

use super::*;

/// Sink to put used descriptors into virtio queues.
///
/// For split-queue, it puts used descriptors into the used ring.
pub trait QueueSinkerT {
    /// Check whether the queue sinker is ready to process used descriptors.
    fn sinker_ready(&self) -> bool;

    /// Returns the index for the next descriptor in the available ring.
    fn next_used(&self) -> u16;

    /// Sets the index for the next descriptor in the available ring.
    fn set_next_used(&mut self, next_used: u16);

    /// Puts an available descriptor head into the used ring for use by the guest.
    fn add_used(&mut self, head_index: u16, len: u32) -> Result<(), Error>;

    /// Check whether a notification to the guest is needed.
    ///
    /// Please note this method has side effects: once it returns `true`, it considers the
    /// driver will actually be notified, remember the associated index in the used ring, and
    /// won't return `true` again until the driver updates `used_event` and/or the notification
    /// conditions hold once more.
    fn needs_notification(&mut self) -> Result<bool, Error>;
}

impl<S: QueueSinkerT> QueueSinkerT for Arc<Mutex<S>> {
    fn sinker_ready(&self) -> bool {
        self.lock().unwrap().sinker_ready()
    }

    fn next_used(&self) -> u16 {
        self.lock().unwrap().next_used()
    }

    fn set_next_used(&mut self, next_used: u16) {
        self.lock().unwrap().set_next_used(next_used);
    }

    fn add_used(&mut self, head_index: u16, len: u32) -> Result<(), Error> {
        self.lock().unwrap().add_used(head_index, len)
    }

    fn needs_notification(&mut self) -> Result<bool, Error> {
        self.lock().unwrap().needs_notification()
    }
}

impl<S: QueueSinkerT> QueueSinkerT for RefCell<S> {
    fn sinker_ready(&self) -> bool {
        self.deref().sinker_ready()
    }

    fn next_used(&self) -> u16 {
        self.deref().next_used()
    }

    fn set_next_used(&mut self, next_used: u16) {
        self.get_mut().set_next_used(next_used)
    }

    fn add_used(&mut self, head_index: u16, len: u32) -> Result<(), Error> {
        self.get_mut().add_used(head_index, len)
    }

    fn needs_notification(&mut self) -> Result<bool, Error> {
        self.get_mut().needs_notification()
    }
}

/// A default implementation of [QueueSinkerT](trait.QueueSinkerT.html).
pub struct QueueSinker<M: GuestAddressSpace>(pub(crate) Arc<Mutex<Queue<M>>>);

impl<M: GuestAddressSpace> Clone for QueueSinker<M> {
    fn clone(&self) -> Self {
        QueueSinker(self.0.clone())
    }
}

impl<M: GuestAddressSpace> QueueSinkerT for QueueSinker<M> {
    fn sinker_ready(&self) -> bool {
        self.0.lock().unwrap().sinker_ready()
    }

    fn next_used(&self) -> u16 {
        self.0.lock().unwrap().next_used()
    }

    fn set_next_used(&mut self, next_used: u16) {
        self.0.lock().unwrap().set_next_used(next_used)
    }

    fn add_used(&mut self, head_index: u16, len: u32) -> Result<(), Error> {
        self.0.lock().unwrap().add_used(head_index, len)
    }

    fn needs_notification(&mut self) -> Result<bool, Error> {
        self.0.lock().unwrap().needs_notification()
    }
}

#[cfg(test)]
mod tests {
    use super::super::tests::VirtQueue;
    use super::*;
    use vm_memory::GuestMemoryMmap;

    macro_rules! offset_of {
        ($ty:ty, $field:ident) => {
            unsafe { &(*(0 as *const $ty)).$field as *const _ as usize }
        };
    }

    #[test]
    fn test_offset() {
        assert_eq!(offset_of!(VirtqUsedElem, id), 0);
        assert_eq!(offset_of!(VirtqUsedElem, len), 4);
    }

    #[test]
    fn test_add_used() {
        let m = GuestMemoryMmap::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap();
        let vq = VirtQueue::new(GuestAddress(0), &m, 16);

        let mut q = vq.create_queue(&m);
        assert_eq!(vq.used.idx().load(), 0);

        //index too large
        assert!(q.add_used(16, 0x1000).is_err());
        assert_eq!(vq.used.idx().load(), 0);

        //should be ok
        q.add_used(1, 0x1000).unwrap();
        assert_eq!(q.next_used(), 1);
        assert_eq!(vq.used.idx().load(), 1);
        let x = vq.used.ring(0).load();
        assert_eq!(x.id, 1);
        assert_eq!(x.len, 0x1000);
    }

    #[test]
    fn test_sink_is_valid() {
        let m = &GuestMemoryMmap::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap();
        let queue = Queue::new(m, 16);
        let (mut config, _source, _sinker) = queue.split_into_config_source_sinker();

        config.set_used_ring_address(GuestAddress(0x2000));
        config.set_queue_size(16);
        config.set_ready(true);
        assert_eq!(config.is_valid(), true);

        // Available ring not ready
        config.set_ready(false);
        assert_eq!(config.is_valid(), false);
        config.set_ready(true);
        assert_eq!(config.is_valid(), true);

        // Used ring out of range or not aligned
        config.set_used_ring_address(GuestAddress(0x20000));
        assert_eq!(config.is_valid(), false);
        config.set_used_ring_address(GuestAddress(0x1001));
        assert_eq!(config.is_valid(), false);
        config.set_used_ring_address(GuestAddress(0x1000));
        assert_eq!(config.is_valid(), true);

        // Queue size out of range or not aligned
        config.set_queue_size(32);
        assert_eq!(config.is_valid(), false);
        config.set_queue_size(0);
        assert_eq!(config.is_valid(), false);
        config.set_queue_size(15);
        assert_eq!(config.is_valid(), false);
        config.set_queue_size(16);
        assert_eq!(config.is_valid(), true);
    }

    #[test]
    fn test_sink_set_next_used() {
        let m = &GuestMemoryMmap::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap();
        let queue = Queue::new(m, 16);
        let (_config, _source, mut sinker) = queue.split_into_config_source_sinker();

        assert_eq!(sinker.next_used(), 0);
        sinker.set_next_used(1);
        assert_eq!(sinker.next_used(), 1);
        sinker.set_next_used(0xffff);
        assert_eq!(sinker.next_used(), 0xffff);
    }
}
