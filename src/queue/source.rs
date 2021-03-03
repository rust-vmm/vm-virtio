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

use vm_memory::GuestAddressSpace;

use super::*;

/// Source to fetch available descriptors from a virtio queue.
///
/// For split-queue, it fetches available descriptors from the available ring.
pub trait QueueSourceT {
    /// Associated type to access guest memory.
    type M: GuestAddressSpace;

    /// Associated type of the iterator returned by `iter()`.
    type I: Iterator<Item = DescriptorChain<Self::M>>;

    /// Check whether the queue source is ready to process available descriptors.
    fn source_ready(&self) -> bool;

    /// Returns the index for the next descriptor in the available ring.
    fn next_avail(&self) -> u16;

    /// Sets the index for the next descriptor in the available ring.
    fn set_next_avail(&mut self, next_avail: u16);

    /// A consuming iterator over all available descriptor chain heads offered by the driver.
    fn iter(&mut self) -> Result<Self::I, Error>;

    /// Goes back one position in the available descriptor chain offered by the driver.
    /// Rust does not support bidirectional iterators. This is the only way to revert the effect
    /// of an iterator increment on the queue.
    fn go_to_previous_position(&mut self);

    /// Enable notification events from the guest driver. Returns true if one or more descriptors
    /// can be consumed from the available ring after notifications were enabled (and thus it's
    /// possible there will be no corresponding notification).
    // TODO: Turn this into a doc comment/example.
    // With the current implementation, a common way of consuming entries from the available ring
    // while also leveraging notification suppression is to use a loop, for example:
    //
    // loop {
    //     // We have to explicitly disable notifications if `VIRTIO_F_EVENT_IDX` has not been
    //     // negotiated.
    //     self.disable_notification()?;
    //
    //     for chain in self.iter()? {
    //         // Do something with each chain ...
    //         // Let's assume we process all available chains here.
    //     }
    //
    //     // If `enable_notification` returns `true`, the driver has added more entries to the
    //     // available ring.
    //     if !self.enable_notification()? {
    //         break;
    //     }
    // }
    fn enable_notification(&mut self) -> Result<bool, Error>;

    /// Disable notification events from the guest driver.
    fn disable_notification(&mut self) -> Result<(), Error>;
}

impl<S: QueueSourceT> QueueSourceT for Arc<Mutex<S>> {
    type M = <S as QueueSourceT>::M;
    type I = <S as QueueSourceT>::I;

    fn source_ready(&self) -> bool {
        self.lock().unwrap().source_ready()
    }

    fn next_avail(&self) -> u16 {
        self.lock().unwrap().next_avail()
    }

    fn set_next_avail(&mut self, next_avail: u16) {
        self.lock().unwrap().set_next_avail(next_avail)
    }

    fn iter(&mut self) -> Result<Self::I, Error> {
        self.lock().unwrap().iter()
    }

    fn go_to_previous_position(&mut self) {
        panic!("You should go_to_previous_position() from concurrent access!");
    }

    fn enable_notification(&mut self) -> Result<bool, Error> {
        self.lock().unwrap().enable_notification()
    }

    fn disable_notification(&mut self) -> Result<(), Error> {
        self.lock().unwrap().disable_notification()
    }
}

impl<S: QueueSourceT> QueueSourceT for RefCell<S> {
    type M = <S as QueueSourceT>::M;
    type I = <S as QueueSourceT>::I;

    fn source_ready(&self) -> bool {
        self.deref().source_ready()
    }

    fn next_avail(&self) -> u16 {
        self.deref().next_avail()
    }

    fn set_next_avail(&mut self, next_avail: u16) {
        self.get_mut().set_next_avail(next_avail)
    }

    fn iter(&mut self) -> Result<Self::I, Error> {
        self.get_mut().iter()
    }

    fn go_to_previous_position(&mut self) {
        self.get_mut().go_to_previous_position()
    }

    fn enable_notification(&mut self) -> Result<bool, Error> {
        self.get_mut().enable_notification()
    }

    fn disable_notification(&mut self) -> Result<(), Error> {
        self.get_mut().disable_notification()
    }
}

#[cfg(test)]
mod tests {
    use super::super::QueueConfigT;
    use super::*;
    use vm_memory::GuestMemoryMmap;

    #[test]
    #[should_panic]
    fn test_invalid_go_to_previous() {
        let m = &GuestMemoryMmap::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap();
        let queue = Queue::new(m, 16);
        let (_config, mut source, _sinker) = queue.split_into_config_source_sinker();

        source.go_to_previous_position();
    }

    #[test]
    fn test_source_is_valid() {
        let m = &GuestMemoryMmap::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap();
        let queue = Queue::new(m, 16);
        let (mut config, _queue) = queue.split_into_config_queue();

        config.set_desc_table_address(GuestAddress(0x1000));
        config.set_used_ring_address(GuestAddress(0x2000));
        config.set_avail_ring_address(GuestAddress(0x3000));
        config.set_queue_size(16);
        config.set_ready(true);
        assert_eq!(config.is_valid(), true);
        assert_eq!(config.ready(), true);
        assert_eq!(config.desc_table_address(), GuestAddress(0x1000));
        assert_eq!(config.used_ring_address(), GuestAddress(0x2000));
        assert_eq!(config.avail_ring_address(), GuestAddress(0x3000));
        assert_eq!(config.event_idx(), false);

        // Available ring not ready
        config.set_ready(false);
        assert_eq!(config.is_valid(), false);
        config.set_ready(true);
        assert_eq!(config.is_valid(), true);

        // Descriptor table out of range or not aligned
        config.set_desc_table_address(GuestAddress(0x20000));
        assert_eq!(config.is_valid(), false);
        config.set_desc_table_address(GuestAddress(0x1001));
        assert_eq!(config.is_valid(), false);
        config.set_desc_table_address(GuestAddress(0x1000));
        assert_eq!(config.is_valid(), true);

        // Available ring out of range or not aligned
        config.set_avail_ring_address(GuestAddress(0x20000));
        assert_eq!(config.is_valid(), false);
        config.set_avail_ring_address(GuestAddress(0x2001));
        assert_eq!(config.is_valid(), false);
        config.set_avail_ring_address(GuestAddress(0x2000));
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
    fn test_source_next_avail() {
        let m = &GuestMemoryMmap::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap();
        let mut source = Arc::new(Mutex::new(Queue::new(m, 16)));

        assert_eq!(source.next_avail(), 0);
        source.set_next_avail(1);
        assert_eq!(source.next_avail(), 1);

        source.set_next_avail(2);
        assert_eq!(source.next_avail(), 2);
    }
}
