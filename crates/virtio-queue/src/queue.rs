// Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Portions Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// Copyright © 2019 Intel Corporation
//
// Copyright (C) 2020-2021 Alibaba Cloud. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0 AND BSD-3-Clause

use std::num::Wrapping;
use std::ops::Deref;
use std::sync::atomic::Ordering;

use vm_memory::GuestAddressSpace;

use crate::{AvailIter, Error, QueueState, QueueStateGuard, QueueStateOwnedT, QueueStateT};

/// A convenient wrapper struct for a virtio queue, with associated `GuestMemory` object.
///
/// # Example
///
/// ```rust
/// use virtio_queue::{Queue, QueueState};
/// use vm_memory::{Bytes, GuestAddress, GuestAddressSpace, GuestMemoryMmap};
///
/// let m = GuestMemoryMmap::<()>::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap();
/// let mut queue = Queue::<&GuestMemoryMmap, QueueState>::new(&m, 1024);
///
/// // First, the driver sets up the queue; this set up is done via writes on the bus (PCI, MMIO).
/// queue.set_size(8);
/// queue.set_desc_table_address(Some(0x1000), None);
/// queue.set_avail_ring_address(Some(0x2000), None);
/// queue.set_used_ring_address(Some(0x3000), None);
/// queue.set_event_idx(true);
/// queue.set_ready(true);
/// // The user should check if the queue is valid before starting to use it.
/// assert!(queue.is_valid());
///
/// // Here the driver would add entries in the available ring and then update the `idx` field of
/// // the available ring (address = 0x2000 + 2).
/// m.write_obj(3, GuestAddress(0x2002));
///
/// loop {
///     queue.disable_notification().unwrap();
///
///     // Consume entries from the available ring.
///     while let Some(chain) = queue.iter().unwrap().next() {
///         // Process the descriptor chain, and then add an entry in the used ring and optionally
///         // notify the driver.
///         queue.add_used(chain.head_index(), 0x100).unwrap();
///
///         if queue.needs_notification().unwrap() {
///             // Here we would notify the driver it has new entries in the used ring to consume.
///         }
///     }
///     if !queue.enable_notification().unwrap() {
///         break;
///     }
/// }
///
/// // We can reset the queue at some point.
/// queue.reset();
/// // The queue should not be ready after reset.
/// assert!(!queue.ready());
/// ```
#[derive(Clone, Debug)]
pub struct Queue<M: GuestAddressSpace, S: QueueStateT = QueueState> {
    /// Guest memory object associated with the queue.
    pub mem: M,
    /// Virtio queue state.
    pub state: S,
}

impl<M: GuestAddressSpace, S: QueueStateT> Queue<M, S> {
    /// Construct an empty virtio queue with the given `max_size`.
    ///
    /// # Arguments
    /// * `mem` - the guest memory object that can be used to access the queue buffers.
    /// * `max_size` - the maximum size (and the default one) of the queue.
    pub fn new(mem: M, max_size: u16) -> Self {
        Queue {
            mem,
            state: S::new(max_size),
        }
    }

    /// Check whether the queue configuration is valid.
    pub fn is_valid(&self) -> bool {
        self.state.is_valid(self.mem.memory().deref())
    }

    /// Reset the queue to the initial state.
    pub fn reset(&mut self) {
        self.state.reset()
    }

    /// Get an exclusive reference to the underlying `QueueState` object.
    ///
    /// Logically this method will acquire the underlying lock protecting the `QueueState` Object.
    /// The lock will be released when the returned object gets dropped.
    pub fn lock(&mut self) -> <S as QueueStateGuard>::G {
        self.state.lock()
    }

    /// Get the maximum size of the virtio queue.
    pub fn max_size(&self) -> u16 {
        self.state.max_size()
    }

    /// Configure the queue size for the virtio queue.
    ///
    /// # Arguments
    /// * `size` - the queue size; it should be a power of two, different than 0 and less than or
    ///            equal to the value reported by `max_size()`, otherwise the queue size remains the
    ///            default one (which is the maximum one).
    pub fn set_size(&mut self, size: u16) {
        self.state.set_size(size);
    }

    /// Check whether the queue is ready to be processed.
    pub fn ready(&self) -> bool {
        self.state.ready()
    }

    /// Configure the queue to the `ready for processing` state.
    ///
    /// # Arguments
    /// * `ready` - a boolean to indicate whether the queue is ready to be used or not.
    pub fn set_ready(&mut self, ready: bool) {
        self.state.set_ready(ready)
    }

    /// Set the descriptor table address for the queue.
    ///
    /// The descriptor table address is 64-bit, the corresponding part will be updated if 'low'
    /// and/or `high` is `Some` and valid.
    ///
    /// # Arguments
    /// * `low` - an optional value for the lowest 32 bits of the address.
    /// * `high` - an optional value for the highest 32 bits of the address.
    pub fn set_desc_table_address(&mut self, low: Option<u32>, high: Option<u32>) {
        self.state.set_desc_table_address(low, high);
    }

    /// Set the available ring address for the queue.
    ///
    /// The available ring address is 64-bit, the corresponding part will be updated if 'low'
    /// and/or `high` is `Some` and valid.
    ///
    /// # Arguments
    /// * `low` - an optional value for the lowest 32 bits of the address.
    /// * `high` - an optional value for the highest 32 bits of the address.
    pub fn set_avail_ring_address(&mut self, low: Option<u32>, high: Option<u32>) {
        self.state.set_avail_ring_address(low, high);
    }

    /// Set the used ring address for the queue.
    ///
    /// The used ring address is 64-bit, the corresponding part will be updated if 'low'
    /// and/or `high` is `Some` and valid.
    ///
    /// # Arguments
    /// * `low` - an optional value for the lowest 32 bits of the address.
    /// * `high` - an optional value for the highest 32 bits of the address.
    pub fn set_used_ring_address(&mut self, low: Option<u32>, high: Option<u32>) {
        self.state.set_used_ring_address(low, high);
    }

    /// Enable/disable the VIRTIO_F_RING_EVENT_IDX feature for interrupt coalescing.
    ///
    /// # Arguments
    /// * `enabled` - a boolean to indicate whether the VIRTIO_F_RING_EVENT_IDX feature was
    ///               successfully negotiated or not.
    pub fn set_event_idx(&mut self, enabled: bool) {
        self.state.set_event_idx(enabled)
    }

    /// Read the `idx` field from the available ring.
    ///
    /// # Arguments
    /// * `order` - the memory ordering used to access the `idx` field from memory.
    pub fn avail_idx(&self, order: Ordering) -> Result<Wrapping<u16>, Error> {
        self.state.avail_idx(self.mem.memory().deref(), order)
    }

    /// Reads the `idx` field from the used ring.
    ///
    /// # Arguments
    /// * `order` - the memory ordering used to access the `idx` field from memory.
    pub fn used_idx(&self, order: Ordering) -> Result<Wrapping<u16>, Error> {
        self.state.used_idx(self.mem.memory().deref(), order)
    }

    /// Put a used descriptor head into the used ring.
    ///
    /// # Arguments
    /// * `head_index` - the index of the used descriptor chain.
    /// * `len` - the total length of the descriptor chain which was used (written to).
    pub fn add_used(&mut self, head_index: u16, len: u32) -> Result<(), Error> {
        self.state
            .add_used(self.mem.memory().deref(), head_index, len)
    }

    /// Enable notification events from the guest driver.
    ///
    /// Return true if one or more descriptors can be consumed from the available ring after
    /// notifications were enabled (and thus it's possible there will be no corresponding
    /// notification).
    pub fn enable_notification(&mut self) -> Result<bool, Error> {
        self.state.enable_notification(self.mem.memory().deref())
    }

    /// Disable notification events from the guest driver.
    pub fn disable_notification(&mut self) -> Result<(), Error> {
        self.state.disable_notification(self.mem.memory().deref())
    }

    /// Check whether a notification to the guest is needed.
    ///
    /// Please note this method has side effects: once it returns `true`, it considers the
    /// driver will actually be notified, remember the associated index in the used ring, and
    /// won't return `true` again until the driver updates `used_event` and/or the notification
    /// conditions hold once more.
    pub fn needs_notification(&mut self) -> Result<bool, Error> {
        self.state.needs_notification(self.mem.memory().deref())
    }

    /// Return the index of the next entry in the available ring.
    pub fn next_avail(&self) -> u16 {
        self.state.next_avail()
    }

    /// Returns the index for the next descriptor in the used ring.
    pub fn next_used(&self) -> u16 {
        self.state.next_used()
    }

    /// Set the index of the next entry in the available ring.
    ///
    /// # Arguments
    /// * `next_avail` - the index of the next available ring entry.
    pub fn set_next_avail(&mut self, next_avail: u16) {
        self.state.set_next_avail(next_avail);
    }

    /// Sets the index for the next descriptor in the used ring.
    ///
    /// # Arguments
    /// * `next_used` - the index of the next used ring entry.
    pub fn set_next_used(&mut self, next_used: u16) {
        self.state.set_next_used(next_used);
    }
}

impl<M: GuestAddressSpace> Queue<M, QueueState> {
    /// A consuming iterator over all available descriptor chain heads offered by the driver.
    pub fn iter(&mut self) -> Result<AvailIter<'_, M::T>, Error> {
        self.state.iter(self.mem.memory())
    }
}
