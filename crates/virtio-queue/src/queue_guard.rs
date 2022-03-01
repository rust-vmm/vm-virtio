// Copyright (C) 2020-2021 Alibaba Cloud. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0 AND BSD-3-Clause

use std::num::Wrapping;
use std::ops::{Deref, DerefMut};
use std::sync::atomic::Ordering;

use vm_memory::GuestMemory;

use crate::{AvailIter, Error, QueueState, QueueStateT};

/// A guard object to exclusively access an `Queue` object.
///
/// The guard object holds an exclusive lock to the underlying `QueueState` object, with an
/// associated guest memory object. It helps to guarantee that the whole session is served
/// with the same guest memory object.
///
/// # Example
///
/// ```rust
/// use virtio_queue::{Queue, QueueState};
/// use vm_memory::{Bytes, GuestAddress, GuestAddressSpace, GuestMemoryMmap};
///
/// let m = GuestMemoryMmap::<()>::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap();
/// let mut queue = Queue::<&GuestMemoryMmap, QueueState>::new(&m, 1024);
/// let mut queue_guard = queue.lock_with_memory();
///
/// // First, the driver sets up the queue; this set up is done via writes on the bus (PCI, MMIO).
/// queue_guard.set_size(8);
/// queue_guard.set_desc_table_address(Some(0x1000), None);
/// queue_guard.set_avail_ring_address(Some(0x2000), None);
/// queue_guard.set_used_ring_address(Some(0x3000), None);
/// queue_guard.set_event_idx(true);
/// queue_guard.set_ready(true);
/// // The user should check if the queue is valid before starting to use it.
/// assert!(queue_guard.is_valid());
///
/// // Here the driver would add entries in the available ring and then update the `idx` field of
/// // the available ring (address = 0x2000 + 2).
/// m.write_obj(3, GuestAddress(0x2002));
///
/// loop {
///     queue_guard.disable_notification().unwrap();
///
///     // Consume entries from the available ring.
///     while let Some(chain) = queue_guard.iter().unwrap().next() {
///         // Process the descriptor chain, and then add an entry in the used ring and optionally
///         // notify the driver.
///         queue_guard.add_used(chain.head_index(), 0x100).unwrap();
///
///         if queue_guard.needs_notification().unwrap() {
///             // Here we would notify the driver it has new entries in the used ring to consume.
///         }
///     }
///     if !queue_guard.enable_notification().unwrap() {
///         break;
///     }
/// }
/// ```
pub struct QueueGuard<M, S> {
    state: S,
    mem: M,
}

impl<M, S> QueueGuard<M, S>
where
    M: Deref + Clone,
    M::Target: GuestMemory + Sized,
    S: DerefMut<Target = QueueState>,
{
    /// Create a new instance of `QueueGuard`.
    pub fn new(state: S, mem: M) -> Self {
        QueueGuard { state, mem }
    }

    /// Check whether the queue configuration is valid.
    pub fn is_valid(&self) -> bool {
        self.state.is_valid(self.mem.deref())
    }

    /// Reset the queue to the initial state.
    pub fn reset(&mut self) {
        self.state.reset()
    }

    /// Get the maximum size of the virtio queue.
    pub fn max_size(&self) -> u16 {
        self.state.max_size()
    }

    /// Configure the queue size for the virtio queue.
    pub fn set_size(&mut self, size: u16) {
        self.state.set_size(size);
    }

    /// Check whether the queue is ready to be processed.
    pub fn ready(&self) -> bool {
        self.state.ready()
    }

    /// Configure the queue to `ready for processing` state.
    pub fn set_ready(&mut self, ready: bool) {
        self.state.set_ready(ready)
    }

    /// Set the descriptor table address for the queue.
    ///
    /// The descriptor table address is 64-bit, the corresponding part will be updated if 'low'
    /// and/or `high` is `Some` and valid.
    pub fn set_desc_table_address(&mut self, low: Option<u32>, high: Option<u32>) {
        self.state.set_desc_table_address(low, high);
    }

    /// Set the available ring address for the queue.
    ///
    /// The available ring address is 64-bit, the corresponding part will be updated if 'low'
    /// and/or `high` is `Some` and valid.
    pub fn set_avail_ring_address(&mut self, low: Option<u32>, high: Option<u32>) {
        self.state.set_avail_ring_address(low, high);
    }

    /// Set the used ring address for the queue.
    ///
    /// The used ring address is 64-bit, the corresponding part will be updated if 'low'
    /// and/or `high` is `Some` and valid.
    pub fn set_used_ring_address(&mut self, low: Option<u32>, high: Option<u32>) {
        self.state.set_used_ring_address(low, high);
    }

    /// Enable/disable the VIRTIO_F_RING_EVENT_IDX feature for interrupt coalescing.
    pub fn set_event_idx(&mut self, enabled: bool) {
        self.state.set_event_idx(enabled)
    }

    /// Read the `idx` field from the available ring.
    pub fn avail_idx(&self, order: Ordering) -> Result<Wrapping<u16>, Error> {
        self.state.avail_idx(self.mem.deref(), order)
    }

    /// Read the `idx` field from the used ring.
    pub fn used_idx(&self, order: Ordering) -> Result<Wrapping<u16>, Error> {
        self.state.used_idx(self.mem.deref(), order)
    }

    /// Put a used descriptor head into the used ring.
    pub fn add_used(&mut self, head_index: u16, len: u32) -> Result<(), Error> {
        self.state.add_used(self.mem.deref(), head_index, len)
    }

    /// Enable notification events from the guest driver.
    ///
    /// Return true if one or more descriptors can be consumed from the available ring after
    /// notifications were enabled (and thus it's possible there will be no corresponding
    /// notification).
    pub fn enable_notification(&mut self) -> Result<bool, Error> {
        self.state.enable_notification(self.mem.deref())
    }

    /// Disable notification events from the guest driver.
    pub fn disable_notification(&mut self) -> Result<(), Error> {
        self.state.disable_notification(self.mem.deref())
    }

    /// Check whether a notification to the guest is needed.
    ///
    /// Please note this method has side effects: once it returns `true`, it considers the
    /// driver will actually be notified, remember the associated index in the used ring, and
    /// won't return `true` again until the driver updates `used_event` and/or the notification
    /// conditions hold once more.
    pub fn needs_notification(&mut self) -> Result<bool, Error> {
        self.state.needs_notification(self.mem.deref())
    }

    /// Return the index of the next entry in the available ring.
    pub fn next_avail(&self) -> u16 {
        self.state.next_avail()
    }

    /// Return the index of the next entry in the used ring.
    pub fn next_used(&self) -> u16 {
        self.state.next_used()
    }

    /// Set the index of the next entry in the available ring.
    pub fn set_next_avail(&mut self, next_avail: u16) {
        self.state.set_next_avail(next_avail);
    }

    /// Set the index of the next entry in the used ring.
    pub fn set_next_used(&mut self, next_used: u16) {
        self.state.set_next_used(next_used);
    }

    /// Get a consuming iterator over all available descriptor chain heads offered by the driver.
    pub fn iter(&mut self) -> Result<AvailIter<'_, M>, Error> {
        self.state.deref_mut().iter(self.mem.clone())
    }
}

#[cfg(test)]
mod tests {
    use crate::mock::MockSplitQueue;

    use crate::queue::tests::check_invalid_avail_idx;
    use vm_memory::{GuestAddress, GuestMemoryMmap};

    #[test]
    fn test_invalid_avail_idx() {
        let m = &GuestMemoryMmap::<()>::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap();
        let vq = &MockSplitQueue::new(m, 0x100);
        let mut q = vq.create_queue(m);
        let mut g = q.lock_with_memory();

        assert!(g.ready());
        assert_eq!(g.max_size(), 0x100);
        g.set_size(16);
        check_invalid_avail_idx(g.state, m, vq);
    }
}
