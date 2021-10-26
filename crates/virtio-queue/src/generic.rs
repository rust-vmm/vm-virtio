// Copyright 2021 Red Hat, Inc.
//
// SPDX-License-Identifier: Apache-2.0 AND BSD-3-Clause

use std::num::Wrapping;
use std::ops::DerefMut;

use crate::{Error, Queue, QueueGuard, QueueState, QueueSync};
use std::sync::atomic::Ordering;
use std::sync::{Arc, Mutex, MutexGuard};
use vm_memory::GuestAddressSpace;

/// Lifetime-generic guard associated to a QueueStateT. In practice,
/// instead of having a `QueueStateT::Guard<'g>` generic associated type,
/// you have to write `<QueueStateT::Guard as QueueStateGuard<'g>>::Out`.
pub(crate) trait QueueStateGuard<'g> {
    /// Type of the guard passed to the `with` method.
    type Out: 'g + DerefMut<Target = QueueState>;
}

pub(crate) trait QueueT<M: GuestAddressSpace> {
    /// Lifetime-generic guard. Usually this is just `Self`, and implementors
    /// of `QueueT` also implement `QueueStateGuard`.
    type Guard: for<'g> QueueStateGuard<'g>;

    fn construct(mem: M, state: QueueState) -> Self;
    fn with<
        'a,
        'g,
        U,
        F: FnOnce(QueueGuard<M::T, <Self::Guard as QueueStateGuard<'g>>::Out>) -> U,
    >(
        &'a mut self,
        f: F,
    ) -> U
    where
        'a: 'g;

    /// Check whether the queue configuration is valid.
    fn is_valid(&mut self) -> bool {
        self.with(|qstate| qstate.is_valid())
    }

    /// Reset the queue to the initial state.
    fn reset(&mut self) {
        self.with(|mut qstate| qstate.reset())
    }

    /// Get the maximum size of the virtio queue.
    fn max_size(&mut self) -> u16 {
        self.with(|qstate| qstate.max_size())
    }

    /// Configure the queue size for the virtio queue.
    ///
    /// The `size` should power of two and less than or equal to value reported by `max_size()`,
    /// otherwise it will panic.
    fn set_size(&mut self, size: u16) {
        self.with(|mut qstate| qstate.set_size(size))
    }

    /// Check whether the queue is ready to be processed.
    fn ready(&mut self) -> bool {
        self.with(|qstate| qstate.ready())
    }

    /// Configure the queue to ready for processing.
    fn set_ready(&mut self, ready: bool) {
        self.with(|mut qstate| qstate.set_ready(ready))
    }

    /// Set descriptor table address for the queue.
    ///
    /// The descriptor table address is 64-bit, the corresponding part will be updated if 'low'
    /// and/or `high` is valid.
    fn set_desc_table_address(&mut self, low: Option<u32>, high: Option<u32>) {
        self.with(|mut qstate| qstate.set_desc_table_address(low, high))
    }

    /// Set available ring address for the queue.
    ///
    /// The available ring address is 64-bit, the corresponding part will be updated if 'low'
    /// and/or `high` is valid.
    fn set_avail_ring_address(&mut self, low: Option<u32>, high: Option<u32>) {
        self.with(|mut qstate| qstate.set_avail_ring_address(low, high))
    }

    /// Set used ring address for the queue.
    ///
    /// The used ring address is 64-bit, the corresponding part will be updated if 'low'
    /// and/or `high` is valid.
    fn set_used_ring_address(&mut self, low: Option<u32>, high: Option<u32>) {
        self.with(|mut qstate| qstate.set_used_ring_address(low, high))
    }

    /// Enable/disable the VIRTIO_F_RING_EVENT_IDX feature for interrupt coalescing.
    fn set_event_idx(&mut self, enabled: bool) {
        self.with(|mut qstate| qstate.set_event_idx(enabled))
    }

    /// Read the `idx` field from the available ring.
    fn avail_idx(&mut self, order: Ordering) -> Result<Wrapping<u16>, Error> {
        self.with(|qstate| qstate.avail_idx(order))
    }

    /// Put a used descriptor head into the used ring.
    fn add_used(&mut self, head_index: u16, len: u32) -> Result<(), Error> {
        self.with(|mut qstate| qstate.add_used(head_index, len))
    }

    /// Enable notification events from the guest driver.
    ///
    /// Return true if one or more descriptors can be consumed from the available ring after
    /// notifications were enabled (and thus it's possible there will be no corresponding
    /// notification).
    fn enable_notification(&mut self) -> Result<bool, Error> {
        self.with(|mut qstate| qstate.enable_notification())
    }

    /// Disable notification events from the guest driver.
    fn disable_notification(&mut self) -> Result<(), Error> {
        self.with(|mut qstate| qstate.disable_notification())
    }

    /// Check whether a notification to the guest is needed.
    ///
    /// Please note this method has side effects: once it returns `true`, it considers the
    /// driver will actually be notified, remember the associated index in the used ring, and
    /// won't return `true` again until the driver updates `used_event` and/or the notification
    /// conditions hold once more.
    fn needs_notification(&mut self) -> Result<bool, Error> {
        self.with(|mut qstate| qstate.needs_notification())
    }

    /// Return the index for the next descriptor in the available ring.
    fn next_avail(&mut self) -> u16 {
        self.with(|qstate| qstate.next_avail())
    }

    /// Set the index for the next descriptor in the available ring.
    fn set_next_avail(&mut self, next_avail: u16) {
        self.with(|mut qstate| qstate.set_next_avail(next_avail))
    }
}

impl<'g, M: GuestAddressSpace> QueueStateGuard<'g> for Queue<M> {
    type Out = &'g mut QueueState;
}

impl<M: GuestAddressSpace> QueueT<M> for Queue<M> {
    type Guard = Self;

    fn construct(mem: M, state: QueueState) -> Self {
        Queue { mem, state }
    }
    fn with<
        'a,
        'g,
        U,
        F: FnOnce(QueueGuard<M::T, <Self::Guard as QueueStateGuard<'g>>::Out>) -> U,
    >(
        &'a mut self,
        f: F,
    ) -> U
    where
        'a: 'g,
    {
        f(self.acquire())
    }
}

impl<'g, M: GuestAddressSpace> QueueStateGuard<'g> for QueueSync<M> {
    type Out = MutexGuard<'g, QueueState>;
}

impl<M: GuestAddressSpace> QueueT<M> for QueueSync<M> {
    type Guard = Self;

    fn construct(mem: M, state: QueueState) -> Self {
        QueueSync {
            mem,
            state: Arc::new(Mutex::new(state)),
        }
    }
    fn with<
        'a,
        'g,
        U,
        F: FnOnce(QueueGuard<M::T, <Self::Guard as QueueStateGuard<'g>>::Out>) -> U,
    >(
        &'a mut self,
        f: F,
    ) -> U
    where
        'a: 'g,
    {
        f(self.lock())
    }
}
