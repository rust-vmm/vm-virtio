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

//! Virtio queue API for backend device drivers to access virtio queues.

#![deny(missing_docs)]

use std::fmt::{self, Debug, Display};
use std::num::Wrapping;
use std::ops::{Deref, DerefMut};
use std::sync::atomic::Ordering;

use log::error;
use vm_memory::{GuestMemory, GuestMemoryError};

pub use self::chain::{DescriptorChain, DescriptorChainRwIter};
pub use self::descriptor::{Descriptor, VirtqUsedElem};
pub use self::queue::{AvailIter, Queue};
pub use self::queue_sync::QueueSync;
pub use self::state::QueueState;

pub mod defs;
#[cfg(any(test, feature = "test-utils"))]
pub mod mock;

mod chain;
mod descriptor;
mod queue;
mod queue_sync;
mod state;

/// Virtio Queue related errors.
#[derive(Debug)]
pub enum Error {
    /// Address overflow.
    AddressOverflow,
    /// Failed to access guest memory.
    GuestMemory(GuestMemoryError),
    /// Invalid indirect descriptor.
    InvalidIndirectDescriptor,
    /// Invalid indirect descriptor table.
    InvalidIndirectDescriptorTable,
    /// Invalid descriptor chain.
    InvalidChain,
    /// Invalid descriptor index.
    InvalidDescriptorIndex,
    /// Invalid max_size.
    InvalidMaxSize,
    /// Invalid Queue Size.
    InvalidSize,
    /// Invalid alignment of descriptor table address.
    InvalidDescTableAlign,
    /// Invalid alignment of available ring address.
    InvalidAvailRingAlign,
    /// Invalid alignment of used ring address.
    InvalidUsedRingAlign,
    /// Invalid available ring index.
    InvalidAvailRingIndex,
    /// The queue is not ready for operation.
    QueueNotReady,
}

impl Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Error::*;

        match self {
            AddressOverflow => write!(f, "address overflow"),
            GuestMemory(_) => write!(f, "error accessing guest memory"),
            InvalidChain => write!(f, "invalid descriptor chain"),
            InvalidIndirectDescriptor => write!(f, "invalid indirect descriptor"),
            InvalidIndirectDescriptorTable => write!(f, "invalid indirect descriptor table"),
            InvalidDescriptorIndex => write!(f, "invalid descriptor index"),
            InvalidMaxSize => write!(f, "invalid queue maximum size"),
            InvalidSize => write!(f, "invalid queue size"),
            InvalidDescTableAlign => write!(
                f,
                "virtio queue descriptor table breaks alignment constraints"
            ),
            InvalidAvailRingAlign => write!(
                f,
                "virtio queue available ring breaks alignment constraints"
            ),
            InvalidUsedRingAlign => {
                write!(f, "virtio queue used ring breaks alignment constraints")
            }
            InvalidAvailRingIndex => write!(
                f,
                "invalid available ring index (more descriptors to process than queue size)"
            ),
            QueueNotReady => write!(f, "trying to process requests on a queue that's not ready"),
        }
    }
}

impl std::error::Error for Error {}

/// Trait for objects returned by `QueueT::lock()`.
pub trait QueueGuard<'a> {
    /// Type for guard returned by `Self::lock()`.
    type G: DerefMut<Target = Queue>;
}

/// Trait to access and manipulate a virtio queue.
///
/// To optimize for performance, different implementations of the `QueueT` trait may be
/// provided for single-threaded context and multi-threaded context.
///
/// Using Higher-Rank Trait Bounds (HRTBs) to effectively define an associated type that has a
/// lifetime parameter, without tagging the `QueueT` trait with a lifetime as well.
pub trait QueueT: for<'a> QueueGuard<'a> {
    /// Construct an empty virtio queue state object with the given `max_size`.
    ///
    /// Returns an error if `max_size` is invalid.
    fn new(max_size: u16) -> Result<Self, Error>
    where
        Self: Sized;

    /// Check whether the queue configuration is valid.
    fn is_valid<M: GuestMemory>(&self, mem: &M) -> bool;

    /// Reset the queue to the initial state.
    fn reset(&mut self);

    /// Get an exclusive reference to the underlying `Queue` object.
    ///
    /// Logically this method will acquire the underlying lock protecting the `Queue` Object.
    /// The lock will be released when the returned object gets dropped.
    fn lock(&mut self) -> <Self as QueueGuard>::G;

    /// Get the maximum size of the virtio queue.
    fn max_size(&self) -> u16;

    /// Get the actual size configured by the guest.
    fn size(&self) -> u16;

    /// Configure the queue size for the virtio queue.
    fn set_size(&mut self, size: u16);

    /// Check whether the queue is ready to be processed.
    fn ready(&self) -> bool;

    /// Configure the queue to `ready for processing` state.
    fn set_ready(&mut self, ready: bool);

    /// Set the descriptor table address for the queue.
    ///
    /// The descriptor table address is 64-bit, the corresponding part will be updated if 'low'
    /// and/or `high` is `Some` and valid.
    fn set_desc_table_address(&mut self, low: Option<u32>, high: Option<u32>);

    /// Set the available ring address for the queue.
    ///
    /// The available ring address is 64-bit, the corresponding part will be updated if 'low'
    /// and/or `high` is `Some` and valid.
    fn set_avail_ring_address(&mut self, low: Option<u32>, high: Option<u32>);

    /// Set the used ring address for the queue.
    ///
    /// The used ring address is 64-bit, the corresponding part will be updated if 'low'
    /// and/or `high` is `Some` and valid.
    fn set_used_ring_address(&mut self, low: Option<u32>, high: Option<u32>);

    /// Enable/disable the VIRTIO_F_RING_EVENT_IDX feature for interrupt coalescing.
    fn set_event_idx(&mut self, enabled: bool);

    /// Read the `idx` field from the available ring.
    ///
    /// # Panics
    ///
    /// Panics if order is Release or AcqRel.
    fn avail_idx<M>(&self, mem: &M, order: Ordering) -> Result<Wrapping<u16>, Error>
    where
        M: GuestMemory + ?Sized;

    /// Read the `idx` field from the used ring.
    ///
    /// # Panics
    ///
    /// Panics if order is Release or AcqRel.
    fn used_idx<M: GuestMemory>(&self, mem: &M, order: Ordering) -> Result<Wrapping<u16>, Error>;

    /// Put a used descriptor head into the used ring.
    fn add_used<M: GuestMemory>(&mut self, mem: &M, head_index: u16, len: u32)
        -> Result<(), Error>;

    /// Enable notification events from the guest driver.
    ///
    /// Return true if one or more descriptors can be consumed from the available ring after
    /// notifications were enabled (and thus it's possible there will be no corresponding
    /// notification).
    fn enable_notification<M: GuestMemory>(&mut self, mem: &M) -> Result<bool, Error>;

    /// Disable notification events from the guest driver.
    fn disable_notification<M: GuestMemory>(&mut self, mem: &M) -> Result<(), Error>;

    /// Check whether a notification to the guest is needed.
    ///
    /// Please note this method has side effects: once it returns `true`, it considers the
    /// driver will actually be notified, remember the associated index in the used ring, and
    /// won't return `true` again until the driver updates `used_event` and/or the notification
    /// conditions hold once more.
    fn needs_notification<M: GuestMemory>(&mut self, mem: &M) -> Result<bool, Error>;

    /// Return the index of the next entry in the available ring.
    fn next_avail(&self) -> u16;

    /// Set the index of the next entry in the available ring.
    fn set_next_avail(&mut self, next_avail: u16);

    /// Return the index for the next descriptor in the used ring.
    fn next_used(&self) -> u16;

    /// Set the index for the next descriptor in the used ring.
    fn set_next_used(&mut self, next_used: u16);

    /// Return the address of the descriptor table.
    fn desc_table(&self) -> u64;

    /// Return the address of the available ring.
    fn avail_ring(&self) -> u64;

    /// Return the address of the used ring.
    fn used_ring(&self) -> u64;

    /// Checks whether `VIRTIO_F_RING_EVENT_IDX` is negotiated.
    ///
    /// This getter is only returning the correct value after the device passes the `FEATURES_OK`
    /// status.
    fn event_idx_enabled(&self) -> bool;

    /// Pop and return the next available descriptor chain, or `None` when there are no more
    /// descriptor chains available.
    ///
    /// This enables the consumption of available descriptor chains in a "one at a time"
    /// manner, without having to hold a borrow after the method returns.
    fn pop_descriptor_chain<M>(&mut self, mem: M) -> Option<DescriptorChain<M>>
    where
        M: Clone + Deref,
        M::Target: GuestMemory;
}

/// Trait to access and manipulate a Virtio queue that's known to be exclusively accessed
/// by a single execution thread.
pub trait QueueOwnedT: QueueT {
    /// Get a consuming iterator over all available descriptor chain heads offered by the driver.
    ///
    /// # Arguments
    /// * `mem` - the `GuestMemory` object that can be used to access the queue buffers.
    fn iter<M>(&mut self, mem: M) -> Result<AvailIter<'_, M>, Error>
    where
        M: Deref,
        M::Target: GuestMemory;

    /// Undo the last advancement of the next available index field by decrementing its
    /// value by one.
    fn go_to_previous_position(&mut self);
}
