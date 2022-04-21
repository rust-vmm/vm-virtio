// Copyright 2022 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

use std::num::Wrapping;

use serde::{Deserialize, Serialize};
use versionize::{VersionMap, Versionize, VersionizeResult};
use versionize_derive::Versionize;
use virtio_queue::QueueState;
use vm_memory::GuestAddress;

/// Wrapper over a `QueueState` that has serialization capabilities.
#[derive(Clone, Debug, Deserialize, PartialEq, Serialize, Versionize)]
pub struct QueueStateSer {
    /// The maximum size in elements offered by the device.
    pub max_size: u16,
    /// Tail position of the available ring.
    pub next_avail: u16,
    /// Head position of the used ring.
    pub next_used: u16,
    /// VIRTIO_F_RING_EVENT_IDX negotiated.
    pub event_idx_enabled: bool,
    /// The number of descriptor chains placed in the used ring via `add_used`
    /// since the last time `needs_notification` was called on the associated queue.
    pub num_added: u16,
    /// The queue size in elements the driver selected.
    pub size: u16,
    /// Indicates if the queue finished with the configuration.
    pub ready: bool,
    /// Guest physical address of the descriptor table.
    pub desc_table: u64,
    /// Guest physical address of the available ring.
    pub avail_ring: u64,
    /// Guest physical address of the used ring.
    pub used_ring: u64,
}

// The following `From` implementations can be used to convert from a `QueueStateSer` to the
// `QueueState` from the base crate and vice versa.
// WARNING: They don't check for any invalid data, that would otherwise be checked when initializing
// a queue object from scratch (for example setting a queue size greater than its max possible
// size). The problem with the current `QueueState` implementation is that it can be used as the
// queue object itself. `QueueState`'s fields are public, which allows the user to set up and use an
// invalid queue. Once we fix https://github.com/rust-vmm/vm-virtio/issues/143, `QueueState` will be
// renamed to `Queue`, its fields will no longer be public, and `QueueState` will consist of the
// actual state. This way we can also check against any invalid data when trying to get a `Queue`
// from the state object.
// Nevertheless, we don't make any assumptions in the virtio-queue code about the queue's state that
// would otherwise result in a panic, when initialized with random data, so from this point of view
// these conversions are safe to use.
impl From<&QueueStateSer> for QueueState {
    fn from(state: &QueueStateSer) -> Self {
        QueueState {
            max_size: state.max_size,
            next_avail: Wrapping(state.next_avail),
            next_used: Wrapping(state.next_used),
            event_idx_enabled: state.event_idx_enabled,
            num_added: Wrapping(state.num_added),
            size: state.size,
            ready: state.ready,
            desc_table: GuestAddress(state.desc_table),
            avail_ring: GuestAddress(state.avail_ring),
            used_ring: GuestAddress(state.used_ring),
        }
    }
}

impl From<&QueueState> for QueueStateSer {
    fn from(state: &QueueState) -> Self {
        QueueStateSer {
            max_size: state.max_size,
            next_avail: state.next_avail.0,
            next_used: state.next_used.0,
            event_idx_enabled: state.event_idx_enabled,
            num_added: state.num_added.0,
            size: state.size,
            ready: state.ready,
            desc_table: state.desc_table.0,
            avail_ring: state.avail_ring.0,
            used_ring: state.used_ring.0,
        }
    }
}

impl Default for QueueStateSer {
    fn default() -> Self {
        QueueStateSer::from(&QueueState::default())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_state_ser() {
        const SOME_VALUE: u16 = 16;

        let state = QueueState {
            max_size: SOME_VALUE * 2,
            next_avail: Wrapping(SOME_VALUE - 1),
            next_used: Wrapping(SOME_VALUE + 1),
            event_idx_enabled: false,
            num_added: Wrapping(0),
            size: SOME_VALUE,
            ready: true,
            desc_table: GuestAddress(SOME_VALUE as u64),
            avail_ring: GuestAddress(SOME_VALUE as u64 * 2),
            used_ring: GuestAddress(SOME_VALUE as u64 * 4),
        };

        let ser_state = QueueStateSer::from(&state);
        let state_from_ser = QueueState::from(&ser_state);

        // Check that the old and the new state are identical when using the intermediate
        // `QueueStateSer` object.
        assert_eq!(state, state_from_ser);

        // Test the `Default` implementation of `QueueStateSer`.
        let default_queue_state_ser = QueueStateSer::default();
        assert_eq!(
            QueueState::from(&default_queue_state_ser),
            QueueState::default()
        );
    }
}
