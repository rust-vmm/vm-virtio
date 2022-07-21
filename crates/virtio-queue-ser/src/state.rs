// Copyright 2022 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause
use serde::{Deserialize, Serialize};
use versionize::{VersionMap, Versionize, VersionizeResult};
use versionize_derive::Versionize;
use virtio_queue::QueueState;

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
impl From<&QueueStateSer> for QueueState {
    fn from(state: &QueueStateSer) -> Self {
        QueueState {
            max_size: state.max_size,
            next_avail: state.next_avail,
            next_used: state.next_used,
            event_idx_enabled: state.event_idx_enabled,
            size: state.size,
            ready: state.ready,
            desc_table: state.desc_table,
            avail_ring: state.avail_ring,
            used_ring: state.used_ring,
        }
    }
}

impl From<&QueueState> for QueueStateSer {
    fn from(state: &QueueState) -> Self {
        QueueStateSer {
            max_size: state.max_size,
            next_avail: state.next_avail,
            next_used: state.next_used,
            event_idx_enabled: state.event_idx_enabled,
            size: state.size,
            ready: state.ready,
            desc_table: state.desc_table,
            avail_ring: state.avail_ring,
            used_ring: state.used_ring,
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
    use std::convert::TryFrom;
    use virtio_queue::{Error, Queue};

    #[test]
    fn test_state_ser() {
        const SOME_VALUE: u16 = 16;

        let state = QueueState {
            max_size: SOME_VALUE * 2,
            next_avail: SOME_VALUE - 1,
            next_used: SOME_VALUE + 1,
            event_idx_enabled: false,
            size: SOME_VALUE,
            ready: true,
            desc_table: SOME_VALUE as u64,
            avail_ring: SOME_VALUE as u64 * 2,
            used_ring: SOME_VALUE as u64 * 4,
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

    #[test]
    fn test_ser_with_len_zero() {
        // This is a regression test that tests that a queue where the size is set to 0 does not
        // cause any problems when poping the descriptor chain.
        let queue_ser = QueueStateSer {
            max_size: 16,
            next_avail: 0,
            next_used: 0,
            event_idx_enabled: false,
            size: 0,
            ready: true,
            desc_table: 0,
            avail_ring: 256,
            used_ring: 276,
        };

        let queue_state = QueueState::from(&queue_ser);
        let err = Queue::try_from(queue_state).unwrap_err();
        assert_eq!(err, Error::InvalidSize);
    }
}
