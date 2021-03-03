// Copyright (C) 2021 Alibaba Cloud. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0

use vm_memory::GuestAddress;

/// Trait to configure virtio queues.
pub trait QueueConfigT {
    /// Gets the virtio queue maximum size.
    fn max_size(&self) -> u16;

    /// Return the actual size of the queue, as the driver may not set up a
    /// queue as big as the device allows.
    fn actual_size(&self) -> u16;

    /// Get the actual size of the queue.
    fn queue_size(&self) -> u16;

    /// Set the actual size of the queue.
    fn set_queue_size(&mut self, size: u16);

    /// Get the address for the descriptor table.
    fn desc_table_address(&self) -> GuestAddress;

    /// Set the address for the descriptor table.
    fn set_desc_table_address(&mut self, addr: GuestAddress);

    /// Get the address for the available ring of split queue.
    fn avail_ring_address(&self) -> GuestAddress;

    /// Set the address for the available ring of split queue.
    fn set_avail_ring_address(&mut self, addr: GuestAddress);

    /// Get the address for the used ring of split queue.
    fn used_ring_address(&self) -> GuestAddress;

    /// Set the address for the used ring of split queue.
    fn set_used_ring_address(&mut self, addr: GuestAddress);

    /// Returns whether the VIRTIO_F_RING_EVENT_IDX feature has been enabled.
    fn event_idx(&self) -> bool;

    /// Enable/disable the VIRTIO_F_RING_EVENT_IDX feature.
    fn set_event_idx(&mut self, enabled: bool);

    /// Returns the ready flag for the queue.
    fn ready(&self) -> bool;

    /// Setup the queue to start processing requests.
    fn set_ready(&mut self, ready: bool);

    /// Reset the queue to a state that is acceptable for a device reset
    fn reset(&mut self);

    /// Check if the virtio queue configuration is valid.
    fn is_valid(&self) -> bool;
}
