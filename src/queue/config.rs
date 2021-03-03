// Copyright (C) 2021 Alibaba Cloud. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0

use vm_memory::{GuestAddress, GuestAddressSpace};

use super::{QueueSinker, QueueSource};

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

/// A `QueueConfigT` implementation for split queue source and sinker.
#[derive(Clone)]
pub struct QueueConfig<M: GuestAddressSpace> {
    max_size: u16,
    source: QueueSource<M>,
    sinker: QueueSinker<M>,
}

impl<M: GuestAddressSpace> QueueConfig<M> {
    /// Create a new `QueueConfig` instance.
    pub fn new(max_size: u16, source: QueueSource<M>, sinker: QueueSinker<M>) -> Self {
        QueueConfig {
            max_size,
            source,
            sinker,
        }
    }

    /// Clone the queue source.
    pub fn clone_source(&self) -> QueueSource<M> {
        self.source.clone()
    }

    /// Clone the queue sinker.
    pub fn clone_sinker(&self) -> QueueSinker<M> {
        self.sinker.clone()
    }
}

impl<M: GuestAddressSpace> QueueConfigT for QueueConfig<M> {
    fn max_size(&self) -> u16 {
        self.max_size
    }

    fn actual_size(&self) -> u16 {
        self.source.0.lock().unwrap().actual_size()
    }

    fn queue_size(&self) -> u16 {
        self.source.0.lock().unwrap().queue_size()
    }

    fn set_queue_size(&mut self, size: u16) {
        self.source.0.lock().unwrap().set_queue_size(size);
        self.sinker.0.lock().unwrap().set_queue_size(size);
    }

    fn desc_table_address(&self) -> GuestAddress {
        self.source.0.lock().unwrap().desc_table_address()
    }

    fn set_desc_table_address(&mut self, addr: GuestAddress) {
        self.source.0.lock().unwrap().set_desc_table_address(addr);
        self.sinker.0.lock().unwrap().set_desc_table_address(addr);
    }

    fn avail_ring_address(&self) -> GuestAddress {
        self.source.0.lock().unwrap().avail_ring_address()
    }

    fn set_avail_ring_address(&mut self, addr: GuestAddress) {
        self.source.0.lock().unwrap().set_avail_ring_address(addr);
        self.sinker.0.lock().unwrap().set_avail_ring_address(addr);
    }

    fn used_ring_address(&self) -> GuestAddress {
        self.sinker.0.lock().unwrap().used_ring_address()
    }

    fn set_used_ring_address(&mut self, addr: GuestAddress) {
        self.source.0.lock().unwrap().set_used_ring_address(addr);
        self.sinker.0.lock().unwrap().set_used_ring_address(addr);
    }

    fn event_idx(&self) -> bool {
        self.source.0.lock().unwrap().event_idx()
    }

    fn set_event_idx(&mut self, enabled: bool) {
        self.source.0.lock().unwrap().set_event_idx(enabled);
        self.sinker.0.lock().unwrap().set_event_idx(enabled)
    }

    fn ready(&self) -> bool {
        self.source.0.lock().unwrap().ready()
    }

    fn set_ready(&mut self, ready: bool) {
        self.source.0.lock().unwrap().set_ready(ready);
        self.sinker.0.lock().unwrap().set_ready(ready);
    }

    fn reset(&mut self) {
        self.source.0.lock().unwrap().reset();
        self.sinker.0.lock().unwrap().reset();
    }

    fn is_valid(&self) -> bool {
        let source_valid = self.source.0.lock().unwrap().is_valid();

        source_valid && self.sinker.0.lock().unwrap().is_valid()
    }
}
