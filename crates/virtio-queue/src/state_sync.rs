// Copyright (C) 2021 Alibaba Cloud. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0 AND BSD-3-Clause

use std::num::Wrapping;
use std::sync::atomic::Ordering;
use std::sync::{Arc, Mutex};

use vm_memory::GuestMemory;

use crate::{Error, QueueState, QueueStateGuard, QueueStateT};

/// Struct to maintain information and manipulate state of a virtio queue for multi-threaded
/// context.
#[derive(Clone, Debug)]
pub struct QueueStateSync {
    state: Arc<Mutex<QueueState>>,
}

impl QueueStateT for QueueStateSync {
    fn new(max_size: u16) -> Self {
        QueueStateSync {
            state: Arc::new(Mutex::new(QueueState::new(max_size))),
        }
    }

    fn is_valid<M: GuestMemory>(&self, mem: &M) -> bool {
        self.state.lock().unwrap().is_valid(mem)
    }

    fn reset(&mut self) {
        self.state.lock().unwrap().reset();
    }

    fn lock(&mut self) -> QueueStateGuard {
        QueueStateGuard::MutexGuard(self.state.lock().unwrap())
    }

    fn max_size(&self) -> u16 {
        self.state.lock().unwrap().max_size()
    }

    fn set_size(&mut self, size: u16) {
        self.state.lock().unwrap().set_size(size);
    }

    fn ready(&self) -> bool {
        self.state.lock().unwrap().ready
    }

    fn set_ready(&mut self, ready: bool) {
        self.state.lock().unwrap().set_ready(ready)
    }

    fn set_desc_table_address(&mut self, low: Option<u32>, high: Option<u32>) {
        self.state.lock().unwrap().set_desc_table_address(low, high);
    }

    fn set_avail_ring_address(&mut self, low: Option<u32>, high: Option<u32>) {
        self.state.lock().unwrap().set_avail_ring_address(low, high);
    }

    fn set_used_ring_address(&mut self, low: Option<u32>, high: Option<u32>) {
        self.state.lock().unwrap().set_used_ring_address(low, high);
    }

    fn set_event_idx(&mut self, enabled: bool) {
        self.state.lock().unwrap().set_event_idx(enabled);
    }

    fn avail_idx<M: GuestMemory>(&self, mem: &M, order: Ordering) -> Result<Wrapping<u16>, Error> {
        self.state.lock().unwrap().avail_idx(mem, order)
    }

    fn add_used<M: GuestMemory>(
        &mut self,
        mem: &M,
        head_index: u16,
        len: u32,
    ) -> Result<(), Error> {
        self.state.lock().unwrap().add_used(mem, head_index, len)
    }

    fn enable_notification<M: GuestMemory>(&mut self, mem: &M) -> Result<bool, Error> {
        self.state.lock().unwrap().enable_notification(mem)
    }

    fn disable_notification<M: GuestMemory>(&mut self, mem: &M) -> Result<(), Error> {
        self.state.lock().unwrap().disable_notification(mem)
    }

    fn needs_notification<M: GuestMemory>(&mut self, mem: &M) -> Result<bool, Error> {
        self.state.lock().unwrap().needs_notification(mem)
    }

    fn next_avail(&self) -> u16 {
        self.state.lock().unwrap().next_avail()
    }

    fn set_next_avail(&mut self, next_avail: u16) {
        self.state.lock().unwrap().set_next_avail(next_avail);
    }
}
