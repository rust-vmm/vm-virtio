// Copyright 2018 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

use super::queue::Queue;
use super::*;
use std::sync::Arc;
use vm_device::interrupt::{InterruptIndex, InterruptSourceGroup, InterruptSourceType};
use vm_device::resources::DeviceResourceRequest;
use vm_memory::GuestMemory;
use vmm_sys_util::eventfd::EventFd;

/// Data struct to manage an virtio queue.
pub struct VirtioQueueConfig<'a, M: GuestMemory> {
    /// A virtque.
    pub queue: Queue<'a, M>,

    /// And associated event notification fd.
    pub queue_evt: EventFd,
}

/// Configuration information for an virtio device.
///
/// The ownership of an virtio device configuration object will be moved into the VirtioDevice
/// object when VirtioDevice::activate() method gets called, and it should be returned back
/// if VirtioDevice::activate() fails or when VirtioDevice::reset() gets called.
pub struct VirtioDeviceConfig<'a, M: GuestMemory> {
    /// Memory object to access the guest memory.
    pub mem: M,

    /// Virtqueues of the virtio device.
    pub queues: Vec<VirtioQueueConfig<'a, M>>,

    /// A group of interrupts to notify the guest for queue events.
    pub intr_group: Arc<Box<dyn InterruptSourceGroup>>,
}

impl<'a, M> VirtioDeviceConfig<'a, M>
where
    M: GuestMemory,
{
    /// Constructs an virtio device configuration object.
    pub fn new(
        mem: M,
        queues: Vec<VirtioQueueConfig<'a, M>>,
        intr_group: Arc<Box<dyn InterruptSourceGroup>>,
    ) -> Self {
        VirtioDeviceConfig {
            mem,
            queues,
            intr_group,
        }
    }

    /// Trigger an interrupt for a specific event source.
    pub fn trigger(&self, index: u32, flags: u32) -> Result<(), std::io::Error> {
        match self.intr_group.get_type() {
            InterruptSourceType::LegacyIrq => self.intr_group.trigger(0, flags),
            InterruptSourceType::MsiIrq | InterruptSourceType::VfioMsiIrq(_, _) => {
                self.intr_group.trigger(index, 0)
            }
        }
    }

    /// Get all irqfds associated with vritio queues.
    pub fn get_vring_irqfds(&self) -> Vec<&EventFd> {
        match self.intr_group.get_type() {
            InterruptSourceType::LegacyIrq => {
                let irqfd = self.intr_group.get_irqfd(0).unwrap();
                vec![irqfd; 1]
            }
            InterruptSourceType::MsiIrq | InterruptSourceType::VfioMsiIrq(_, _) => {
                //Skip the first irqfd which is for device configuration change events.
                let intr_len = self.intr_group.len() as usize;
                let mut irqfds = Vec::with_capacity(intr_len - 1);
                for index in 1..intr_len {
                    irqfds.push(self.intr_group.get_irqfd(index as InterruptIndex).unwrap());
                }
                irqfds
            }
        }
    }
}

/// Trait for virtio devices to be driven by a virtio transport.
///
/// The lifecycle of a virtio device is to be moved to a virtio transport, which will then query
/// the device. Once the guest driver has configured the device,
/// `[VirtioDevice::activate`](trait.VirtioDevice.html#method.activate)` will be
/// called and all the events, memory, and queues for device operation will be moved into the
/// device. Optionally, a virtio device can implement device reset in which it returns said
/// resources and resets its internal state.
pub trait VirtioDevice<M: GuestMemory>: Send {
    /// Associated guest memory
    type M: GuestMemory;

    /// The virtio device type.
    fn device_type(&self) -> u32;

    /// The maximum size of each queue that this device supports.
    fn queue_max_sizes(&self) -> &[u16];

    /// The set of feature bits shifted by `page * 32`.
    fn features(&self, page: u32) -> u32 {
        let _ = page;
        0
    }

    /// Acknowledges that this set of features should be enabled.
    fn ack_features(&mut self, page: u32, value: u32);

    /// Reads this device configuration space at `offset`.
    fn read_config(&self, offset: u64, data: &mut [u8]);

    /// Writes to this device configuration space at `offset`.
    fn write_config(&mut self, offset: u64, data: &[u8]);

    /// Returns the resource requirements of the virtio device.
    fn get_resource_requirements(&self, requests: &mut Vec<DeviceResourceRequest>);

    /// Activates this device for real usage.
    /// The ownership of the VirtioDeviceConfig object moves into the VirtioDevice object if
    /// activate succeeds, otherwise it should return the ownership back.
    fn activate(&mut self, config: VirtioDeviceConfig<M>) -> ActivateResult<VirtioDeviceConfig<M>>;

    /// Optional method to deactivate the device and return ownership of the VirtioDeviceConfig
    /// object.
    fn reset(&mut self) -> Option<VirtioDeviceConfig<M>> {
        None
    }
}
