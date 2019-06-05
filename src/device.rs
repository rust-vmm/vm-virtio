// Copyright 2018 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

use super::*;
use vm_memory::GuestMemory;
use vmm_sys_util::EventFd;

/// Trait for virtio devices to inject interrupts into the guest.
pub trait VirtioDeviceInterrupt: Sized + Send {
    /// Inject the specified interrupt into the guest.
    fn trigger(&mut self, interrupt_id: u32) -> std::io::Error;
}

/// Struct to encapsulate information for a single virtio queue.
pub struct VirtioDeviceQueue<'a, M: GuestMemory> {
    /// Virtio queue.
    pub queue: Queue<'a, M>,
    /// Eventfd for queue notification.
    pub queue_evt: EventFd,
    /// Id of the interrupt source to inject into the guest.
    pub interrupt_id: u32,
}

/// Configuration information passed to VirtioDevice::activate().
pub struct VirtioDeviceConfig<'a, M: GuestMemory, I: VirtioDeviceInterrupt> {
    /// Object to access guest physical memory.
    pub mem: M,
    /// Virtio queues for the virtio device.
    pub queues: Vec<VirtioDeviceQueue<'a, M>>,
    /// Interrupt controller to inject interrupt into the guest.
    pub intr_controller: I,
}

impl<'a, M, I> VirtioDeviceConfig<'a, M, I>
where
    M: GuestMemory,
    I: VirtioDeviceInterrupt,
{
    /// Inject the specified interrupt into the guest.
    pub fn trigger_intr(&mut self, interrupt_id: u32) -> std::io::Error {
        self.intr_controller.trigger(interrupt_id)
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
pub trait VirtioDevice: Send {
    /// Associated guest memory
    type M: GuestMemory;

    /// Associated type to inject interrupt into the guest.
    type I: VirtioDeviceInterrupt;

    /// The virtio device type.
    fn device_type(&self) -> u32;

    /// The maximum size of each queue that this device supports.
    fn queue_max_sizes(&self) -> &[u16];

    /// Get the number of interrupts required.
    fn interrupt_count(&self) -> u32;

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

    /// Activates this device for real usage.
    fn activate(&mut self, config: VirtioDeviceConfig<Self::M, Self::I>) -> ActivateResult;

    /// Optionally deactivates this device and returns ownership of the guest memory map, interrupt
    /// event, and queue events.
    fn reset(&mut self) -> Option<VirtioDeviceConfig<Self::M, Self::I>> {
        None
    }
}
