// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

use std::borrow::BorrowMut;
use std::cmp;
use std::result;
use std::sync::atomic::AtomicU8;
use std::sync::Arc;

use vm_memory::GuestAddressSpace;

use crate::device::{VirtioDevice, WithDriverSelect};
use crate::Queue;

/// An object that provides a common virtio device configuration representation. It is not part
/// of the main `vm-virtio` set of interfaces, but rather can be used as a helper object in
/// conjunction with the `WithVirtioConfig` trait (provided in the same module), to enable the
/// automatic implementation of other traits such as `VirtioDevice` and `WithDriverSelect`.
// Adding the `M` generic parameter that's also required by `VirtioDevice` for the time being.
// The various members have `pub` visibility until we determine whether it makes sense to drop
// this in favor of adding accessors.
pub struct VirtioConfig<M: GuestAddressSpace> {
    /// The set of features exposed by the device.
    pub device_features: u64,
    /// The set of features acknowledged by the driver.
    pub driver_features: u64,
    /// Index of the current device features page.
    pub device_features_select: u32,
    /// Index of the current driver acknowledgement device features page.
    pub driver_features_select: u32,
    /// Device status flags.
    pub device_status: u8,
    /// Index of the queue currently selected by the driver.
    pub queue_select: u16,
    /// Queues associated with the device.
    pub queues: Vec<Queue<M>>,
    /// Configuration space generation number.
    pub config_generation: u8,
    /// Contents of the device configuration space.
    pub config_space: Vec<u8>,
    /// Represents whether the device has been activated or not.
    pub device_activated: bool,
    /// Device interrupt status.
    pub interrupt_status: Arc<AtomicU8>,
}

impl<M: GuestAddressSpace> VirtioConfig<M> {
    /// Build and initialize a `VirtioConfig` object.
    pub fn new(device_features: u64, queues: Vec<Queue<M>>, config_space: Vec<u8>) -> Self {
        VirtioConfig {
            device_features,
            driver_features: 0,
            device_features_select: 0,
            driver_features_select: 0,
            device_status: 0,
            queue_select: 0,
            queues,
            config_generation: 0,
            config_space,
            device_activated: false,
            interrupt_status: Arc::new(AtomicU8::new(0)),
        }
    }

    /// Helper method which checks whether all queues are valid.
    // TODO: This method assumes all queues are intended for use. We probably need to tweak it
    // for devices that support multiple queues which might not all be configured/activated by
    // the driver.
    pub fn queues_valid(&self) -> bool {
        self.queues.iter().all(Queue::is_valid)
    }
}

/// Helper trait that can be implemented for objects which represent virtio devices. Together
/// with `VirtioDeviceActions`, it enables an automatic `VirtioDevice` implementation for objects
/// that also implement `BorrowMut<VirtioConfig>`.
pub trait VirtioDeviceType {
    /// Return the virtio device type.
    fn device_type(&self) -> u32;
}

/// Helper trait that can be implemented for objects which represent virtio devices. Together
/// with `VirtioDeviceType`, it enables an automatic `VirtioDevice` implementation for objects
/// that also implement `BorrowMut<VirtioConfig>`.
pub trait VirtioDeviceActions {
    /// Type of the error that can be returned by `activate` and `reset`.
    type E;

    /// Invoke the logic associated with activating this device.
    fn activate(&mut self) -> result::Result<(), Self::E>;

    /// Invoke the logic associated with resetting this device.
    fn reset(&mut self) -> result::Result<(), Self::E>;
}

// We can automatically implement the `VirtioDevice` trait for objects that only explicitly
// implement `WithVirtioConfig` and `WithDeviceOps`.
impl<M, T> VirtioDevice<M> for T
where
    M: GuestAddressSpace + 'static,
    T: VirtioDeviceType + VirtioDeviceActions + BorrowMut<VirtioConfig<M>>,
{
    type E = <Self as VirtioDeviceActions>::E;

    fn device_type(&self) -> u32 {
        // Avoid infinite recursion.
        <Self as VirtioDeviceType>::device_type(self)
    }

    fn num_queues(&self) -> u16 {
        // It's invalid for the number of queues to exceed `u16::MAX`.
        self.borrow().queues.len() as u16
    }

    fn queue(&self, index: u16) -> Option<&Queue<M>> {
        self.borrow().queues.get(usize::from(index))
    }

    fn queue_mut(&mut self, index: u16) -> Option<&mut Queue<M>> {
        self.borrow_mut().queues.get_mut(usize::from(index))
    }

    fn device_features(&self) -> u64 {
        self.borrow().device_features
    }

    fn driver_features(&self) -> u64 {
        self.borrow().driver_features
    }

    fn set_driver_features(&mut self, page: u32, value: u32) {
        let features = self.borrow().driver_features;
        let v = u64::from(value);
        self.borrow_mut().driver_features = match page {
            0 => ((features >> 32) << 32) + v,
            1 => ((features << 32) >> 32) + (v << 32),
            // Accessing an unknown page has no effect.
            _ => features,
        }
    }

    fn device_status(&self) -> u8 {
        self.borrow().device_status
    }

    fn set_device_status(&mut self, status: u8) {
        self.borrow_mut().device_status = status;
    }

    fn activate(&mut self) -> Result<(), Self::E> {
        <Self as VirtioDeviceActions>::activate(self)
    }

    fn reset(&mut self) -> Result<(), Self::E> {
        <Self as VirtioDeviceActions>::reset(self)
    }

    fn interrupt_status(&self) -> &Arc<AtomicU8> {
        &self.borrow().interrupt_status
    }

    fn config_generation(&self) -> u8 {
        self.borrow().config_generation
    }

    fn read_config(&self, offset: usize, data: &mut [u8]) {
        let config_space = &self.borrow().config_space;
        let config_len = config_space.len();
        if offset >= config_len {
            error!("Failed to read from config space");
            return;
        }

        // TODO: Are partial reads ok?
        let end = cmp::min(offset.saturating_add(data.len()), config_len);
        let read_len = end - offset;
        // Cannot fail because the lengths are identical and we do bounds checking beforehand.
        data[..read_len].copy_from_slice(&config_space[offset..end])
    }

    fn write_config(&mut self, offset: usize, data: &[u8]) {
        let config_space = &mut self.borrow_mut().config_space;
        let config_len = config_space.len();
        if offset >= config_len {
            error!("Failed to write to config space");
            return;
        }

        // TODO: Are partial writes ok?
        let end = cmp::min(offset.saturating_add(data.len()), config_len);
        let write_len = end - offset;
        // Cannot fail because the lengths are identical and we do bounds checking beforehand.
        config_space[offset..end].copy_from_slice(&data[..write_len]);
    }
}

impl<M, T> WithDriverSelect<M> for T
where
    // Added a `static bound here while `M` is around to simplify dealing with lifetimes.
    M: GuestAddressSpace + 'static,
    T: BorrowMut<VirtioConfig<M>> + VirtioDevice<M>,
{
    fn queue_select(&self) -> u16 {
        self.borrow().queue_select
    }

    fn set_queue_select(&mut self, value: u16) {
        self.borrow_mut().queue_select = value
    }

    fn device_features_select(&self) -> u32 {
        self.borrow().device_features_select
    }

    fn set_device_features_select(&mut self, value: u32) {
        self.borrow_mut().device_features_select = value;
    }

    fn driver_features_select(&self) -> u32 {
        self.borrow().driver_features_select
    }

    fn set_driver_features_select(&mut self, value: u32) {
        self.borrow_mut().driver_features_select = value;
    }
}
