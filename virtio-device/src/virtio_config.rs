// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

use std::borrow::BorrowMut;
use std::cmp;
use std::result;
use std::sync::atomic::AtomicU8;
use std::sync::Arc;

use log::error;

use crate::status::{ACKNOWLEDGE, DRIVER, FEATURES_OK};
use crate::{VirtioDevice, WithDriverSelect};
use virtio_queue::{Queue, QueueT};

/// An object that provides a common virtio device configuration representation. It is not part
/// of the main `vm-virtio` set of interfaces, but rather can be used as a helper object in
/// conjunction with the `WithVirtioConfig` trait (provided in the same module), to enable the
/// automatic implementation of other traits such as `VirtioDevice` and `WithDriverSelect`.
// Adding the `M` generic parameter that's also required by `VirtioDevice` for the time being.
// The various members have `pub` visibility until we determine whether it makes sense to drop
// this in favor of adding accessors.
#[derive(Debug)]
pub struct VirtioConfig<Q: QueueT> {
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
    pub queues: Vec<Q>,
    /// Configuration space generation number.
    pub config_generation: u8,
    /// Contents of the device configuration space.
    pub config_space: Vec<u8>,
    /// Represents whether the device has been activated or not.
    pub device_activated: bool,
    /// Device interrupt status.
    pub interrupt_status: Arc<AtomicU8>,
}

impl<Q: QueueT> VirtioConfig<Q> {
    /// Build and initialize a `VirtioConfig` object.
    pub fn new(device_features: u64, queues: Vec<Q>, config_space: Vec<u8>) -> Self {
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
pub trait VirtioDeviceActions: BorrowMut<VirtioConfig<Queue>> {
    /// Type of the error that can be returned by `activate` and `reset`.
    type E;

    /// Invoke the logic associated with activating this device.
    fn activate(&mut self) -> result::Result<(), Self::E>;

    /// Invoke the logic associated with resetting this device.
    fn reset(&mut self) -> result::Result<(), Self::E>;

    /// Invoke the logic associated with reading from the device configuration space.
    ///
    /// A default implementation is provided as we cannot expect all backends to implement
    /// this function.
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

    /// Invoke the logic associated with writing to the device configuration space.
    ///
    /// A default implementation is provided as we cannot expect all backends to implement
    /// this function.
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

    /// Invoke the logic associated with negotiating the driver features.
    ///
    /// A default implementation is provided as we cannot expect all backends to implement
    /// this function.
    fn negotiate_driver_features(&mut self) {}

    /// Invoke the logic associated with the device interrupt status.
    ///
    /// A default implementation is provided as we cannot expect all backends to implement
    /// this function.
    fn interrupt_status(&self) -> &Arc<AtomicU8> {
        &self.borrow().interrupt_status
    }
}

// We can automatically implement the `VirtioDevice` trait for objects that only explicitly
// implement `WithVirtioConfig` and `WithDeviceOps`.
impl<T> VirtioDevice for T
where
    T: VirtioDeviceType + VirtioDeviceActions + BorrowMut<VirtioConfig<Queue>>,
{
    type E = <Self as VirtioDeviceActions>::E;
    type Q = Queue;

    fn device_type(&self) -> u32 {
        // Avoid infinite recursion.
        <Self as VirtioDeviceType>::device_type(self)
    }

    fn num_queues(&self) -> u16 {
        // It's invalid for the number of queues to exceed `u16::MAX`.
        self.borrow().queues.len() as u16
    }

    fn queue(&self, index: u16) -> Option<&Queue> {
        self.borrow().queues.get(usize::from(index))
    }

    fn queue_mut(&mut self, index: u16) -> Option<&mut Queue> {
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
        if self.borrow_mut().device_status == (ACKNOWLEDGE | DRIVER | FEATURES_OK) {
            <Self as VirtioDeviceActions>::negotiate_driver_features(self);
        }
    }

    fn activate(&mut self) -> Result<(), Self::E> {
        <Self as VirtioDeviceActions>::activate(self)
    }

    fn reset(&mut self) -> Result<(), Self::E> {
        <Self as VirtioDeviceActions>::reset(self)
    }

    fn interrupt_status(&self) -> &Arc<AtomicU8> {
        <Self as VirtioDeviceActions>::interrupt_status(self)
    }

    fn config_generation(&self) -> u8 {
        self.borrow().config_generation
    }

    fn read_config(&self, offset: usize, data: &mut [u8]) {
        <Self as VirtioDeviceActions>::read_config(self, offset, data)
    }

    fn write_config(&mut self, offset: usize, data: &[u8]) {
        <Self as VirtioDeviceActions>::write_config(self, offset, data)
    }
}

impl<T> WithDriverSelect for T
where
    T: BorrowMut<VirtioConfig<Queue>> + VirtioDevice,
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

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::mmio::VirtioMmioDevice;
    use std::borrow::Borrow;
    use std::sync::atomic::Ordering;

    pub struct Dummy {
        pub cfg: VirtioConfig<Queue>,
        pub device_type: u32,
        pub activate_count: u64,
        pub reset_count: u64,
        pub last_queue_notify: u32,
    }

    impl Dummy {
        pub fn new(device_type: u32, features: u64, config_space: Vec<u8>) -> Self {
            let queue = Queue::new(256).unwrap();

            let cfg = VirtioConfig::new(features, vec![queue], config_space);
            Dummy {
                cfg,
                device_type,
                activate_count: 0,
                reset_count: 0,
                last_queue_notify: 0,
            }
        }
    }

    impl VirtioDeviceType for Dummy {
        fn device_type(&self) -> u32 {
            self.device_type
        }
    }

    impl Borrow<VirtioConfig<Queue>> for Dummy {
        fn borrow(&self) -> &VirtioConfig<Queue> {
            &self.cfg
        }
    }

    impl BorrowMut<VirtioConfig<Queue>> for Dummy {
        fn borrow_mut(&mut self) -> &mut VirtioConfig<Queue> {
            &mut self.cfg
        }
    }

    impl VirtioDeviceActions for Dummy {
        type E = ();

        fn activate(&mut self) -> Result<(), Self::E> {
            self.activate_count += 1;
            Ok(())
        }

        fn reset(&mut self) -> Result<(), Self::E> {
            self.reset_count += 1;
            Ok(())
        }
    }

    impl VirtioMmioDevice for Dummy {
        fn queue_notify(&mut self, val: u32) {
            self.last_queue_notify = val;
        }
    }

    #[test]
    fn test_impls() {
        let device_type = 2;
        let features = 7;

        let config_space = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

        let mut d = Dummy::new(device_type, features, config_space.clone());

        assert_eq!(VirtioDevice::device_type(&d), device_type);
        assert_eq!(d.num_queues(), 1);

        assert!(d.queue(0).is_some());
        assert!(d.queue_mut(0).is_some());
        assert!(d.queue(1).is_none());
        assert!(d.queue_mut(1).is_none());

        assert_eq!(d.device_features(), features);

        assert_eq!(d.driver_features(), 0);
        d.set_driver_features(0, 1);
        assert_eq!(d.driver_features(), 1);
        d.set_driver_features(1, 1);
        assert_eq!(d.driver_features(), (1 << 32) + 1);
        d.set_driver_features(2, 1);
        assert_eq!(d.driver_features(), (1 << 32) + 1);

        assert_eq!(d.device_status(), 0);
        d.set_device_status(2);
        assert_eq!(d.device_status(), 2);

        let len = config_space.len();
        let v1 = vec![0u8; len];
        let mut v2 = vec![0u8; len];

        // Offset to large to read anything.
        VirtioDevice::read_config(&d, len, v2.as_mut_slice());
        assert_eq!(v1, v2);

        VirtioDevice::read_config(&d, len / 2, v2.as_mut_slice());
        for i in 0..len {
            if i < len / 2 {
                assert_eq!(v2[i], config_space[len / 2 + i]);
            } else {
                assert_eq!(v2[i], 0);
            }
        }

        // Offset too large to overwrite anything.
        VirtioDevice::write_config(&mut d, len, v1.as_slice());
        assert_eq!(d.cfg.config_space, config_space);

        VirtioDevice::write_config(&mut d, len / 2, v1.as_slice());
        for (i, &value) in config_space.iter().enumerate().take(len) {
            if i < len / 2 {
                assert_eq!(d.cfg.config_space[i], value);
            } else {
                assert_eq!(d.cfg.config_space[i], 0);
            }
        }

        d.cfg.interrupt_status.fetch_or(1, Ordering::SeqCst);
        assert_eq!(VirtioDevice::interrupt_status(&d).load(Ordering::SeqCst), 1);

        // Let's test the `WithDriverSelect` auto impl now.
        assert_eq!(d.queue_select(), 0);
        d.set_queue_select(1);
        assert_eq!(d.queue_select(), 1);

        assert_eq!(d.device_features_select(), 0);
        d.set_device_features_select(1);
        assert_eq!(d.device_features_select(), 1);

        assert_eq!(d.driver_features_select(), 0);
        d.set_driver_features_select(1);
        assert_eq!(d.driver_features_select(), 1);
    }
}
