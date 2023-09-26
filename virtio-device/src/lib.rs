// Copyright 2018 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

//! A crate that offers building blocks for virtio devices.

#![deny(missing_docs)]

mod mmio;
mod virtio_config;

use std::result;
use std::sync::atomic::AtomicU8;
use std::sync::Arc;

use log::warn;
use virtio_queue::QueueT;

pub use mmio::VirtioMmioDevice;
pub use virtio_config::{VirtioConfig, VirtioDeviceActions, VirtioDeviceType};

// TODO: Bring this (and other feature definitions) to the vm-virtio crate proper.
// Using a local const temporarily until then.
const VIRTIO_F_RING_EVENT_IDX: u64 = 29;

/// When the driver initializes the device, it lets the device know about the completed stages
/// using the Device Status field.
///
/// These following consts are defined in the order in which the bits would typically be set by
/// the driver. `RESET` -> `ACKNOWLEDGE` -> `DRIVER` and so on. This module is a 1:1 mapping for
/// the Device Status field in the virtio 1.1 specification, section 2.1 (except for the `RESET`
/// value, which is not explicitly named there as such). The status flag descriptions (except
/// `RESET`) are taken from the standard.
pub mod status {
    /// The initial status of the device.
    pub const RESET: u8 = 0;
    /// Indicates that the guest OS has found the device and recognized it as a valid
    /// virtio device.
    pub const ACKNOWLEDGE: u8 = 1;
    /// Indicates that the guest OS knows how to drive the device.
    pub const DRIVER: u8 = 2;
    /// Indicates that something went wrong in the guest, and it has given up on the device.
    /// This could be an internal error, or the driver didn’t like the device for some reason,
    /// or even a fatal error during device operation.
    pub const FAILED: u8 = 128;
    /// Indicates that the driver has acknowledged all the features it understands, and feature
    /// negotiation is complete.
    pub const FEATURES_OK: u8 = 8;
    /// Indicates that the driver is set up and ready to drive the device.
    pub const DRIVER_OK: u8 = 4;
    /// Indicates that the device has experienced an error from which it can’t recover.
    pub const DEVICE_NEEDS_RESET: u8 = 64;
}

// We're currently relying on macros from the `log` crate to output messages (as do other modules
// from `vm-virtio`). This is temporary solution until we agree on a better alternative going
// forward since different customers most likely have different expectation around levels,
// messages, formatting, etc.

/// A common interface for Virtio devices, shared by all transports. The methods present here
/// are mainly concerned with enabling the initial discovery/configuration and related interactions
/// between a device and the driver over the transport protocol. Once a device is activated, queue
/// handling is generally implementation specific, based on the features and notification
/// mechanisms established during the configuration phase.
pub trait VirtioDevice {
    /// Error type for operations such as `activate` and `reset`.
    type E;
    /// The type of queue used for the operation of this device.
    type Q: QueueT;

    /// The virtio device type.
    fn device_type(&self) -> u32;

    /// The maximum number of queues supported by the device.
    fn num_queues(&self) -> u16;

    /// Return a reference to the queue currently selected by the driver, or `None` for an
    /// invalid selection.
    fn queue(&self, index: u16) -> Option<&Self::Q>;

    /// Return a mutable reference to the queue currently selected by the driver, or `None`
    /// for an invalid selection.
    fn queue_mut(&mut self, index: u16) -> Option<&mut Self::Q>;

    /// Return the features advertised by the device.
    ///
    /// Using `u64` for the entire feature set because it's wide enough for the entire feature
    /// set specified by the standard (and we can later switch to `u128` if necessary).
    fn device_features(&self) -> u64;

    /// Return the features bits written by the driver.
    fn driver_features(&self) -> u64;

    /// Set the specified page of features written by the driver.
    fn set_driver_features(&mut self, page: u32, value: u32);

    /// Return the current device status flags.
    fn device_status(&self) -> u8;

    /// Validate the current device status with respect to a group of flags that must be set,
    /// and another group that must be cleared.
    fn check_device_status(&self, set: u8, cleared: u8) -> bool {
        self.device_status() & (set | cleared) == set
    }

    /// Set the value of the device status flags. This is just a simple accessor method, and
    /// `ack_device_status` must be used to process a status update coming from the driver.
    fn set_device_status(&mut self, status: u8);

    /// Acknowledge a status update from the driver, based on the provided value. This method
    /// is not just a simple accessor, but rather is expected to handle virtio device status
    /// transitions (which may involve things such as calling activation or reset logic).
    fn ack_device_status(&mut self, status: u8) {
        use status::*;
        let current_status = self.device_status();

        // Match changed bits.
        match !current_status & status {
            ACKNOWLEDGE if current_status == RESET => {
                self.set_device_status(status);
            }
            DRIVER if current_status == ACKNOWLEDGE => {
                self.set_device_status(status);
            }
            FEATURES_OK if current_status == (ACKNOWLEDGE | DRIVER) => {
                // Ensure the driver did not ack a feature that wasn't actually offered. If that
                // happens, the standard specifies devices should not actually accept/set the
                // `FEATURES_OK` status bit.
                if !self.device_features() & self.driver_features() != 0 {
                    warn!("driver accepted invalid feature bits");
                    return;
                }

                // Set the appropriate configuration flag for all queues if we offered the
                //`VIRTIO_F_RING_EVENT_IDX` feature and the driver acknowledged it.
                if self.driver_features() & (1 << VIRTIO_F_RING_EVENT_IDX) != 0 {
                    for i in 0..self.num_queues() {
                        // The unwrap is ok to use here because we're requesting mutable
                        // references for queues at valid indices only.
                        self.queue_mut(i).unwrap().set_event_idx(true);
                    }
                }

                self.set_device_status(status);
            }
            DRIVER_OK if current_status == (ACKNOWLEDGE | DRIVER | FEATURES_OK) => {
                if self.activate().is_ok() {
                    self.set_device_status(status);
                } else {
                    warn!("activation error");
                }
            }
            _ if (status & FAILED) != 0 => {
                self.set_device_status(current_status | FAILED);
            }
            // The driver writes a zero to the status register to request a device reset.
            _ if status == 0 => {
                if self.reset().is_err() {
                    warn!("reset error");
                }
            }
            _ => {
                warn!(
                    "invalid virtio driver status transition: 0x{:x} -> 0x{:x}",
                    self.device_status(),
                    status
                );
            }
        }
    }

    /// Invoke implementation specific device activation logic.
    fn activate(&mut self) -> result::Result<(), Self::E>;

    /// Invoke implementation specific device reset logic.
    fn reset(&mut self) -> result::Result<(), Self::E>;

    /// Borrow the handle to the interrupt status of the device.
    ///
    /// This is currently represented as an `Arc<AtomicU8>` because it often needs to be shared
    /// between multiple threads that are running different parts of device-specific functionality.
    fn interrupt_status(&self) -> &Arc<AtomicU8>;

    /// Return the current config generation value.
    fn config_generation(&self) -> u8;

    /// Read from the configuration space associated with the device into `data`,
    /// starting at `offset`.
    fn read_config(&self, offset: usize, data: &mut [u8]);

    /// Write to the configuration space associated with the device at `offset`, using
    /// input from `data`.
    fn write_config(&mut self, offset: usize, data: &[u8]);
}

/// Virtio transports such as MMIO and PCI use a two step mechanism to read or write various parts
/// of device configuration, by first selecting a queue or features page and then performing the
/// actual access. `WithDriverSelect` provides common abstractions for this pattern on top of the
/// `VirtioDevice` interface.
pub trait WithDriverSelect: VirtioDevice {
    /// Return the index of the currently selected queue.
    fn queue_select(&self) -> u16;

    /// Set the index of the queue currently selected by the driver.
    fn set_queue_select(&mut self, value: u16);

    /// Return a handle to the currently selected queue, or `None` for an invalid selection.
    fn selected_queue(&self) -> Option<&<Self as VirtioDevice>::Q> {
        self.queue(self.queue_select())
    }

    /// Return a mutable handle to the currently selected queue, or `None` for an invalid selection.
    fn selected_queue_mut(&mut self) -> Option<&mut <Self as VirtioDevice>::Q> {
        self.queue_mut(self.queue_select())
    }

    /// Return the device features page currently selected by the driver.
    fn device_features_select(&self) -> u32;

    /// Set the index of the currently selected device features page.
    fn set_device_features_select(&mut self, value: u32);

    /// Return the currently selected driver features page.
    fn driver_features_select(&self) -> u32;

    /// Set the index of the currently selected page for driver features acknowledgement.
    fn set_driver_features_select(&mut self, value: u32);
}

#[cfg(test)]
mod tests {
    use crate::status::*;
    use crate::virtio_config::tests::Dummy;

    use super::*;

    #[test]
    fn test_ack_device_status() {
        // We're using the `Dummy` struct that gets a `VirtioDevice` implementation
        // automatically via the logic in `virtio_config`. The auto implementation does
        // not override the default `ack_device_status` implementation.

        let mut d = Dummy::new(0, 0, Vec::new());

        // TODO: This is just a quick test for the happy path mostly. Find a better way to test
        // things for the various combinations which are possible.

        assert_eq!(d.cfg.device_status, 0);

        // Doesn't do anything; `ACKNOWLEDGE` has to be set first.
        d.ack_device_status(DRIVER);
        assert_eq!(d.cfg.device_status, 0);

        let mut status = ACKNOWLEDGE;

        d.ack_device_status(status);
        assert_eq!(d.cfg.device_status, status);

        status |= DRIVER;
        d.ack_device_status(status);
        assert_eq!(d.cfg.device_status, status);

        // Test several `ack_device_status` cases.
        {
            let old_status = status;

            status |= FEATURES_OK;
            d.ack_device_status(status);
            assert_eq!(d.cfg.device_status, status);

            // Make sure the EVENT_IDX feature was not advertised.
            assert_eq!(d.cfg.device_features & (1 << VIRTIO_F_RING_EVENT_IDX), 0);

            for q in d.cfg.queues.iter() {
                assert!(!q.event_idx_enabled());
            }

            // Revert status.
            d.cfg.device_status = old_status;

            d.cfg.driver_features |= 1 << VIRTIO_F_RING_EVENT_IDX;

            d.ack_device_status(status);
            // The device status didn't change because the "driver" acknowledged a feature that's
            // not advertised by the device.
            assert_eq!(d.cfg.device_status, old_status);

            d.cfg.device_features |= 1 << VIRTIO_F_RING_EVENT_IDX;
            d.ack_device_status(status);
            assert_eq!(d.cfg.device_status, status);

            for q in d.cfg.queues.iter() {
                assert!(q.event_idx_enabled());
            }
        }

        status |= FEATURES_OK;
        d.ack_device_status(status);
        assert_eq!(d.cfg.device_status, status);

        assert_eq!(d.activate_count, 0);
        status |= DRIVER_OK;
        d.ack_device_status(status);
        assert_eq!(d.cfg.device_status, status);
        assert_eq!(d.activate_count, 1);

        d.ack_device_status(FAILED);
        assert_ne!(d.cfg.device_status & FAILED, 0);

        assert_eq!(d.reset_count, 0);
        d.ack_device_status(RESET);
        assert_eq!(d.reset_count, 1);
    }
}
