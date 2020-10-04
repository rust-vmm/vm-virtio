// Copyright 2018 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

use std::convert::TryInto;
use std::sync::atomic::Ordering;

use vm_memory::{GuestAddress, GuestAddressSpace};

use crate::device::{status, WithDriverSelect};
use crate::Queue;

// Required by the Virtio MMIO device register layout at offset 0 from base. Turns out this
// is actually the ASCII sequence for "virt" (in little endian ordering).
const MMIO_MAGIC_VALUE: u32 = 0x7472_6976;

// Current version specified by the Virtio standard (legacy devices used 1 here).
const MMIO_VERSION: u32 = 2;

// TODO: Crosvm was using 0 here a while ago, and Firecracker started doing that as well. Should
// we leave it like that, or should we use the VENDOR_ID value for PCI Virtio devices? It looks
// like the standard doesn't say anything regarding an actual VENDOR_ID value for MMIO devices.
const VENDOR_ID: u32 = 0;

// Helper function that runs the provided closure to mutate the currently selected queue of
// a `VirtioDevice`, provided the status check is successful.
// TODO: This function and its uses will likely have to be updated when we start offering
// packed virtqueue support as well.
fn update_queue_field<M, D, F>(device: &mut D, f: F)
where
    M: GuestAddressSpace,
    D: WithDriverSelect<M> + ?Sized,
    F: FnOnce(&mut Queue<M>),
{
    if device.check_device_status(status::FEATURES_OK, status::DRIVER_OK | status::FAILED) {
        if let Some(queue) = device.selected_queue_mut() {
            f(queue);
        } else {
            warn!("update invalid virtio queue");
        }
    } else {
        warn!(
            "update virtio queue in invalid state 0x{:x}",
            device.device_status()
        );
    }
}

// Helper function that rewrites the most significant 4 bytes of the provided `GuestAddress`.
fn set_high(v: &mut GuestAddress, hi: u32) {
    *v = (*v & 0xffff_ffff) | (u64::from(hi) << 32)
}

// Helper function that rewrites the least significant 4 bytes of the provided `GuestAddress`.
fn set_low(v: &mut GuestAddress, lo: u32) {
    *v = (*v & !0xffff_ffff) | u64::from(lo)
}

/// A common interface for Virtio devices that use the MMIO transport, which also provides a
/// default implementation of read and write operations from/to the device registers and
/// configuration space.
// Adding the `M` generic parameter that's also required by `VirtioDevice` for the time being.
pub trait VirtioMmioDevice<M: GuestAddressSpace>: WithDriverSelect<M> {
    /// Callback invoked when the driver writes a value to the Queue Notify configuration register.
    ///
    /// This is the simplest mechanism the driver can use to notify a virtio MMIO device. The
    /// meaning of the value is interpreted as specified by the standard. Many VMMs use something
    /// like the KVM `ioeventfd` mechanism, which eliminates the need to implement this method.
    // TODO: Move this to the `VirtioDevice` interface if it uniformly applies to all transports.
    fn queue_notify(&mut self, _val: u32) {
        // Do nothing by default.
    }

    /// Handle a driver read operation from the MMIO space of the device.
    fn read(&self, offset: u64, data: &mut [u8]) {
        match offset {
            // The standard specifies that accesses to configuration registers are 32-bit wide.
            0x00..=0xff if data.len() == 4 => {
                let v = match offset {
                    0x0 => MMIO_MAGIC_VALUE,
                    0x04 => MMIO_VERSION,
                    0x08 => self.device_type(),
                    0x0c => VENDOR_ID,
                    0x10 => match self.device_features_select() {
                        0 => self.device_features() as u32,
                        1 => (self.device_features() >> 32) as u32,
                        // No device features defined beyond the first two pages.
                        _ => 0,
                    },
                    0x34 => self
                        .selected_queue()
                        .map(Queue::max_size)
                        .unwrap_or(0)
                        .into(),
                    0x44 => self
                        .selected_queue()
                        .map(|q| q.ready)
                        .unwrap_or(false)
                        .into(),
                    0x60 => self.interrupt_status().load(Ordering::SeqCst).into(),
                    0x70 => self.device_status().into(),
                    0xfc => self.config_generation().into(),
                    _ => {
                        warn!("unknown virtio mmio register read: 0x{:x}", offset);
                        return;
                    }
                };
                // This cannot panic, because we checked that `data.len() == 4`.
                data.copy_from_slice(v.to_le_bytes().as_ref());
            }

            // TODO: The standard specifies that configuration space size is device specific, so
            // we might want to express that via the trait instead of hard coding the current
            // arbitrary ceiling.
            // It's ok to use `as` here because `offset` always fits into an `usize` in this case.
            0x100..=0xfff => self.read_config(offset as usize - 0x100, data),
            _ => {
                warn!(
                    "invalid virtio mmio read: 0x{:x}:0x{:x}",
                    offset,
                    data.len()
                );
            }
        };
    }

    /// Handle a driver write operation to the MMIO space of the device.
    fn write(&mut self, offset: u64, data: &[u8]) {
        match offset {
            // The standard specifies that accesses to configuration registers are 32-bit wide.
            0x00..=0xff if data.len() == 4 => {
                // The `try_into` below attempts to convert `data` to a `[u8; 4]`, which
                // always succeeds because we previously checked that `data.len() == 4`.
                let v = u32::from_le_bytes(data.try_into().unwrap());
                match offset {
                    0x14 => self.set_device_features_select(v),
                    0x20 => {
                        if self.check_device_status(
                            status::DRIVER,
                            status::FEATURES_OK | status::FAILED,
                        ) {
                            self.set_driver_features(self.driver_features_select(), v);
                        } else {
                            warn!(
                                "ack virtio features in invalid state 0x{:x}",
                                self.device_status()
                            );
                        }
                    }
                    0x24 => self.set_driver_features_select(v),

                    // TODO: add warnings or signal some sort of event (depending on how we end up
                    // implementing logging and metrics) for values that do not actually fit the
                    // data type specified by the virtio standard (we simply use `as` conversion
                    // for now).
                    0x30 => self.set_queue_select(v as u16),
                    0x38 => update_queue_field(self, |q| q.size = v as u16),
                    0x44 => update_queue_field(self, |q| q.ready = v == 1),
                    0x50 => self.queue_notify(v),
                    0x64 => {
                        if self.check_device_status(status::DRIVER_OK, 0) {
                            self.interrupt_status()
                                .fetch_and(!(v as u8), Ordering::SeqCst);
                        }
                    }
                    0x70 => self.ack_device_status(v as u8),
                    0x80 => update_queue_field(self, |q| set_low(&mut q.desc_table, v)),
                    0x84 => update_queue_field(self, |q| set_high(&mut q.desc_table, v)),
                    0x90 => update_queue_field(self, |q| set_low(&mut q.avail_ring, v)),
                    0x94 => update_queue_field(self, |q| set_high(&mut q.avail_ring, v)),
                    0xa0 => update_queue_field(self, |q| set_low(&mut q.used_ring, v)),
                    0xa4 => update_queue_field(self, |q| set_high(&mut q.used_ring, v)),
                    _ => {
                        warn!("unknown virtio mmio register write: 0x{:x}", offset);
                    }
                }
            }
            // TODO: The standard specifies that configuration space size is device specific, so
            // we might want to express that via the trait instead of hard coding the current
            // arbitrary ceiling (same as for `read`).
            0x100..=0xfff => {
                if self.check_device_status(status::DRIVER, status::FAILED) {
                    // It's ok to use `as` here because `offset` always fits into an `usize`.
                    self.write_config(offset as usize - 0x100, data)
                } else {
                    warn!("can not write to device config data area before driver is ready");
                }
            }
            _ => {
                warn!(
                    "invalid virtio mmio write: 0x{:x}:0x{:x}",
                    offset,
                    data.len()
                );
            }
        }
    }
}
