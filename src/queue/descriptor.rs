// Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Portions Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// Copyright © 2019 Intel Corporation
//
// Copyright (C) 2021 Alibaba Cloud. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0 AND BSD-3-Clause

use vm_memory::{ByteValued, GuestAddress};

use super::{VIRTQ_DESC_F_INDIRECT, VIRTQ_DESC_F_NEXT, VIRTQ_DESC_F_WRITE};

/// A split virtio descriptor to encapsulate a driver data buffer.
///
/// The descriptor table refers to the buffers the driver is using for the device. The `addr` is
/// a physical address, and the buffers can be chained via next. Each descriptor describes a
/// buffer which is read-only for the device (“device-readable”) or write-only for the device
/// (“device-writable”), but a chain of descriptors can contain both device-readable and
/// device-writable buffers.
#[repr(C)]
#[derive(Default, Clone, Copy)]
pub struct Descriptor {
    /// Guest physical address of the data buffer.
    pub(crate) addr: u64,

    /// Length of the data buffer.
    pub(crate) len: u32,

    /// Data buffer flags, including the next, write, and indirect bits.
    pub(crate) flags: u16,

    /// Index into the descriptor table of the next descriptor if flags has the next bit set.
    pub(crate) next: u16,
}

#[allow(clippy::len_without_is_empty)]
impl Descriptor {
    /// Return the guest physical address of descriptor buffer.
    pub fn addr(&self) -> GuestAddress {
        GuestAddress(self.addr)
    }

    /// Return the length of descriptor buffer.
    pub fn len(&self) -> u32 {
        self.len
    }

    /// Return the flags for this descriptor, including next, write and indirect bits.
    pub fn flags(&self) -> u16 {
        self.flags
    }

    /// Return the value stored in the `next` field of the descriptor.
    pub fn next(&self) -> u16 {
        self.next
    }

    /// Check whether the `VIRTQ_DESC_F_NEXT` is set for the descriptor.
    pub fn has_next(&self) -> bool {
        self.flags() & VIRTQ_DESC_F_NEXT != 0
    }

    /// Check whether this is an indirect descriptor.
    pub fn is_indirect(&self) -> bool {
        // TODO: The are a couple of restrictions in terms of which flags combinations are
        // actually valid for indirect descriptors. Implement those checks as well somewhere.
        self.flags() & VIRTQ_DESC_F_INDIRECT != 0
    }

    /// Checks if the driver designated this as a write only descriptor.
    ///
    /// If this is false, this descriptor is read only.
    /// Write only means the the emulated device can write and the driver can read.
    pub fn is_write_only(&self) -> bool {
        self.flags() & VIRTQ_DESC_F_WRITE != 0
    }
}

unsafe impl ByteValued for Descriptor {}

#[cfg(test)]
mod tests {
    use super::*;
    use vm_memory::Address;

    macro_rules! offset_of {
        ($ty:ty, $field:ident) => {
            unsafe { &(*(0 as *const $ty)).$field as *const _ as usize }
        };
    }

    #[test]
    fn test_offset() {
        assert_eq!(offset_of!(Descriptor, addr), 0);
        assert_eq!(offset_of!(Descriptor, len), 8);
        assert_eq!(offset_of!(Descriptor, flags), 12);
        assert_eq!(offset_of!(Descriptor, next), 14);
    }

    #[test]
    fn test_new_descriptor() {
        let mut desc = Descriptor {
            addr: 0x1000,
            len: 0x2000,
            flags: VIRTQ_DESC_F_WRITE | VIRTQ_DESC_F_NEXT,
            next: 1,
        };

        assert_eq!(desc.addr().raw_value(), 0x1000);
        assert_eq!(desc.len(), 0x2000);
        assert_eq!(desc.next(), 1);
        assert_eq!(desc.has_next(), true);
        assert_eq!(desc.is_write_only(), true);
        assert_eq!(desc.is_indirect(), false);

        desc.flags = VIRTQ_DESC_F_INDIRECT;
        assert_eq!(desc.has_next(), false);
        assert_eq!(desc.is_write_only(), false);
        assert_eq!(desc.is_indirect(), true);
    }
}
