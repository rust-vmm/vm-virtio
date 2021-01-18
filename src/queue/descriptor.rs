// Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Portions Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// Copyright © 2019 Intel Corporation
//
// Copyright (C) 2020 Alibaba Cloud. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0 AND BSD-3-Clause

use vm_memory::{ByteValued, GuestAddress};

pub(crate) const VIRTQ_DESC_F_NEXT: u16 = 0x1;
pub(crate) const VIRTQ_DESC_F_WRITE: u16 = 0x2;
pub(crate) const VIRTQ_DESC_F_INDIRECT: u16 = 0x4;

// The Virtio Spec 1.0 defines the alignment of VirtIO descriptor is 16 bytes,
// which fulfills the explicit constraint of GuestMemory::read_obj().
pub(crate) const VIRTQ_DESCRIPTOR_SIZE: usize = 16;

/// A virtio descriptor constraints with C representation
#[repr(C)]
#[derive(Default, Clone, Copy)]
pub struct Descriptor {
    /// Guest physical address of device specific data
    pub(crate) addr: u64,

    /// Length of device specific data
    pub(crate) len: u32,

    /// Includes next, write, and indirect bits
    pub(crate) flags: u16,

    /// Index into the descriptor table of the next descriptor if flags has
    /// the next bit set
    pub(crate) next: u16,
}

#[allow(clippy::len_without_is_empty)]
impl Descriptor {
    /// Return the guest physical address of descriptor buffer
    pub fn addr(&self) -> GuestAddress {
        GuestAddress(self.addr)
    }

    /// Return the length of descriptor buffer
    pub fn len(&self) -> u32 {
        self.len
    }

    /// Return the flags for this descriptor, including next, write and indirect
    /// bits
    pub fn flags(&self) -> u16 {
        self.flags
    }

    /// Return the value stored in the `next` field of the descriptor.
    pub fn next(&self) -> u16 {
        self.next
    }

    /// Check whether this is an indirect descriptor.
    pub fn is_indirect(&self) -> bool {
        // TODO: The are a couple of restrictions in terms of which flags combinations are
        // actually valid for indirect descriptors. Implement those checks as well somewhere.
        self.flags() & VIRTQ_DESC_F_INDIRECT != 0
    }

    /// Check whether the `VIRTQ_DESC_F_NEXT` is set for the descriptor.
    pub fn has_next(&self) -> bool {
        self.flags() & VIRTQ_DESC_F_NEXT != 0
    }

    /// Checks if the driver designated this as a write only descriptor.
    ///
    /// If this is false, this descriptor is read only.
    /// Write only means the the emulated device can write and the driver can read.
    pub fn is_write_only(&self) -> bool {
        self.flags & VIRTQ_DESC_F_WRITE != 0
    }
}

unsafe impl ByteValued for Descriptor {}
