// Portions Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Copyright © 2019 Intel Corporation
//
// Copyright (C) 2020-2021 Alibaba Cloud. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0 AND BSD-3-Clause

use vm_memory::{ByteValued, GuestAddress};

use crate::defs::{VIRTQ_DESC_F_INDIRECT, VIRTQ_DESC_F_NEXT, VIRTQ_DESC_F_WRITE};

/// A virtio descriptor constraints with C representation.
#[repr(C)]
#[derive(Default, Clone, Copy, Debug)]
pub struct Descriptor {
    /// Guest physical address of device specific data
    addr: u64,

    /// Length of device specific data
    len: u32,

    /// Includes next, write, and indirect bits
    flags: u16,

    /// Index into the descriptor table of the next descriptor if flags has the next bit set
    next: u16,
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

    /// Check whether this descriptor refers to a buffer containing an indirect descriptor table.
    pub fn refers_to_indirect_table(&self) -> bool {
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

#[cfg(any(test, feature = "test-utils"))]
impl Descriptor {
    /// Creates a new descriptor
    pub fn new(addr: u64, len: u32, flags: u16, next: u16) -> Self {
        Descriptor {
            addr: addr.to_le(),
            len: len.to_le(),
            flags: flags.to_le(),
            next: next.to_le(),
        }
    }

    /// Set the guest physical address of descriptor buffer
    pub fn set_addr(&mut self, addr: u64) {
        self.addr = addr.to_le();
    }

    /// Set the length of descriptor buffer.
    pub fn set_len(&mut self, len: u32) {
        self.len = len.to_le();
    }

    /// Set the flags for this descriptor.
    pub fn set_flags(&mut self, flags: u16) {
        self.flags = flags.to_le();
    }

    /// Set the value stored in the `next` field of the descriptor.
    pub fn set_next(&mut self, next: u16) {
        self.next = next.to_le();
    }
}

unsafe impl ByteValued for Descriptor {}

/// Represents the contents of an element from the used virtqueue ring.
#[repr(C)]
#[derive(Clone, Copy, Default, Debug)]
pub struct VirtqUsedElem {
    id: u32,
    len: u32,
}

impl VirtqUsedElem {
    /// Create a new `VirtqUsedElem` instance.
    pub fn new(id: u16, len: u32) -> Self {
        VirtqUsedElem {
            id: u32::from_le(id as u32),
            len: len.to_le(),
        }
    }
}

#[cfg(any(test, feature = "test-utils"))]
#[allow(clippy::len_without_is_empty)]
impl VirtqUsedElem {
    /// Get id field of the used descriptor.
    pub fn id(&self) -> u32 {
        u32::from_le(self.id)
    }

    /// Get length field of the used descriptor.
    pub fn len(&self) -> u32 {
        u32::from_le(self.len)
    }
}

unsafe impl ByteValued for VirtqUsedElem {}

#[cfg(test)]
mod tests {
    use super::*;
    use memoffset::offset_of;
    use std::mem::{align_of, size_of};

    #[test]
    fn test_descriptor_offset() {
        assert_eq!(size_of::<Descriptor>(), 16);
        assert_eq!(offset_of!(Descriptor, addr), 0);
        assert_eq!(offset_of!(Descriptor, len), 8);
        assert_eq!(offset_of!(Descriptor, flags), 12);
        assert_eq!(offset_of!(Descriptor, next), 14);
        assert!(align_of::<Descriptor>() <= 16);
    }

    #[test]
    fn test_descriptor_getter_setter() {
        let mut desc = Descriptor::new(0, 0, 0, 0);

        desc.set_addr(0x1000);
        assert_eq!(desc.addr(), GuestAddress(0x1000));
        desc.set_len(0x2000);
        assert_eq!(desc.len(), 0x2000);
        desc.set_flags(VIRTQ_DESC_F_NEXT);
        assert_eq!(desc.flags(), VIRTQ_DESC_F_NEXT);
        assert_eq!(desc.has_next(), true);
        assert_eq!(desc.is_write_only(), false);
        assert_eq!(desc.refers_to_indirect_table(), false);
        desc.set_flags(VIRTQ_DESC_F_WRITE);
        assert_eq!(desc.flags(), VIRTQ_DESC_F_WRITE);
        assert_eq!(desc.has_next(), false);
        assert_eq!(desc.is_write_only(), true);
        assert_eq!(desc.refers_to_indirect_table(), false);
        desc.set_flags(VIRTQ_DESC_F_INDIRECT);
        assert_eq!(desc.flags(), VIRTQ_DESC_F_INDIRECT);
        assert_eq!(desc.has_next(), false);
        assert_eq!(desc.is_write_only(), false);
        assert_eq!(desc.refers_to_indirect_table(), true);
        desc.set_next(3);
        assert_eq!(desc.next(), 3);
    }

    #[test]
    fn test_descriptor_copy() {
        let e1 = Descriptor::new(1, 2, VIRTQ_DESC_F_NEXT, 3);
        let mut e2 = Descriptor::default();

        e2.as_mut_slice().copy_from_slice(e1.as_slice());
        assert_eq!(e1.addr(), e2.addr());
        assert_eq!(e1.len(), e2.len());
        assert_eq!(e1.flags(), e2.flags());
        assert_eq!(e1.next(), e2.next());
    }

    #[test]
    fn test_used_elem_offset() {
        assert_eq!(offset_of!(VirtqUsedElem, id), 0);
        assert_eq!(offset_of!(VirtqUsedElem, len), 4);
        assert_eq!(size_of::<VirtqUsedElem>(), 8);
    }

    #[test]
    fn test_used_elem_copy() {
        let e1 = VirtqUsedElem::new(3, 15);
        let mut e2 = VirtqUsedElem::new(0, 0);

        e2.as_mut_slice().copy_from_slice(e1.as_slice());
        assert_eq!(e1.id, e2.id);
        assert_eq!(e1.len, e2.len);
    }
}
