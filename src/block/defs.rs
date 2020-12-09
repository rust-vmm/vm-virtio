// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

// Request types.
/// Read request.
pub const VIRTIO_BLK_T_IN: u32 = 0;
/// Write request.
pub const VIRTIO_BLK_T_OUT: u32 = 1;
/// Flush request.
pub const VIRTIO_BLK_T_FLUSH: u32 = 4;

// Feature bits.
/// Read-only device.
pub const VIRTIO_BLK_F_RO: u64 = 5;
/// Flush command supported.
pub const VIRTIO_BLK_F_FLUSH: u64 = 9;

/// Sector shift.
pub const SECTOR_SHIFT: u8 = 9;
/// Sector size of a block device.
pub const SECTOR_SIZE: u64 = (0x01 as u64) << SECTOR_SHIFT;
