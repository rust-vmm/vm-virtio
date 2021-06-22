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
// This isn't explicitly added to v1.1 spec, though it was implemented in Linux and QEMU in 2010.
// (but it will be added nevertheless to the subsequent version).
// It does not have a feature bit, but devices respond with VIRTIO_BLK_S_UNSUPP if a request type is
// unimplemented. See commit b342d29 from [virtio-spec](https://github.com/oasis-tcs/virtio-spec).
/// Get device ID request.
pub const VIRTIO_BLK_T_GET_ID: u32 = 8;
/// Discard request.
pub const VIRTIO_BLK_T_DISCARD: u32 = 11;
/// Write zeroes request.
pub const VIRTIO_BLK_T_WRITE_ZEROES: u32 = 13;

// Feature bits.
/// Read-only device.
pub const VIRTIO_BLK_F_RO: u64 = 5;
/// Flush command supported.
pub const VIRTIO_BLK_F_FLUSH: u64 = 9;
/// Discard command supported.
pub const VIRTIO_BLK_F_DISCARD: u64 = 13;
/// Write zeroes command supported.
pub const VIRTIO_BLK_F_WRITE_ZEROES: u64 = 14;

/// Length of block device id.
pub const VIRTIO_BLK_ID_BYTES: usize = 20;

/// Sector shift.
pub const SECTOR_SHIFT: u8 = 9;
/// Sector size of a block device.
pub const SECTOR_SIZE: u64 = (0x01 as u64) << SECTOR_SHIFT;

//Status bytes.
/// Success.
pub const VIRTIO_BLK_S_OK: u8 = 0;
/// Device or driver error.
pub const VIRTIO_BLK_S_IOERR: u8 = 1;
/// Request unsupported by device.
pub const VIRTIO_BLK_S_UNSUPP: u8 = 2;
