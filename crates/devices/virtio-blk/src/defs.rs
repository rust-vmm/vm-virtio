// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

/// Sector shift.
pub const SECTOR_SHIFT: u8 = 9;
/// Sector size of a block device.
pub const SECTOR_SIZE: u64 = (0x01_u64) << SECTOR_SHIFT;
