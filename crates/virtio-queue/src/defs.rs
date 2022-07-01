// Copyright 2021 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

//! Virtio queue related constant definitions

/// Size of used ring header: flags (u16) + idx (u16)
pub(crate) const VIRTQ_USED_RING_HEADER_SIZE: u64 = 4;

/// Size of the used ring metadata: header + avail_event (le16).
///
/// The total size of the used ring is:
/// VIRTQ_USED_RING_META_SIZE + VIRTQ_USED_ELEMENT_SIZE * queue_size.
pub(crate) const VIRTQ_USED_RING_META_SIZE: u64 = VIRTQ_USED_RING_HEADER_SIZE + 2;

/// Size of one element in the used ring, id (le32) + len (le32).
pub(crate) const VIRTQ_USED_ELEMENT_SIZE: u64 = 8;

/// Size of available ring header: flags(u16) + idx(u16)
pub(crate) const VIRTQ_AVAIL_RING_HEADER_SIZE: u64 = 4;

/// Size of the available ring metadata: header + used_event (le16).
///
/// The total size of the available ring is:
/// VIRTQ_AVAIL_RING_META_SIZE + VIRTQ_AVAIL_ELEMENT_SIZE * queue_size.
pub(crate) const VIRTQ_AVAIL_RING_META_SIZE: u64 = VIRTQ_AVAIL_RING_HEADER_SIZE + 2;

/// Size of one element in the available ring (le16).
pub(crate) const VIRTQ_AVAIL_ELEMENT_SIZE: u64 = 2;

/// Default guest physical address for descriptor table.
pub(crate) const DEFAULT_DESC_TABLE_ADDR: u64 = 0x0;

/// Default guest physical address for available ring.
pub(crate) const DEFAULT_AVAIL_RING_ADDR: u64 = 0x0;

/// Default guest physical address for used ring.
pub(crate) const DEFAULT_USED_RING_ADDR: u64 = 0x0;
