// Copyright 2019 Red Hat, Inc. All Rights Reserved.
// SPDX-License-Identifier: (BSD-3-Clause OR Apache-2.0)

#![allow(clippy::all)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(clippy::undocumented_unsafe_blocks)]

pub mod virtio_blk;
pub mod virtio_config;
pub mod virtio_gpu;
pub mod virtio_mmio;
pub mod virtio_net;
pub mod virtio_ring;
pub mod virtio_scsi;

pub mod bindings {
    pub use super::{virtio_blk, virtio_config, virtio_mmio, virtio_net, virtio_ring, virtio_scsi};
}
