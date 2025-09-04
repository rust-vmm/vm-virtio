// Copyright 2025 Alyssa Ross <hi@alyssa.is>
// SPDX-License-Identifier: BSD-3-Clause OR Apache-2.0

#![allow(clippy::all)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(clippy::undocumented_unsafe_blocks)]

#[cfg_attr(target_arch = "arm", path = "bindings/arm/virtio_blk.rs")]
#[cfg_attr(target_arch = "aarch64", path = "bindings/aarch64/virtio_blk.rs")]
#[cfg_attr(target_arch = "hexagon", path = "bindings/hexagon/virtio_blk.rs")]
#[cfg_attr(
    target_arch = "loongarch64",
    path = "bindings/loongarch64/virtio_blk.rs"
)]
#[cfg_attr(target_arch = "m68k", path = "bindings/m68k/virtio_blk.rs")]
#[cfg_attr(target_arch = "mips", path = "bindings/mipsel/virtio_blk.rs")]
#[cfg_attr(
    all(target_arch = "powerpc64", target_endian = "big"),
    path = "bindings/powerpc64/virtio_blk.rs"
)]
#[cfg_attr(
    all(target_arch = "powerpc64", target_endian = "little"),
    path = "bindings/powerpc64le/virtio_blk.rs"
)]
#[cfg_attr(target_arch = "riscv64", path = "bindings/riscv64/virtio_blk.rs")]
#[cfg_attr(target_arch = "s390x", path = "bindings/s390x/virtio_blk.rs")]
#[cfg_attr(target_arch = "sparc64", path = "bindings/sparc64/virtio_blk.rs")]
#[cfg_attr(target_arch = "x86_64", path = "bindings/x86_64/virtio_blk.rs")]
pub mod virtio_blk;

#[cfg_attr(target_arch = "arm", path = "bindings/arm/virtio_config.rs")]
#[cfg_attr(target_arch = "aarch64", path = "bindings/aarch64/virtio_config.rs")]
#[cfg_attr(target_arch = "hexagon", path = "bindings/hexagon/virtio_config.rs")]
#[cfg_attr(
    target_arch = "loongarch64",
    path = "bindings/loongarch64/virtio_config.rs"
)]
#[cfg_attr(target_arch = "m68k", path = "bindings/m68k/virtio_config.rs")]
#[cfg_attr(target_arch = "mips", path = "bindings/mipsel/virtio_config.rs")]
#[cfg_attr(
    all(target_arch = "powerpc64", target_endian = "big"),
    path = "bindings/powerpc64/virtio_config.rs"
)]
#[cfg_attr(
    all(target_arch = "powerpc64", target_endian = "little"),
    path = "bindings/powerpc64le/virtio_config.rs"
)]
#[cfg_attr(target_arch = "riscv64", path = "bindings/riscv64/virtio_config.rs")]
#[cfg_attr(target_arch = "s390x", path = "bindings/s390x/virtio_config.rs")]
#[cfg_attr(target_arch = "sparc64", path = "bindings/sparc64/virtio_config.rs")]
#[cfg_attr(target_arch = "x86_64", path = "bindings/x86_64/virtio_config.rs")]
pub mod virtio_config;

#[cfg_attr(target_arch = "arm", path = "bindings/arm/virtio_gpu.rs")]
#[cfg_attr(target_arch = "aarch64", path = "bindings/aarch64/virtio_gpu.rs")]
#[cfg_attr(target_arch = "hexagon", path = "bindings/hexagon/virtio_gpu.rs")]
#[cfg_attr(
    target_arch = "loongarch64",
    path = "bindings/loongarch64/virtio_gpu.rs"
)]
#[cfg_attr(target_arch = "m68k", path = "bindings/m68k/virtio_gpu.rs")]
#[cfg_attr(target_arch = "mips", path = "bindings/mipsel/virtio_gpu.rs")]
#[cfg_attr(
    all(target_arch = "powerpc64", target_endian = "big"),
    path = "bindings/powerpc64/virtio_gpu.rs"
)]
#[cfg_attr(
    all(target_arch = "powerpc64", target_endian = "little"),
    path = "bindings/powerpc64le/virtio_gpu.rs"
)]
#[cfg_attr(target_arch = "riscv64", path = "bindings/riscv64/virtio_gpu.rs")]
#[cfg_attr(target_arch = "s390x", path = "bindings/s390x/virtio_gpu.rs")]
#[cfg_attr(target_arch = "sparc64", path = "bindings/sparc64/virtio_gpu.rs")]
#[cfg_attr(target_arch = "x86_64", path = "bindings/x86_64/virtio_gpu.rs")]
pub mod virtio_gpu;

#[cfg_attr(target_arch = "arm", path = "bindings/arm/virtio_ids.rs")]
#[cfg_attr(target_arch = "aarch64", path = "bindings/aarch64/virtio_ids.rs")]
#[cfg_attr(target_arch = "hexagon", path = "bindings/hexagon/virtio_ids.rs")]
#[cfg_attr(
    target_arch = "loongarch64",
    path = "bindings/loongarch64/virtio_ids.rs"
)]
#[cfg_attr(target_arch = "m68k", path = "bindings/m68k/virtio_ids.rs")]
#[cfg_attr(target_arch = "mips", path = "bindings/mipsel/virtio_ids.rs")]
#[cfg_attr(
    all(target_arch = "powerpc64", target_endian = "big"),
    path = "bindings/powerpc64/virtio_ids.rs"
)]
#[cfg_attr(
    all(target_arch = "powerpc64", target_endian = "little"),
    path = "bindings/powerpc64le/virtio_ids.rs"
)]
#[cfg_attr(target_arch = "riscv64", path = "bindings/riscv64/virtio_ids.rs")]
#[cfg_attr(target_arch = "s390x", path = "bindings/s390x/virtio_ids.rs")]
#[cfg_attr(target_arch = "sparc64", path = "bindings/sparc64/virtio_ids.rs")]
#[cfg_attr(target_arch = "x86_64", path = "bindings/x86_64/virtio_ids.rs")]
pub mod virtio_ids;

#[cfg_attr(target_arch = "arm", path = "bindings/arm/virtio_input.rs")]
#[cfg_attr(target_arch = "aarch64", path = "bindings/aarch64/virtio_input.rs")]
#[cfg_attr(target_arch = "hexagon", path = "bindings/hexagon/virtio_input.rs")]
#[cfg_attr(
    target_arch = "loongarch64",
    path = "bindings/loongarch64/virtio_input.rs"
)]
#[cfg_attr(target_arch = "m68k", path = "bindings/m68k/virtio_input.rs")]
#[cfg_attr(target_arch = "mips", path = "bindings/mipsel/virtio_input.rs")]
#[cfg_attr(
    all(target_arch = "powerpc64", target_endian = "big"),
    path = "bindings/powerpc64/virtio_input.rs"
)]
#[cfg_attr(
    all(target_arch = "powerpc64", target_endian = "little"),
    path = "bindings/powerpc64le/virtio_input.rs"
)]
#[cfg_attr(target_arch = "riscv64", path = "bindings/riscv64/virtio_input.rs")]
#[cfg_attr(target_arch = "s390x", path = "bindings/s390x/virtio_input.rs")]
#[cfg_attr(target_arch = "sparc64", path = "bindings/sparc64/virtio_input.rs")]
#[cfg_attr(target_arch = "x86_64", path = "bindings/x86_64/virtio_input.rs")]
pub mod virtio_input;

#[cfg_attr(target_arch = "arm", path = "bindings/arm/virtio_mmio.rs")]
#[cfg_attr(target_arch = "aarch64", path = "bindings/aarch64/virtio_mmio.rs")]
#[cfg_attr(target_arch = "hexagon", path = "bindings/hexagon/virtio_mmio.rs")]
#[cfg_attr(
    target_arch = "loongarch64",
    path = "bindings/loongarch64/virtio_mmio.rs"
)]
#[cfg_attr(target_arch = "m68k", path = "bindings/m68k/virtio_mmio.rs")]
#[cfg_attr(target_arch = "mips", path = "bindings/mipsel/virtio_mmio.rs")]
#[cfg_attr(
    all(target_arch = "powerpc64", target_endian = "big"),
    path = "bindings/powerpc64/virtio_mmio.rs"
)]
#[cfg_attr(
    all(target_arch = "powerpc64", target_endian = "little"),
    path = "bindings/powerpc64le/virtio_mmio.rs"
)]
#[cfg_attr(target_arch = "riscv64", path = "bindings/riscv64/virtio_mmio.rs")]
#[cfg_attr(target_arch = "s390x", path = "bindings/s390x/virtio_mmio.rs")]
#[cfg_attr(target_arch = "sparc64", path = "bindings/sparc64/virtio_mmio.rs")]
#[cfg_attr(target_arch = "x86_64", path = "bindings/x86_64/virtio_mmio.rs")]
pub mod virtio_mmio;

pub mod virtio_net;

#[cfg_attr(target_arch = "arm", path = "bindings/arm/virtio_ring.rs")]
#[cfg_attr(target_arch = "aarch64", path = "bindings/aarch64/virtio_ring.rs")]
#[cfg_attr(target_arch = "hexagon", path = "bindings/hexagon/virtio_ring.rs")]
#[cfg_attr(
    target_arch = "loongarch64",
    path = "bindings/loongarch64/virtio_ring.rs"
)]
#[cfg_attr(target_arch = "m68k", path = "bindings/m68k/virtio_ring.rs")]
#[cfg_attr(target_arch = "mips", path = "bindings/mipsel/virtio_ring.rs")]
#[cfg_attr(
    all(target_arch = "powerpc64", target_endian = "big"),
    path = "bindings/powerpc64/virtio_ring.rs"
)]
#[cfg_attr(
    all(target_arch = "powerpc64", target_endian = "little"),
    path = "bindings/powerpc64le/virtio_ring.rs"
)]
#[cfg_attr(target_arch = "riscv64", path = "bindings/riscv64/virtio_ring.rs")]
#[cfg_attr(target_arch = "s390x", path = "bindings/s390x/virtio_ring.rs")]
#[cfg_attr(target_arch = "sparc64", path = "bindings/sparc64/virtio_ring.rs")]
#[cfg_attr(target_arch = "x86_64", path = "bindings/x86_64/virtio_ring.rs")]
pub mod virtio_ring;

#[cfg_attr(target_arch = "arm", path = "bindings/arm/virtio_scsi.rs")]
#[cfg_attr(target_arch = "aarch64", path = "bindings/aarch64/virtio_scsi.rs")]
#[cfg_attr(target_arch = "hexagon", path = "bindings/hexagon/virtio_scsi.rs")]
#[cfg_attr(
    target_arch = "loongarch64",
    path = "bindings/loongarch64/virtio_scsi.rs"
)]
#[cfg_attr(target_arch = "m68k", path = "bindings/m68k/virtio_scsi.rs")]
#[cfg_attr(target_arch = "mips", path = "bindings/mipsel/virtio_scsi.rs")]
#[cfg_attr(
    all(target_arch = "powerpc64", target_endian = "big"),
    path = "bindings/powerpc64/virtio_scsi.rs"
)]
#[cfg_attr(
    all(target_arch = "powerpc64", target_endian = "little"),
    path = "bindings/powerpc64le/virtio_scsi.rs"
)]
#[cfg_attr(target_arch = "riscv64", path = "bindings/riscv64/virtio_scsi.rs")]
#[cfg_attr(target_arch = "s390x", path = "bindings/s390x/virtio_scsi.rs")]
#[cfg_attr(target_arch = "sparc64", path = "bindings/sparc64/virtio_scsi.rs")]
#[cfg_attr(target_arch = "x86_64", path = "bindings/x86_64/virtio_scsi.rs")]
pub mod virtio_scsi;

pub mod bindings {
    pub use super::{virtio_blk, virtio_config, virtio_mmio, virtio_net, virtio_ring, virtio_scsi};
}
