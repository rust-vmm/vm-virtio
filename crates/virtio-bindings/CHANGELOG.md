# Upcoming Release

## Added

- Add bindings for virtio_config.h, virtio_gpu.h, and virtio_mmio.h

## Changed

- Regenerate bindings with Glibc 2.36, Linux 6.0, and bindgen 0.61.0
- The `virtio-v4_14_0` and `virtio-v5_0_0` crate features are now no-ops
  — the latest version of the bindings is now always used.

# v0.1.0

This is the first `virtio-bindings` crate release.

This crate provides Rust FFI bindings to the
[Virtual I/O Device (VIRTIO)](https://docs.oasis-open.org/virtio/virtio/v1.1/virtio-v1.1.html)
Linux kernel API. With this first release, the bindings are for the Linux kernel
versions 4.14 and 5.0.

The bindings are generated using [bindgen](https://crates.io/crates/bindgen).
