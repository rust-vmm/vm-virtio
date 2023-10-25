# Upcoming Release

# v0.2.2

## Added

- Added bindings for virtio_ids.h
- Regenerate bindings with Linux 6.4.

# v0.2.1

- Regenerate bindings with Linux 6.3.
- Added bindings for virtio_scsi.h
- Updated vm-memory from 0.10.0 to 0.12.0.

# v0.2.0

## Added

- Add bindings for virtio_config.h, virtio_gpu.h, and virtio_mmio.h

## Changed

- Regenerate bindings with Glibc 2.36, Linux 6.1, and bindgen 0.63.0
- The `virtio-v4_14_0` and `virtio-v5_0_0` crate features are now no-ops
  — the latest version of the bindings is now always used.
- The bindings modules no longer accidentally re-export constants from
  Glibc or other kernel headers. As a result of this, it is no longer
  possible to reference constants from virtio_config.h through
  e.g. the `virtio_net` module, only through the `virtio_config`
  module.

# v0.1.0

This is the first `virtio-bindings` crate release.

This crate provides Rust FFI bindings to the
[Virtual I/O Device (VIRTIO)](https://docs.oasis-open.org/virtio/virtio/v1.1/virtio-v1.1.html)
Linux kernel API. With this first release, the bindings are for the Linux kernel
versions 4.14 and 5.0.

The bindings are generated using [bindgen](https://crates.io/crates/bindgen).
