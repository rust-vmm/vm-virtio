[![Build Status](https://badge.buildkite.com/9e0e6c88972a3248a0908506d6946624da84e4e18c0870c4d0.svg)](https://buildkite.com/rust-vmm/vm-virtio-ci)

# vm-virtio

The vm-virtio crate provides a [virtio](https://www.oasis-open.org/committees/tc_home.php?wg_abbrev=virtio)
device implementation:

* A virtio virtqueue and Descriptor chain API
* A virtio device trait (`VirtioDevice`)

## Virtio `Device` trait

Virtio device implementations will implement the `VirtioDevice` trait.
Typically the VMM will implement virtio devices and provide the paravirtualized
IO emulation for all supported virtio devices. For example a VMM willing to emulate
a virtio networking device will implement the `VirtioDevice` trait.

The `VirtioDevice` implementation will be discovered by the guest through a virtio
transport layer (MMIO, PCI or channel IO). The transport layer implementation will
then call into the `VirtioDevice` `activate` method to notify the device that the
guest driver is done configuring it and that it should be ready to handle IO from
the guest.
On the other hand, the `VirtioDevice` `reset` method will be called by the transport
layer when the guest driver needs to reset and release all the emulated device resources.

## Virtio queue API

The `vm-virtio` queue API is to be consumed by virtio device implementations.
The virtio device (net, block, rng, etc) implementation will call into the
queue API to allocate and manage its specific virtio queues:

* `new()` to allocate its queues.

* `iter()` to iterate over the queue descriptors and consume virtio queue
  buffers made available by the guest driver.

* `add_used()` to place a virtio queue buffer into the queue and have the
  guest driver consume it.

## Tests

Our Continuous Integration (CI) pipeline is implemented on top of
[Buildkite](https://buildkite.com/).
For the complete list of tests, check our
[CI pipeline](https://buildkite.com/rust-vmm/rust-vmm-ci).

Each individual test runs in a container. To reproduce a test locally, you can
use the dev-container on both x86 and arm64.

```bash
container_version=5
docker run -it \
           --security-opt seccomp=unconfined \
           --volume $(pwd):/vm-virtio \
           rustvmm/dev:v${container_version}
cd vm-virtio/
cargo test
```
