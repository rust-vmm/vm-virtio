# vm-virtio

The `vm-virtio` workspace provides
[virtio](https://www.oasis-open.org/committees/tc_home.php?wg_abbrev=virtio)
abstractions and implementation for the virtio queue and devices. For now, it
consists of the following crates:

- `virtio-bindings` -> provides Rust FFI bindings to the corresponding Linux 
  kernel API;
- `virtio-blk` -> contains abstractions for parsing and executing a request of
  the block device;
- `virtio-console` -> contains abstractions for the virtio console device;
- `virtio-device` -> provides abstractions for the common functionality of the
  virtio devices, and a default implementation for the MMIO
  transport operations (read, write);
- `virtio-queue` -> provides a virtio device implementation for a virtio queue,
                    a virtio descriptor and a chain of such descriptors;
- `virtio-queue-ser` -> provides abstractions for serialization and 
   deserialization for virtio queue states;
- `virtio-vsock` -> provides an implementation for the vsock packet.

### Note
We offer support only for virtio v1.0+
([the legacy interface](https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-60001)
is not supported).

The queues are the mechanism for data transport between the virtio device and
the guest driver. Each device can have zero or more virtqueues, for example the
block device has one queue, the vsock device has three queues etc. The
communication between the driver and device is possible through different
transport options, i.e. PCI, MMIO, and Channel I/O buses.
In addition to the queue and device emulation that is provided in `vm-virtio`,
the VMM has to also define the device backend and the event handling mechanism.

## The `Queue` abstraction

For details about the abstractions provided in `virtio-queue`, check
[its separate README](./virtio-queue/README.md).

## The `VirtioDevice` trait

Virtio device implementations will implement the `VirtioDevice` trait.
Typically, the VMM will implement virtio devices and provide the
paravirtualized IO emulation for all supported virtio devices. For example,
a VMM willing to emulate a virtio networking device will implement the
`VirtioDevice` trait.

The `VirtioDevice` implementation will be discovered by the guest through a
virtio transport layer (MMIO, PCI or Channel I/O). The transport layer
implementation will then call into the `VirtioDevice`'s `activate` method to
notify the device that the guest driver is done configuring it and that it
should be ready to handle IO from the guest.
On the other hand, the `VirtioDevice`'s `reset` method will be called by the
transport layer when the guest driver needs to reset and release all the
emulated device resources.

## Tests

Our Continuous Integration (CI) pipeline is implemented on top of
[Buildkite](https://buildkite.com/).
For the complete list of tests, check our
[CI pipeline](https://github.com/rust-vmm/rust-vmm-ci/blob/main/.buildkite/test_description.json).

Each individual test runs in a container. To run the tests locally, you can
use the dev-container on both x86 and arm64.

```bash
cd ~/vm-virtio
container_version=15
docker run -it \
           --security-opt seccomp=unconfined \
           --volume $(pwd):/vm-virtio \
           --volume ~/.ssh:/root/.ssh \
           rustvmm/dev:v${container_version}
cd vm-virtio
./rust-vmm-ci/test_run.py
```

The `vm-virtio` workspace is tested with unit tests (including documentation
examples). For running all the tests, use the following command:

```bash
cargo test --all-features
```

`--all-features` is used in order to also include the tests under a feature,
such as `backend-stdio`.

For details about the testing in the `virtio-queue` crate, check
[its separate documentation](./virtio-queue/docs/TESTING.md).

## Fuzzing

We run 15 minutes long fuzzing sessions for each PR and on merges to the main
branch. For more details about the fuzz targets and implementation, check the
[Fuzzing Readme](fuzz/README.md).

For changes that could introduce security vulnerabilities, we recommend running
the "fuzzing-vm-virtio" Buildkite pipeline that runs fuzzing for 1 day instead
of 15 minutes. This pipeline is optional which means that PRs can be merged
without waiting for the fuzzing sessions to finish. As running fuzzing for 1
day keeps the Builkite agents busy and could cause delays in merging other PRs,
this longer fuzzing sessions are not run by default on all PRs. To enable the
run, one of the
[Buildkite administrators](https://github.com/rust-vmm/community/blob/main/docs/setup_new_repo.md#set-up-ci)
need to unblock the pipeline by following the Buildkite run link in the PR and
click on the corresponding
[unblock pipeline button](https://buildkite.com/docs/pipelines/block-step).

## License

This project is licensed under either of

- [Apache License](http://www.apache.org/licenses/LICENSE-2.0), Version 2.0
- [BSD-3-Clause License](https://opensource.org/licenses/BSD-3-Clause)
