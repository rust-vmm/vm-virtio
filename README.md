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
[CI pipeline](https://buildkite.com/rust-vmm/vm-virtio-ci).

Each individual test runs in a container. To reproduce a test locally, you can
use the dev-container on both x86 and arm64.

```bash
docker run -it \
           --security-opt seccomp=unconfined \
           --volume $(pwd):/vm-virtio \
           fandree/rust-vmm-dev
cd vm-virtio/
cargo test
```

### Test Profiles

The integration tests support two test profiles:

* **devel**: this is the recommended profile for running the integration tests
  on a local development machine.

* **ci** (default option): this is the profile used when running the
  integration tests as part of the the Continuous Integration (CI).

The test profiles are applicable to tests that run using pytest. Currently only
the [coverage test](tests/test_coverage.py) follows this model as all the other
integration tests are run using the
[Buildkite pipeline](https://buildkite.com/rust-vmm/vm-virtio-ci).

The difference between is declaring tests as passed or failed:

* with the **devel** profile the coverage test passes if the current coverage
  is equal or higher than the upstream coverage value. In case the current
  coverage is higher, the coverage file is updated to the new coverage value.

* with the **ci** profile the coverage test passes only if the current coverage
  is equal to the upstream coverage value.

Further details about the coverage test can be found in the
[Adaptive Coverage](#adaptive-coverage) section.

### Adaptive Coverage

The line coverage is saved in [tests/coverage](tests/coverage). To update the
coverage before submitting a PR, run the coverage test:

```bash
docker run -it \
           --security-opt seccomp=unconfined \
           --volume $(pwd):/vm-virtio \
           fandree/rust-vmm-dev
cd vm-virtio/
pytest --profile=devel tests/test_coverage.py
```

If the PR coverage is higher than the upstream coverage, the coverage file
needs to be manually added to the commit before submitting the PR:

```bash
git add tests/coverage
```

Failing to do so will generate a fail on the CI pipeline when publishing the
PR.

**NOTE:** The coverage file is only updated in the `devel` test profile. In
the `ci` profile the coverage test will fail if the current coverage is higher
than the coverage reported in [tests/coverage](tests/coverage).
