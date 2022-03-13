# Unreleased

## Added
- QueueStateT::size(): [#153](https://github.com/rust-vmm/vm-virtio/pull/153)

## Removed
- #[derive(Clone)] for QueueState: [#153](https://github.com/rust-vmm/vm-virtio/pull/153)

# v0.2.0

## Added

- *Testing Interface*: Added the possibility to initialize a mock descriptor
  chain from a list of descriptors.
- Added setters and getters for the queue fields required for extending the
  `Queue` in VMMs.

## Fixed

- Apply the appropriate endianness conversion on `used_idx`.

# v0.1.0

This is the first release of the crate.
