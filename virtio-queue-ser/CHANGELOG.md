# Upcoming release

# v0.7.0

- Updated virtio-queue from 0.9.1 to 0.10.0.

# v0.6.0

## Changed

- Updated vm-memory from 0.11.0 to 0.13.1.
- Updated virtio-queue from 0.8.0 to 0.9.1.

# v0.5.0

## Changed

- Updated vm-memory from 0.10.0 to 0.11.0.
- Updated virtio-queue from 0.7.1 to 0.8.0.

# v0.4.1
- Update the virtio-queue dependency to v0.7.1. This release contains no
  breaking changes.

# v0.4.0

## Added 

- Derived `Eq` for `state::QueueStateSer`.

## Changed
- Updated vm-memory from 0.9.0 to 0.10.0.
- Updated virtio-queue from 0.6.1 to 0.7.0 and fix version to exactly 0.7.0 to ensure the crates 
  are always updated in lock-step.
- Upgrade rust edition to 2021

# v0.3.0

## Changed
- Update the way that dependencies are pulled such that we don't end up with incompatible versions.

## Removed
- Removed the `num_added` from the saved state. This is an implementation detail coming from
  the notification suppression feature, so it shouldn't be part of the state.

# v0.2.0

- Relax the dependency on `virtio-queue` so that we do not need to publish a release of this crate
  whenever we have a new release of `virtio-queue`.

# v0.1.0

This is the first release of the crate, compatible with version `0.3.x` of `virtio-queue`.
