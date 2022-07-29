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
