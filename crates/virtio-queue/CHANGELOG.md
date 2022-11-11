# v0.7.0

## Changed

- Updated vmm-sys-util from 0.10.0 to 0.11.0.
- Updated vm-memory from 0.9.0 to 0.10.0.

# v0.6.1

## Fixed
- Return an error if the number of available descriptor chains exposed by the
  driver exceeds the queue size. This way we avoid potential hanging and
  Denial-of-Service in the VMM, that was possible before by iterating multiple
  times over the same chains.

# v0.6.0

## Added
- Derive `Eq` for structures that derive `PartialEq`.

## Changed
- Use `add_desc_chains` in tests
- Update dependencies: `vm-memory` from `0.8.0` to `0.9.0` and `log` from `0.4.6` to `0.4.17`.
- Upgrade to Rust 2021 edition.

# v0.5.0

## Added
- Added getters and setters for the Virtio Queue fields.
- Added the `state` method for retrieving the `QueueState` of a `Queue`.

## Fixed
- Validate the state of the Virtio Queue when restoring from state and return errors on invalid
  input.

## Removed
- Removed the wrapper over the Virtio Queue that was wrapping the Guest Memory. VMMs can define
  this wrapper if needed, but this is no longer provided as part of virtio-queue crate so that the
  naming scheme can be simplified. As a consequence, a couple of functions now receive the
  memory as a parameter (more details in the Changed section).
- Removed `num_added` field from the `QueueState` because this is an implementation detail of
  the notification suppression feature and thus should not be part of the state.
- Removed `QueueGuard` and `lock_with_memory`.

## Changed
- `QueueState` is now renamed to `Queue`.
- `QueueStateSync` is now renamed to `QueueSync`.
- The `QueueState` structure now represents the state of the `Queue` without any implementation
  details. This can be used for implementing save/restore.
- Initializing a `Queue` now returns an error in case the `max_size` is invalid.
- The `Queue` fields are now private and can be updated only through the dedicated setters.
- The following Queue methods now receive the memory as a parameter: `iter`, `is_valid`,
  `add_used`, `needs_notification`, `enable_notification`, `disable_notification`, `avail_idx`,
  `used_idx`.
- Use the constant definition from the `virtio-queue` crate.

# v0.4.0

## Fixed
- [[#173]](https://github.com/rust-vmm/vm-virtio/pull/173) Fix potential division by zero in
  iterator when the queue size is 0.

## Changed
- [[#162]](https://github.com/rust-vmm/vm-virtio/pull/162) Added error handling in the mock
  interface and the ability to create multiple descriptor chains for testing in order to
  support running fuzzing.
- [[#174]](https://github.com/rust-vmm/vm-virtio/pull/174) Updated the `avail_idx` and `used_idx`
  documentation to specify when these functions panic.


# v0.3.0

## Added
- [[#148]](https://github.com/rust-vmm/vm-virtio/pull/148): `QueueStateOwnedT` trait that stands
  for queue objects which are exclusively owned and accessed by a single thread of execution.
- [[#148]](https://github.com/rust-vmm/vm-virtio/pull/148): Added the `pop_descriptor_chain`
  method, which can be used to consume descriptor chains from the available ring without
  using an iterator, to `QueueStateT` and `QueueGuard`. Also added `go_to_previous_position()`
  to `QueueGuard`, which enables decrementing the next available index by one position, which
  effectively undoes the consumption of a descriptor chain in some use cases.
- [[#151]](https://github.com/rust-vmm/vm-virtio/pull/151): Added `MockSplitQueue::add_desc_chain()`,
  which places a descriptor chain at the specified offset in the descriptor table.  
- [[#153]](https://github.com/rust-vmm/vm-virtio/pull/153): Added `QueueStateT::size()` to return
  the size of the queue.

## Changed
- The minimum version of the `vm-memory` dependency is now `v0.8.0`
- [[#161]](https://github.com/rust-vmm/vm-virtio/pull/161): Improve the efficiency of `needs_notification`

## Removed
- [[#153]](https://github.com/rust-vmm/vm-virtio/pull/153): `#[derive(Clone)]` for `QueueState`

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
