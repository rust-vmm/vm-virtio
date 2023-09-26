# virtio-queue-ser

This crate is a companion to [virtio-queue](https://crates.io/crates/virtio-queue),
focusing on persistent state representation for use cases such as (de)serialization.
The main abstraction is the `QueueStateSer` object, which can be converted to and
from `QueueState` via the provided `From` trait implementations. `virtio-queue-ser` currently
supports (de)serialization of `QueueStateSer` objects via [serde](https://crates.io/crates/serde)
and [versionize](https://crates.io/crates/versionize). The former always serializes the latest
version of `QueueStateSer`, whereas multiple versions will be supported with `versionize` as
breaking changes are introduced to `QueueState` (and, by extension, `QueueStateSer`).

On serialization, the typical workflow is to start from a `state: QueueState` object, obtain
the corresponding `QueueStateSer` (i.e. `state_ser = QueueStateSer::from(&state)`), then write
the serialized data using the underlying backend (i.e. `serde` or `versionize`). When deserializing,
we first get a `state_ser: QueueStateSer` object from the backend, and then convert it to a
`QueueState` (for example, `state = QueueState::from(&state_ser)`).

When a `versionize`-based backend is used, the state transformations required to transition between
versions are transparent to consumers of `virtio-queue-ser`. For example, if an older version of
`QueueStateSer` has been serialized with `versionize`, and we're deserializing based on that data,
then the `QueueStateSer` object obtained via `versionize` will automatically include any changes
required for converting to the current version.

## License

This project is licensed under either of

- [Apache License](http://www.apache.org/licenses/LICENSE-2.0), Version 2.0
- [BSD-3-Clause License](https://opensource.org/licenses/BSD-3-Clause)
