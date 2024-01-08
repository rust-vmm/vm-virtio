# Upcoming

# v0.5.0

## Changes

- Update vm-memory from 0.13.1 to 0.14.0.
- Update virtio-queue from 0.10.0 to 0.11.0.

# v0.4.0

Mostly identical to v0.3.2, which was incorrectly published as minor release.

## Changes

- Update virtio-queue from 0.9.1 to 0.10.0 (same minor/major problems)

# v0.3.2 - yanked

This version got yanked. It should have been a major release. The vm-memory
dependency - which received a major bump - is part of the public interface.

## Changes

- Update vm-memory from 0.12.0 to 0.13.1.
- Update virtio-queue from 0.9.0 to 0.9.1.

# v0.3.1

## Changes

- Updated vm-memory from 0.11.0 to 0.12.0.

# v0.3.0

## Changes

- Updated vm-memory from 0.10.0 to 0.11.0.
- Updated virtio-queue from 0.7.0 to 0.8.0.

# v0.2.1

## Changes

- `VsockPacket::from_tx_virtq_chain` supports header and data on the same descriptor
- `VsockPacket::from_rx_virtq_chain` supports header and data on the same descriptor

# v0.2.0

## Added

- Derive `Eq` for `packet::PacketHeader`.

## Changes

- Updated vm-memory to 0.10.0.
- Updated virtio-queue to 0.7.0.
- Upgrade Rust edition to 2021.

# v0.1.0

This is the first release of the crate.
