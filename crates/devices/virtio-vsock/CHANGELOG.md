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
