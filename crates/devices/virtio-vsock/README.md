# virtio-vsock

The `virtio-vsock` crate provides abstractions for the components of the
[vsock device](https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-39000010).
For now, it offers only an implementation for the vsock packet.
The support is provided only for stream sockets.

The vsock device is a socket device that can be used as a communication
mechanism between the host and the guest. It is implemented using the virtio
standard. The vsock device has three queues: an RX one, a TX one and an event
one. In a simplified manner, the communication between the host and the guest
is realized with the buffers that are exchanged using the device’s queues.
These buffers are called packets in the vsock device context.

## Vsock Packet

### Design

The virtio vsock packet is defined in the standard as having a header of type
`virtio_vsock_hdr` and an optional `data` array of bytes. There are multiple
operations that can be requested within a packet, e.g. `VIRTIO_VSOCK_OP_RST`
for resetting the connection, `VIRTIO_VSOCK_OP_RW` for sending payload. Most
operations are of the `VIRTIO_VSOCK_OP_RW` type, which means for data transfer,
and the other ones are used for connection and buffer space management.
`data` is non-empty only for the `VIRTIO_VSOCK_OP_RW` operations.

The abstraction used for the packet implementation is the `VsockPacket`.
It is using
[`VolatileSlice`](https://github.com/rust-vmm/vm-memory/blob/fc7153a4f63c352d1fa9419c4654a6c9aec408cb/src/volatile_memory.rs#L266)s
for representing the header and the data. We chose to use the `VolatileSlice`
because it's a safe wrapper over the unsafe Rust's raw pointers, and it is also
generic enough to allow creating packets from pointers to slices. Going with a
`GuestMemory` based approach would not make such configuration possible.
More details (including design
limitations) in [the `packet`'s module-level documentation](src/packet.rs).

A `VsockPacket` instance is created by parsing a descriptor chain from either
the TX or the RX virtqueue. The `VsockPacket` API is also providing methods for
creating/setting up packets directly from pointers to slices.
It also offers setters and getters for each `virtio_vsock_hdr` field (e.g.
*src_cid*, *dst_port*, *op*).

### Usage

The driver queues receive buffers on the RX virtqueue, and outgoing packets on
the TX virtqueue. The device processes the RX virtqueue using 
`VsockPacket::from_rx_virtq_chain` and fills the buffers with data from the
vsock backend.
On the TX side, the device processes the TX queue using
`VsockPacket::from_tx_virtq_chain`, packages the read buffers as vsock packets,
and then sends them to the backend.

### Examples

Examples of usage can be found as documentation tests in
[the packet module](src/packet.rs).

## License

This project is licensed under either of

- [Apache License](http://www.apache.org/licenses/LICENSE-2.0), Version 2.0
- [BSD-3-Clause License](https://opensource.org/licenses/BSD-3-Clause)
