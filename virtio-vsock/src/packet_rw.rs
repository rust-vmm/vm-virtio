// Copyright 2026 Red Hat, Inc. All Rights Reserved.
//
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

//! Reader/Writer-based vsock packet abstractions.
//!
//! This module provides:
//!
//! - [`VsockPacketTx`](crate::packet_rw::VsockPacketTx) which handles parsing a vsock packet from
//!   a TX descriptor chain via
//!   [`VsockPacketTx::from_tx_virtq_chain`](crate::packet_rw::VsockPacketTx::from_tx_virtq_chain).
//!   It uses a [`Reader`](virtio_queue::Reader) to access the device-readable packet data, and
//!   stores a copy of the [`PacketHeader`](crate::PacketHeader).
//! - [`VsockPacketRx`](crate::packet_rw::VsockPacketRx) which handles parsing a vsock packet from
//!   an RX descriptor chain via
//!   [`VsockPacketRx::from_rx_virtq_chain`](crate::packet_rw::VsockPacketRx::from_rx_virtq_chain).
//!   It uses [`Writer`](virtio_queue::Writer)s for the header and data portions of the
//!   device-writable buffers.
//!
//! The virtio vsock packet is defined in the virtio specification as having a header of type
//! `struct virtio_vsock_hdr` and an optional `data` array of bytes. The descriptor chain layout is
//! handled transparently by the [`Reader`](virtio_queue::Reader)/[`Writer`](virtio_queue::Writer)
//! abstractions from `virtio_queue`. The buffers associated to the TX virtio queue are
//! device-readable, and the ones associated to the RX virtio queue are device-writable.

use std::fmt;
use std::ops::Deref;

use virtio_queue::{DescriptorChain, Reader, Writer};
use vm_memory::bitmap::{BitmapSlice, WithBitmapSlice};
use vm_memory::GuestMemory;

use crate::{Error, PacketHeader, Result, PKT_HEADER_SIZE};

/// The TX vsock packet, implemented as a wrapper over a virtio descriptor chain using a
/// [`Reader`]:
/// - a [`PacketHeader`] parsed from the chain;
/// - an optional data `Reader`, only present for data packets (`VSOCK_OP_RW`).
#[derive(Clone)]
pub struct VsockPacketTx<'a, B: BitmapSlice> {
    header: PacketHeader,
    data_slice: Option<Reader<'a, B>>,
}

impl<'a, B: BitmapSlice> VsockPacketTx<'a, B> {
    /// Return a reference to the `data_slice` of the packet, if present.
    pub fn data_slice(&self) -> Option<&Reader<'a, B>> {
        self.data_slice.as_ref()
    }

    /// Return a mutable reference to the `data_slice` of the packet, if present.
    pub fn data_slice_mut(&mut self) -> Option<&mut Reader<'a, B>> {
        self.data_slice.as_mut()
    }

    /// Return a reference to the packet header.
    pub fn header(&self) -> &PacketHeader {
        &self.header
    }

    /// Return a mutable reference to the packet header.
    pub fn header_mut(&mut self) -> &mut PacketHeader {
        &mut self.header
    }

    /// Create the packet wrapper from a TX chain.
    ///
    /// The chain is expected to hold a valid packet header, optionally followed by packet data.
    ///
    /// # Arguments
    ///
    /// * `mem` - the `GuestMemory` object that can be used to access the queue buffers.
    /// * `desc_chain` - the descriptor chain corresponding to a packet.
    /// * `max_data_size` - the maximum size allowed for the packet payload, that was negotiated
    ///   between the device and the driver.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use virtio_queue::mock::MockSplitQueue;
    /// # use virtio_queue::{desc::{split::Descriptor as SplitDescriptor, RawDescriptor}, Queue, QueueT};
    /// # use virtio_vsock::packet_rw::VsockPacketTx;
    /// # use virtio_vsock::{PKT_HEADER_SIZE, PacketHeader};
    /// # use vm_memory::{Bytes, GuestAddress, GuestAddressSpace, GuestMemoryMmap};
    ///
    /// # use std::io::Read;
    ///
    /// # const MAX_PKT_BUF_SIZE: u32 = 64 * 1024;
    /// # const LEN: u32 = 16;
    ///
    /// # fn create_queue_with_chain(m: &GuestMemoryMmap) -> Queue {
    /// #     let vq = MockSplitQueue::new(m, 16);
    /// #     let mut q = vq.create_queue().unwrap();
    /// #
    /// #     let v = vec![
    /// #         RawDescriptor::from(SplitDescriptor::new(0x5_0000, 0x100, 0, 0)),
    /// #         RawDescriptor::from(SplitDescriptor::new(0x8_0000, 0x100, 0, 0)),
    /// #     ];
    /// #     let mut chain = vq.build_desc_chain(&v);
    /// #     q
    /// # }
    /// let mem = GuestMemoryMmap::<()>::from_ranges(&[(GuestAddress(0), 0x10_0000)]).unwrap();
    ///
    /// // Write a header with a 16-byte payload into guest memory.
    /// let mut header = PacketHeader::default();
    /// header.set_src_cid(1).set_dst_cid(2).set_len(LEN);
    /// mem.write_obj(header, GuestAddress(0x5_0000)).unwrap();
    ///
    /// let mut queue = create_queue_with_chain(&mem);
    ///
    /// while let Some(head) = queue.pop_descriptor_chain(&mem) {
    ///     let head_index = head.head_index();
    ///     match VsockPacketTx::from_tx_virtq_chain(&mem, head, MAX_PKT_BUF_SIZE) {
    ///         Ok(mut pkt) => {
    ///             assert_eq!(pkt.header().src_cid(), 1);
    ///             assert_eq!(pkt.header().dst_cid(), 2);
    ///             let data_len = pkt.header().len() as usize;
    ///             // Read the payload data.
    ///             if let Some(reader) = pkt.data_slice_mut() {
    ///                 let mut buf = vec![0u8; data_len];
    ///                 reader.read_exact(&mut buf).unwrap();
    ///             }
    ///         }
    ///         Err(_e) => {
    ///             // Do some error handling.
    ///         }
    ///     };
    ///     queue.add_used(&mem, head_index, 0);
    /// }
    /// ```
    pub fn from_tx_virtq_chain<M, T>(
        mem: &'a M,
        desc_chain: DescriptorChain<T>,
        max_data_size: u32,
    ) -> Result<Self>
    where
        M: GuestMemory,
        <M as GuestMemory>::Bitmap: WithBitmapSlice<'a, S = B>,
        T: Deref<Target = M>,
        T::Target: GuestMemory,
    {
        let mut reader = desc_chain.reader(mem).map_err(|_| Error::InvalidChain)?;
        let header = reader
            .read_obj::<PacketHeader>()
            .map_err(|_| Error::DescriptorLengthTooSmall)?;

        let mut pkt = Self {
            header,
            data_slice: None,
        };

        // If the `len` field of the header is zero, then the packet doesn't have a `data` element.
        if pkt.header.is_empty() {
            return Ok(pkt);
        }

        // Reject packets that exceed the maximum allowed value for payload.
        if pkt.header.len() > max_data_size {
            return Err(Error::InvalidHeaderLen(pkt.header.len()));
        }

        // Reject packets whose payload is bigger than the available space on the descriptor chain.
        if pkt.header.len() as usize > reader.available_bytes() {
            return Err(Error::DescriptorLengthTooSmall);
        }

        // Limit the amount of data that can be read to the payload and not the full chain.
        let _ = reader.split_at(pkt.header.len() as usize);

        pkt.data_slice = Some(reader);
        Ok(pkt)
    }
}

impl<B: BitmapSlice> fmt::Debug for VsockPacketTx<'_, B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("VsockPacketTx")
            .field("header", &self.header)
            .field("has_data", &self.data_slice.is_some())
            .finish()
    }
}

/// The RX vsock packet, implemented as a wrapper over a virtio descriptor chain using
/// [`Writer`]s:
/// - a header `Writer` for writing the packet header;
/// - a data `Writer` for writing the packet payload.
pub struct VsockPacketRx<'a, B: BitmapSlice> {
    header_slice: Writer<'a, B>,
    data_slice: Writer<'a, B>,
}

impl<B: BitmapSlice> fmt::Debug for VsockPacketRx<'_, B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("VsockPacketRx").finish_non_exhaustive()
    }
}

impl<'a, B: BitmapSlice> VsockPacketRx<'a, B> {
    /// Return a mutable reference to the data `Writer` of the packet.
    pub fn data_slice(&mut self) -> &mut Writer<'a, B> {
        &mut self.data_slice
    }

    /// Return a mutable reference to the header `Writer` of the packet.
    pub fn header_slice(&mut self) -> &mut Writer<'a, B> {
        &mut self.header_slice
    }

    /// Create the packet wrapper from an RX chain.
    ///
    /// The writable portion of the chain must be large enough to hold at least a packet header
    /// and some data.
    ///
    /// # Arguments
    ///
    /// * `mem` - the `GuestMemory` object that can be used to access the queue buffers.
    /// * `desc_chain` - the descriptor chain corresponding to a packet.
    /// * `max_data_size` - the maximum size allowed for the packet payload, that was negotiated
    ///   between the device and the driver. Tracking issue for defining this feature in virtio-spec
    ///   [here](https://github.com/oasis-tcs/virtio-spec/issues/140).
    ///
    /// # Example
    ///
    /// ```rust
    /// # use virtio_bindings::bindings::virtio_ring::VRING_DESC_F_WRITE;
    /// # use virtio_queue::mock::MockSplitQueue;
    /// # use virtio_queue::{desc::{split::Descriptor as SplitDescriptor, RawDescriptor}, Queue, QueueT};
    /// # use virtio_vsock::packet_rw::{VsockPacketRx};
    /// # use virtio_vsock::{PKT_HEADER_SIZE, PacketHeader};
    /// # use vm_memory::{Bytes, GuestAddress, GuestAddressSpace, GuestMemoryMmap};
    ///
    /// # use std::io::Write;
    ///
    /// # const MAX_PKT_BUF_SIZE: u32 = 64 * 1024;
    /// # const SRC_CID: u64 = 1;
    /// # const DST_CID: u64 = 2;
    /// # const SRC_PORT: u32 = 3;
    /// # const DST_PORT: u32 = 4;
    /// # const LEN: u32 = 16;
    /// # const TYPE_STREAM: u16 = 1;
    /// # const OP_RW: u16 = 5;
    /// # const FLAGS: u32 = 7;
    /// # const FLAG: u32 = 8;
    /// # const BUF_ALLOC: u32 = 256;
    /// # const FWD_CNT: u32 = 9;
    ///
    /// # fn create_queue_with_chain(m: &GuestMemoryMmap) -> Queue {
    /// #     let vq = MockSplitQueue::new(m, 16);
    /// #     let mut q = vq.create_queue().unwrap();
    /// #
    /// #     let v = vec![
    /// #         RawDescriptor::from(SplitDescriptor::new(0x5_0000, 0x100, VRING_DESC_F_WRITE as u16, 0)),
    /// #         RawDescriptor::from(SplitDescriptor::new(0x8_0000, 0x100, VRING_DESC_F_WRITE as u16, 0)),
    /// #     ];
    /// #     let mut chain = vq.build_desc_chain(&v);
    /// #    q
    /// # }
    /// let mem = GuestMemoryMmap::<()>::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap();
    /// // Create a queue and populate it with a descriptor chain.
    /// let mut queue = create_queue_with_chain(&mem);
    ///
    /// while let Some(head) = queue.pop_descriptor_chain(&mem) {
    ///     let head_index = head.head_index();
    ///     let used_len = match VsockPacketRx::from_rx_virtq_chain(&mem, head, MAX_PKT_BUF_SIZE) {
    ///         Ok(mut pkt) => {
    ///             // Make sure the header is zeroed out first.
    ///             let mut header = PacketHeader::default();
    ///             header.set_src_cid(SRC_CID)
    ///                 .set_dst_cid(DST_CID)
    ///                 .set_src_port(SRC_PORT)
    ///                 .set_dst_port(DST_PORT)
    ///                 .set_type(TYPE_STREAM)
    ///                 .set_buf_alloc(BUF_ALLOC)
    ///                 .set_fwd_cnt(FWD_CNT)
    ///                 .set_op(OP_RW)
    ///                 .set_len(LEN);
    ///             pkt.header_slice().write_obj(header).unwrap();
    ///             // In this example, we are sending a RW packet.
    ///             pkt.data_slice()
    ///                 .write(&[1u8; LEN as usize]).unwrap();
    ///             size_of::<PacketHeader>() as u32 + LEN
    ///         }
    ///         Err(_e) => {
    ///             // Do some error handling.
    ///             0
    ///         }
    ///     };
    ///     queue.add_used(&mem, head_index, used_len);
    /// }
    /// ```
    pub fn from_rx_virtq_chain<M, T>(
        mem: &'a M,
        desc_chain: DescriptorChain<T>,
        max_data_size: u32,
    ) -> Result<Self>
    where
        M: GuestMemory,
        <M as GuestMemory>::Bitmap: WithBitmapSlice<'a, S = B>,
        T: Deref<Target = M>,
        T::Target: GuestMemory,
    {
        let mut header_writer = desc_chain.writer(mem).map_err(|_| Error::InvalidChain)?;

        if header_writer.available_bytes() == 0 {
            return Err(Error::InvalidChain);
        }

        let data_writer = header_writer
            .split_at(PKT_HEADER_SIZE)
            .map_err(|_| Error::DescriptorLengthTooSmall)?;

        if data_writer.available_bytes() as u32 > max_data_size {
            return Err(Error::DescriptorLengthTooLong);
        }

        if data_writer.available_bytes() == 0 {
            return Err(Error::DescriptorLengthTooSmall);
        }

        Ok(Self {
            header_slice: header_writer,
            data_slice: data_writer,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use vm_memory::{Bytes, GuestAddress, GuestMemoryMmap};

    use virtio_bindings::bindings::virtio_ring::VRING_DESC_F_WRITE;
    use virtio_queue::desc::{split::Descriptor as SplitDescriptor, RawDescriptor};
    use virtio_queue::mock::MockSplitQueue;

    const SRC_CID: u64 = 1;
    const DST_CID: u64 = 2;
    const SRC_PORT: u32 = 3;
    const DST_PORT: u32 = 4;
    const LEN: u32 = 16;
    const TYPE: u16 = 5;
    const OP: u16 = 6;
    const FLAGS: u32 = 7;
    const FLAG: u32 = 8;
    const BUF_ALLOC: u32 = 256;
    const FWD_CNT: u32 = 9;

    const MAX_PKT_BUF_SIZE: u32 = 64 * 1024;

    #[test]
    fn test_from_rx_virtq_chain() {
        let mem: GuestMemoryMmap =
            GuestMemoryMmap::from_ranges(&[(GuestAddress(0), 0x1000_0000)]).unwrap();

        // The `build_desc_chain` function will populate the `NEXT` related flags and field.
        let v = vec![
            // A device-readable packet header descriptor should be invalid.
            RawDescriptor::from(SplitDescriptor::new(0x10_0000, 0x100, 0, 0)),
            RawDescriptor::from(SplitDescriptor::new(0x10_0000, 0x100, 0, 0)),
        ];
        let queue = MockSplitQueue::new(&mem, 16);
        let chain = queue.build_desc_chain(&v).unwrap();

        assert_eq!(
            VsockPacketRx::from_rx_virtq_chain(&mem, chain, MAX_PKT_BUF_SIZE).unwrap_err(),
            Error::InvalidChain
        );

        let v = vec![
            // A header length < PKT_HEADER_SIZE is invalid.
            RawDescriptor::from(SplitDescriptor::new(
                0x10_0000,
                PKT_HEADER_SIZE as u32 - 1,
                VRING_DESC_F_WRITE as u16,
                0,
            )),
        ];
        let chain = queue.build_desc_chain(&v).unwrap();
        assert_eq!(
            VsockPacketRx::from_rx_virtq_chain(&mem, chain, MAX_PKT_BUF_SIZE).unwrap_err(),
            Error::DescriptorLengthTooSmall
        );

        let v = vec![
            RawDescriptor::from(SplitDescriptor::new(
                0x10_0000,
                PKT_HEADER_SIZE as u32,
                VRING_DESC_F_WRITE as u16,
                0,
            )),
            RawDescriptor::from(SplitDescriptor::new(
                0x20_0000,
                MAX_PKT_BUF_SIZE + 1,
                VRING_DESC_F_WRITE as u16,
                0,
            )),
        ];
        let chain = queue.build_desc_chain(&v).unwrap();
        assert_eq!(
            VsockPacketRx::from_rx_virtq_chain(&mem, chain, MAX_PKT_BUF_SIZE).unwrap_err(),
            Error::DescriptorLengthTooLong
        );

        let v = vec![
            // The data descriptor should always be present on the RX path.
            RawDescriptor::from(SplitDescriptor::new(
                0x10_0000,
                PKT_HEADER_SIZE as u32,
                VRING_DESC_F_WRITE as u16,
                0,
            )),
        ];
        let chain = queue.build_desc_chain(&v).unwrap();
        assert_eq!(
            VsockPacketRx::from_rx_virtq_chain(&mem, chain, MAX_PKT_BUF_SIZE).unwrap_err(),
            Error::DescriptorLengthTooSmall
        );

        let v = vec![RawDescriptor::from(SplitDescriptor::new(
            0x20_0000, 0x100, 0, 0,
        ))];
        let chain = queue.build_desc_chain(&v).unwrap();
        assert_eq!(
            VsockPacketRx::from_rx_virtq_chain(&mem, chain, MAX_PKT_BUF_SIZE).unwrap_err(),
            Error::InvalidChain
        );

        let mem: GuestMemoryMmap =
            GuestMemoryMmap::from_ranges(&[(GuestAddress(0), 0x10_0004)]).unwrap();

        let v = vec![
            // The header doesn't fit entirely in the memory bounds.
            RawDescriptor::from(SplitDescriptor::new(
                0x10_0000,
                0x100,
                VRING_DESC_F_WRITE as u16,
                0,
            )),
            RawDescriptor::from(SplitDescriptor::new(
                0x20_0000,
                0x100,
                VRING_DESC_F_WRITE as u16,
                0,
            )),
        ];
        let queue = MockSplitQueue::new(&mem, 16);
        let chain = queue.build_desc_chain(&v).unwrap();
        assert_eq!(
            VsockPacketRx::from_rx_virtq_chain(&mem, chain, MAX_PKT_BUF_SIZE).unwrap_err(),
            Error::InvalidChain
        );

        let v = vec![
            // The header is outside the memory bounds.
            RawDescriptor::from(SplitDescriptor::new(
                0x20_0000,
                0x100,
                VRING_DESC_F_WRITE as u16,
                0,
            )),
            RawDescriptor::from(SplitDescriptor::new(
                0x30_0000,
                0x100,
                VRING_DESC_F_WRITE as u16,
                0,
            )),
        ];
        let chain = queue.build_desc_chain(&v).unwrap();
        assert_eq!(
            VsockPacketRx::from_rx_virtq_chain(&mem, chain, MAX_PKT_BUF_SIZE).unwrap_err(),
            Error::InvalidChain
        );

        let v = vec![
            RawDescriptor::from(SplitDescriptor::new(
                0x5_0000,
                0x100,
                VRING_DESC_F_WRITE as u16,
                0,
            )),
            // The data array doesn't fit entirely in the memory bounds.
            RawDescriptor::from(SplitDescriptor::new(
                0x10_0000,
                0x100,
                VRING_DESC_F_WRITE as u16,
                0,
            )),
        ];

        let chain = queue.build_desc_chain(&v).unwrap();
        assert_eq!(
            VsockPacketRx::from_rx_virtq_chain(&mem, chain, MAX_PKT_BUF_SIZE).unwrap_err(),
            Error::InvalidChain
        );

        let v = vec![
            RawDescriptor::from(SplitDescriptor::new(
                0x5_0000,
                0x100,
                VRING_DESC_F_WRITE as u16,
                0,
            )),
            // The data array is outside the memory bounds.
            RawDescriptor::from(SplitDescriptor::new(
                0x20_0000,
                0x100,
                VRING_DESC_F_WRITE as u16,
                0,
            )),
        ];
        let chain = queue.build_desc_chain(&v).unwrap();
        assert_eq!(
            VsockPacketRx::from_rx_virtq_chain(&mem, chain, MAX_PKT_BUF_SIZE).unwrap_err(),
            Error::InvalidChain
        );

        // Let's also test a valid descriptor chain.
        let v = vec![
            RawDescriptor::from(SplitDescriptor::new(
                0x5_0000,
                0x100,
                VRING_DESC_F_WRITE as u16,
                0,
            )),
            RawDescriptor::from(SplitDescriptor::new(
                0x8_0000,
                0x100,
                VRING_DESC_F_WRITE as u16,
                0,
            )),
        ];
        let chain = queue.build_desc_chain(&v).unwrap();

        let mut packet = VsockPacketRx::from_rx_virtq_chain(&mem, chain, MAX_PKT_BUF_SIZE).unwrap();

        assert_eq!(packet.header_slice().available_bytes(), PKT_HEADER_SIZE);
        assert_eq!(
            packet.data_slice().available_bytes(),
            0x200 - PKT_HEADER_SIZE
        );

        // Let's also test a valid descriptor chain, with both header and data on a single
        // descriptor.
        let v = vec![RawDescriptor::from(SplitDescriptor::new(
            0x5_0000,
            PKT_HEADER_SIZE as u32 + 0x100,
            VRING_DESC_F_WRITE as u16,
            0,
        ))];
        let chain = queue.build_desc_chain(&v).unwrap();

        let mut packet = VsockPacketRx::from_rx_virtq_chain(&mem, chain, MAX_PKT_BUF_SIZE).unwrap();
        let header = packet.header_slice();
        assert_eq!(header.available_bytes(), PKT_HEADER_SIZE);
        assert_eq!(packet.data_slice().available_bytes(), 0x100);
    }

    #[test]
    fn test_from_tx_virtq_chain() {
        let mem: GuestMemoryMmap =
            GuestMemoryMmap::from_ranges(&[(GuestAddress(0), 0x1000_0000)]).unwrap();

        // The `build_desc_chain` function will populate the `NEXT` related flags and field.
        let v = vec![
            // A device-writable packet header descriptor should be invalid.
            RawDescriptor::from(SplitDescriptor::new(
                0x10_0000,
                0x100,
                VRING_DESC_F_WRITE as u16,
                0,
            )),
        ];
        let queue = MockSplitQueue::new(&mem, 16);
        let chain = queue.build_desc_chain(&v).unwrap();
        assert_eq!(
            VsockPacketTx::from_tx_virtq_chain(&mem, chain, MAX_PKT_BUF_SIZE).unwrap_err(),
            Error::DescriptorLengthTooSmall
        );

        let v = vec![
            // A header length < PKT_HEADER_SIZE is invalid.
            RawDescriptor::from(SplitDescriptor::new(
                0x10_0000,
                PKT_HEADER_SIZE as u32 - 1,
                0,
                0,
            )),
        ];
        let chain = queue.build_desc_chain(&v).unwrap();
        assert_eq!(
            VsockPacketTx::from_tx_virtq_chain(&mem, chain, MAX_PKT_BUF_SIZE).unwrap_err(),
            Error::DescriptorLengthTooSmall
        );

        // On the TX path, it is allowed to not have a data descriptor.
        let v = vec![RawDescriptor::from(SplitDescriptor::new(
            0x10_0000,
            PKT_HEADER_SIZE as u32,
            0,
            0,
        ))];
        let chain = queue.build_desc_chain(&v).unwrap();

        let mut header = PacketHeader::default();
        header
            .set_src_cid(SRC_CID)
            .set_dst_cid(DST_CID)
            .set_src_port(SRC_PORT)
            .set_dst_port(DST_PORT);
        mem.write_obj(header, GuestAddress(0x10_0000)).unwrap();

        let packet = VsockPacketTx::from_tx_virtq_chain(&mem, chain, MAX_PKT_BUF_SIZE).unwrap();
        assert_eq!(*packet.header(), header);
        assert!(packet.data_slice().is_none());

        let mem: GuestMemoryMmap =
            GuestMemoryMmap::from_ranges(&[(GuestAddress(0), 0x10_0004)]).unwrap();

        let v = vec![
            // The header doesn't fit entirely in the memory bounds.
            RawDescriptor::from(SplitDescriptor::new(0x10_0000, 0x100, 0, 0)),
            RawDescriptor::from(SplitDescriptor::new(0x20_0000, 0x100, 0, 0)),
        ];
        let queue = MockSplitQueue::new(&mem, 16);
        let chain = queue.build_desc_chain(&v).unwrap();
        assert_eq!(
            VsockPacketTx::from_tx_virtq_chain(&mem, chain, MAX_PKT_BUF_SIZE).unwrap_err(),
            Error::InvalidChain
        );

        let v = vec![
            // The header is outside the memory bounds.
            RawDescriptor::from(SplitDescriptor::new(0x20_0000, 0x100, 0, 0)),
            RawDescriptor::from(SplitDescriptor::new(0x30_0000, 0x100, 0, 0)),
        ];
        let chain = queue.build_desc_chain(&v).unwrap();
        assert_eq!(
            VsockPacketTx::from_tx_virtq_chain(&mem, chain, MAX_PKT_BUF_SIZE).unwrap_err(),
            Error::InvalidChain
        );

        // Write some non-zero value to the `len` field of the header, which means there is also
        // a data descriptor in the chain, first with a value that exceeds the maximum allowed one.
        let mut header = PacketHeader::default();
        header
            .set_src_cid(SRC_CID)
            .set_dst_cid(DST_CID)
            .set_src_port(SRC_PORT)
            .set_dst_port(DST_PORT)
            .set_len(MAX_PKT_BUF_SIZE + 1);
        mem.write_obj(header, GuestAddress(0x5_0000)).unwrap();
        let v = vec![
            RawDescriptor::from(SplitDescriptor::new(0x5_0000, 0x100, 0, 0)),
            RawDescriptor::from(SplitDescriptor::new(0x8_0000, 0x100, 0, 0)),
        ];
        let chain = queue.build_desc_chain(&v).unwrap();
        assert_eq!(
            VsockPacketTx::from_tx_virtq_chain(&mem, chain, MAX_PKT_BUF_SIZE).unwrap_err(),
            Error::InvalidHeaderLen(MAX_PKT_BUF_SIZE + 1)
        );

        // Write some non-zero, valid value to the `len` field of the header.
        let mut header = PacketHeader::default();
        header
            .set_src_cid(SRC_CID)
            .set_dst_cid(DST_CID)
            .set_src_port(SRC_PORT)
            .set_dst_port(DST_PORT)
            .set_len(LEN);
        mem.write_obj(header, GuestAddress(0x5_0000)).unwrap();
        let v = vec![
            // No room for data.
            RawDescriptor::from(SplitDescriptor::new(0x5_0000, PKT_HEADER_SIZE as u32, 0, 0)),
        ];
        let chain = queue.build_desc_chain(&v).unwrap();

        assert_eq!(
            VsockPacketTx::from_tx_virtq_chain(&mem, chain, MAX_PKT_BUF_SIZE).unwrap_err(),
            Error::DescriptorLengthTooSmall
        );

        let v = vec![
            RawDescriptor::from(SplitDescriptor::new(0x5_0000, 0x100, 0, 0)),
            // The data array doesn't fit entirely in the memory bounds.
            RawDescriptor::from(SplitDescriptor::new(0x10_0000, 0x100, 0, 0)),
        ];
        let chain = queue.build_desc_chain(&v).unwrap();

        assert_eq!(
            VsockPacketTx::from_tx_virtq_chain(&mem, chain, MAX_PKT_BUF_SIZE).unwrap_err(),
            Error::InvalidChain
        );

        let v = vec![
            RawDescriptor::from(SplitDescriptor::new(0x5_0000, 0x100, 0, 0)),
            // The data array is outside the memory bounds.
            RawDescriptor::from(SplitDescriptor::new(0x20_0000, 0x100, 0, 0)),
        ];
        let chain = queue.build_desc_chain(&v).unwrap();

        assert_eq!(
            VsockPacketTx::from_tx_virtq_chain(&mem, chain, MAX_PKT_BUF_SIZE).unwrap_err(),
            Error::InvalidChain
        );

        let v = vec![
            RawDescriptor::from(SplitDescriptor::new(0x5_0000, PKT_HEADER_SIZE as u32, 0, 0)),
            // A data length < the length of data as described by the header.
            RawDescriptor::from(SplitDescriptor::new(0x8_0000, LEN - 1, 0, 0)),
        ];
        let chain = queue.build_desc_chain(&v).unwrap();
        assert_eq!(
            VsockPacketTx::from_tx_virtq_chain(&mem, chain, MAX_PKT_BUF_SIZE).unwrap_err(),
            Error::DescriptorLengthTooSmall
        );

        // Let's also test a valid descriptor chain, with both header and data.
        let v = vec![
            RawDescriptor::from(SplitDescriptor::new(0x5_0000, 0x100, 0, 0)),
            RawDescriptor::from(SplitDescriptor::new(0x8_0000, 0x100, 0, 0)),
        ];
        let chain = queue.build_desc_chain(&v).unwrap();

        let packet = VsockPacketTx::from_tx_virtq_chain(&mem, chain, MAX_PKT_BUF_SIZE).unwrap();
        assert_eq!(*packet.header(), header);

        // The `len` field of the header was set to 16.
        assert_eq!(packet.header().len(), LEN);

        let data = packet.data_slice().unwrap();
        assert_eq!(data.available_bytes(), LEN as usize);

        // Let's also test a valid descriptor chain, with both header and data on a single
        // descriptor.
        let v = vec![RawDescriptor::from(SplitDescriptor::new(
            0x5_0000,
            PKT_HEADER_SIZE as u32 + 0x100,
            0,
            0,
        ))];
        let chain = queue.build_desc_chain(&v).unwrap();

        let packet = VsockPacketTx::from_tx_virtq_chain(&mem, chain, MAX_PKT_BUF_SIZE).unwrap();
        assert_eq!(*packet.header(), header);
        // The `len` field of the header was set to 16.
        assert_eq!(packet.header().len(), LEN);

        let data = packet.data_slice().unwrap();
        assert_eq!(data.available_bytes(), LEN as usize);
    }

    #[test]
    fn test_header_set_get() {
        let mem: GuestMemoryMmap =
            GuestMemoryMmap::from_ranges(&[(GuestAddress(0), 0x30_0000)]).unwrap();
        // The `build_desc_chain` function will populate the `NEXT` related flags and field.
        let v = vec![
            RawDescriptor::from(SplitDescriptor::new(
                0x10_0000,
                0x100,
                VRING_DESC_F_WRITE as u16,
                0,
            )),
            RawDescriptor::from(SplitDescriptor::new(
                0x20_0000,
                0x100,
                VRING_DESC_F_WRITE as u16,
                0,
            )),
        ];
        let queue = MockSplitQueue::new(&mem, 16);
        let chain = queue.build_desc_chain(&v).unwrap();

        let mut packet = VsockPacketRx::from_rx_virtq_chain(&mem, chain, MAX_PKT_BUF_SIZE).unwrap();

        let mut header = PacketHeader::default();
        header
            .set_src_cid(SRC_CID)
            .set_dst_cid(DST_CID)
            .set_src_port(SRC_PORT)
            .set_dst_port(DST_PORT)
            .set_len(LEN)
            .set_type(TYPE)
            .set_op(OP)
            .set_flags(FLAGS)
            .set_flag(FLAG)
            .set_buf_alloc(BUF_ALLOC)
            .set_fwd_cnt(FWD_CNT);

        // Verify PacketHeader getters.
        assert_eq!(header.src_cid(), SRC_CID);
        assert_eq!(header.dst_cid(), DST_CID);
        assert_eq!(header.src_port(), SRC_PORT);
        assert_eq!(header.dst_port(), DST_PORT);
        assert_eq!(header.len(), LEN);
        assert_eq!(header.type_(), TYPE);
        assert_eq!(header.op(), OP);
        assert_eq!(header.flags(), FLAGS | FLAG);
        assert_eq!(header.buf_alloc(), BUF_ALLOC);
        assert_eq!(header.fwd_cnt(), FWD_CNT);

        // Write header through the Writer, then read back from guest memory.
        packet.header_slice().write_obj(header).unwrap();

        let read_back: PacketHeader = mem.read_obj(GuestAddress(0x10_0000)).unwrap();
        assert_eq!(read_back, header);

        // Offsets of the header fields.
        const SRC_CID_OFFSET: u64 = 0;
        const DST_CID_OFFSET: u64 = 8;
        const SRC_PORT_OFFSET: u64 = 16;
        const DST_PORT_OFFSET: u64 = 20;
        const LEN_OFFSET: u64 = 24;
        const TYPE_OFFSET: u64 = 28;
        const OP_OFFSET: u64 = 30;
        const FLAGS_OFFSET: u64 = 32;
        const BUF_ALLOC_OFFSET: u64 = 36;
        const FWD_CNT_OFFSET: u64 = 40;

        let base = 0x10_0000;
        assert_eq!(
            u64::from_le(
                mem.read_obj::<u64>(GuestAddress(base + SRC_CID_OFFSET))
                    .unwrap()
            ),
            SRC_CID
        );
        assert_eq!(
            u64::from_le(
                mem.read_obj::<u64>(GuestAddress(base + DST_CID_OFFSET))
                    .unwrap()
            ),
            DST_CID
        );
        assert_eq!(
            u32::from_le(
                mem.read_obj::<u32>(GuestAddress(base + SRC_PORT_OFFSET))
                    .unwrap()
            ),
            SRC_PORT
        );
        assert_eq!(
            u32::from_le(
                mem.read_obj::<u32>(GuestAddress(base + DST_PORT_OFFSET))
                    .unwrap()
            ),
            DST_PORT
        );
        assert_eq!(
            u32::from_le(
                mem.read_obj::<u32>(GuestAddress(base + LEN_OFFSET))
                    .unwrap()
            ),
            LEN
        );
        assert_eq!(
            u16::from_le(
                mem.read_obj::<u16>(GuestAddress(base + TYPE_OFFSET))
                    .unwrap()
            ),
            TYPE
        );
        assert_eq!(
            u16::from_le(mem.read_obj::<u16>(GuestAddress(base + OP_OFFSET)).unwrap()),
            OP
        );
        assert_eq!(
            u32::from_le(
                mem.read_obj::<u32>(GuestAddress(base + FLAGS_OFFSET))
                    .unwrap()
            ),
            FLAGS | FLAG
        );
        assert_eq!(
            u32::from_le(
                mem.read_obj::<u32>(GuestAddress(base + BUF_ALLOC_OFFSET))
                    .unwrap()
            ),
            BUF_ALLOC
        );
        assert_eq!(
            u32::from_le(
                mem.read_obj::<u32>(GuestAddress(base + FWD_CNT_OFFSET))
                    .unwrap()
            ),
            FWD_CNT
        );
    }
}
