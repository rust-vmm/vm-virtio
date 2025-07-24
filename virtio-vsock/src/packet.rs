// Copyright 2022 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

//! Vsock packet abstraction.
//!
//! This module provides the following abstraction for parsing a vsock packet, and working with it:
//!
//! - [`VsockPacket`](struct.VsockPacket.html) which handles the parsing of the vsock packet from
//! either a TX descriptor chain via
//! [`VsockPacket::from_tx_virtq_chain`](struct.VsockPacket.html#method.from_tx_virtq_chain), or an
//! RX descriptor chain via
//! [`VsockPacket::from_rx_virtq_chain`](struct.VsockPacket.html#method.from_rx_virtq_chain).
//! The virtio vsock packet is defined in the standard as having a header of type `virtio_vsock_hdr`
//! and an optional `data` array of bytes. The methods mentioned above assume that both packet
//! elements are on the same descriptor, or each of the packet elements occupies exactly one
//! descriptor. For the usual drivers, this assumption stands,
//! but in the future we might make the implementation more generic by removing any constraint
//! regarding the number of descriptors that correspond to the header/data. The buffers associated
//! to the TX virtio queue are device-readable, and the ones associated to the RX virtio queue are
//! device-writable.
///
/// The `VsockPacket` abstraction is using vm-memory's `VolatileSlice` for representing the header
/// and the data. `VolatileSlice` is a safe wrapper over a raw pointer, which also handles the dirty
/// page tracking behind the scenes. A limitation of the current implementation is that it does not
/// cover the scenario where the header or data buffer doesn't fit in a single `VolatileSlice`
/// because the guest memory regions of the buffer are contiguous in the guest physical address
/// space, but not in the host virtual one as well. If this becomes an use case, we can extend this
/// solution to use an array of `VolatileSlice`s for the header and data.
/// The `VsockPacket` abstraction is also storing a `virtio_vsock_hdr` instance (which is defined
/// here as `PacketHeader`). This is needed so that we always access the same data that was read the
/// first time from the descriptor chain. We avoid this way potential time-of-check time-of-use
/// problems that may occur when reading later a header field from the underlying memory itself
/// (i.e. from the header's `VolatileSlice` object).
use std::fmt::{self, Display};
use std::ops::Deref;

use virtio_queue::DescriptorChain;
use vm_memory::bitmap::{BitmapSlice, WithBitmapSlice};
use vm_memory::{
    Address, ByteValued, Bytes, GuestMemory, GuestMemoryError, GuestMemoryRegion, Le16, Le32, Le64,
    VolatileMemoryError, VolatileSlice,
};

/// Vsock packet parsing errors.
#[derive(Debug)]
pub enum Error {
    /// Too few descriptors in a descriptor chain.
    DescriptorChainTooShort,
    /// Descriptor that was too short to use.
    DescriptorLengthTooSmall,
    /// Descriptor that was too long to use.
    DescriptorLengthTooLong,
    /// The slice for creating a header has an invalid length.
    InvalidHeaderInputSize(usize),
    /// The `len` header field value exceeds the maximum allowed data size.
    InvalidHeaderLen(u32),
    /// Invalid guest memory access.
    InvalidMemoryAccess(GuestMemoryError),
    /// Invalid volatile memory access.
    InvalidVolatileAccess(VolatileMemoryError),
    /// Read only descriptor that protocol says to write to.
    UnexpectedReadOnlyDescriptor,
    /// Write only descriptor that protocol says to read from.
    UnexpectedWriteOnlyDescriptor,
}

impl std::error::Error for Error {}

impl Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::DescriptorChainTooShort => {
                write!(f, "There are not enough descriptors in the chain.")
            }
            Error::DescriptorLengthTooSmall => write!(
                f,
                "The descriptor is pointing to a buffer that has a smaller length than expected."
            ),
            Error::DescriptorLengthTooLong => write!(
                f,
                "The descriptor is pointing to a buffer that has a longer length than expected."
            ),
            Error::InvalidHeaderInputSize(size) => {
                write!(f, "Invalid header input size: {size}")
            }
            Error::InvalidHeaderLen(size) => {
                write!(f, "Invalid header `len` field value: {size}")
            }
            Error::InvalidMemoryAccess(error) => {
                write!(f, "Invalid guest memory access: {error}")
            }
            Error::InvalidVolatileAccess(error) => {
                write!(f, "Invalid volatile memory access: {error}")
            }
            Error::UnexpectedReadOnlyDescriptor => {
                write!(f, "Unexpected read-only descriptor.")
            }
            Error::UnexpectedWriteOnlyDescriptor => {
                write!(f, "Unexpected write-only descriptor.")
            }
        }
    }
}

#[repr(C, packed)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
/// The vsock packet header structure.
pub struct PacketHeader {
    src_cid: Le64,
    dst_cid: Le64,
    src_port: Le32,
    dst_port: Le32,
    len: Le32,
    type_: Le16,
    op: Le16,
    flags: Le32,
    buf_alloc: Le32,
    fwd_cnt: Le32,
}

// SAFETY: This is safe because `PacketHeader` contains only wrappers over POD types
// and all accesses through safe `vm-memory` API will validate any garbage that could
// be included in there.
unsafe impl ByteValued for PacketHeader {}
//
// This structure will occupy the buffer pointed to by the head of the descriptor chain. Below are
// the offsets for each field, as well as the packed structure size.
// Note that these offsets are only used privately by the `VsockPacket` struct, the public interface
// consisting of getter and setter methods, for each struct field, that will also handle the correct
// endianness.

/// The size of the header structure (when packed).
pub const PKT_HEADER_SIZE: usize = std::mem::size_of::<PacketHeader>();

// Offsets of the header fields.
const SRC_CID_OFFSET: usize = 0;
const DST_CID_OFFSET: usize = 8;
const SRC_PORT_OFFSET: usize = 16;
const DST_PORT_OFFSET: usize = 20;
const LEN_OFFSET: usize = 24;
const TYPE_OFFSET: usize = 28;
const OP_OFFSET: usize = 30;
const FLAGS_OFFSET: usize = 32;
const BUF_ALLOC_OFFSET: usize = 36;
const FWD_CNT_OFFSET: usize = 40;

/// Dedicated [`Result`](https://doc.rust-lang.org/std/result/) type.
pub type Result<T> = std::result::Result<T, Error>;

/// The vsock packet, implemented as a wrapper over a virtio descriptor chain:
/// - the chain head, holding the packet header;
/// - an optional data/buffer descriptor, only present for data packets (for VSOCK_OP_RW requests).
#[derive(Debug)]
pub struct VsockPacket<'a, B: BitmapSlice> {
    // When writing to the header slice, we are using the `write` method of `VolatileSlice`s Bytes
    // implementation. Because that can only return an error if we pass an invalid offset, we can
    // safely use `unwraps` in the setters below. If we switch to a type different than
    // `VolatileSlice`, this assumption can no longer hold. We also must always make sure the
    // `VsockPacket` API is creating headers with PKT_HEADER_SIZE size.
    header_slice: VolatileSlice<'a, B>,
    header: PacketHeader,
    data_slice: Option<VolatileSlice<'a, B>>,
}

// This macro is intended to be used for setting a header field in both the `VolatileSlice` and the
// `PacketHeader` structure from a packet. `$offset` should be a valid offset in the `header_slice`,
// otherwise the macro will panic.
macro_rules! set_header_field {
    ($packet:ident, $field:ident, $offset:ident, $value:ident) => {
        $packet.header.$field = $value.into();
        $packet
            .header_slice
            .write(&$value.to_le_bytes(), $offset)
            // This unwrap is safe only if `$offset` is a valid offset in the `header_slice`.
            .unwrap();
    };
}

impl<'a, B: BitmapSlice> VsockPacket<'a, B> {
    /// Return a reference to the `header_slice` of the packet.
    pub fn header_slice(&self) -> &VolatileSlice<'a, B> {
        &self.header_slice
    }

    /// Return a reference to the `data_slice` of the packet.
    pub fn data_slice(&self) -> Option<&VolatileSlice<'a, B>> {
        self.data_slice.as_ref()
    }

    /// Write to the packet header from an input of raw bytes.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use virtio_bindings::bindings::virtio_ring::VRING_DESC_F_WRITE;
    /// # use virtio_queue::mock::MockSplitQueue;
    /// # use virtio_queue::{desc::{split::Descriptor as SplitDescriptor, RawDescriptor}, Queue, QueueT};
    /// use virtio_vsock::packet::{VsockPacket, PKT_HEADER_SIZE};
    /// # use vm_memory::{Bytes, GuestAddress, GuestAddressSpace, GuestMemoryMmap};
    ///
    /// const MAX_PKT_BUF_SIZE: u32 = 64 * 1024;
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
    /// #     q
    /// # }
    /// let mem = GuestMemoryMmap::<()>::from_ranges(&[(GuestAddress(0), 0x10_0000)]).unwrap();
    /// // Create a queue and populate it with a descriptor chain.
    /// let mut queue = create_queue_with_chain(&mem);
    ///
    /// while let Some(mut head) = queue.pop_descriptor_chain(&mem) {
    ///     let mut pkt = VsockPacket::from_rx_virtq_chain(&mem, &mut head, MAX_PKT_BUF_SIZE).unwrap();
    ///     pkt.set_header_from_raw(&[0u8; PKT_HEADER_SIZE]).unwrap();
    /// }
    /// ```
    pub fn set_header_from_raw(&mut self, bytes: &[u8]) -> Result<()> {
        if bytes.len() != PKT_HEADER_SIZE {
            return Err(Error::InvalidHeaderInputSize(bytes.len()));
        }
        self.header_slice
            .write(bytes, 0)
            .map_err(Error::InvalidVolatileAccess)?;
        let header = self
            .header_slice()
            .read_obj::<PacketHeader>(0)
            .map_err(Error::InvalidVolatileAccess)?;
        self.header = header;
        Ok(())
    }

    /// Return the `src_cid` of the header.
    pub fn src_cid(&self) -> u64 {
        self.header.src_cid.into()
    }

    /// Set the `src_cid` of the header.
    pub fn set_src_cid(&mut self, cid: u64) -> &mut Self {
        set_header_field!(self, src_cid, SRC_CID_OFFSET, cid);
        self
    }

    /// Return the `dst_cid` of the header.
    pub fn dst_cid(&self) -> u64 {
        self.header.dst_cid.into()
    }

    /// Set the `dst_cid` of the header.
    pub fn set_dst_cid(&mut self, cid: u64) -> &mut Self {
        set_header_field!(self, dst_cid, DST_CID_OFFSET, cid);
        self
    }

    /// Return the `src_port` of the header.
    pub fn src_port(&self) -> u32 {
        self.header.src_port.into()
    }

    /// Set the `src_port` of the header.
    pub fn set_src_port(&mut self, port: u32) -> &mut Self {
        set_header_field!(self, src_port, SRC_PORT_OFFSET, port);
        self
    }

    /// Return the `dst_port` of the header.
    pub fn dst_port(&self) -> u32 {
        self.header.dst_port.into()
    }

    /// Set the `dst_port` of the header.
    pub fn set_dst_port(&mut self, port: u32) -> &mut Self {
        set_header_field!(self, dst_port, DST_PORT_OFFSET, port);
        self
    }

    /// Return the `len` of the header.
    pub fn len(&self) -> u32 {
        self.header.len.into()
    }

    /// Returns whether the `len` field of the header is 0 or not.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Set the `len` of the header.
    pub fn set_len(&mut self, len: u32) -> &mut Self {
        set_header_field!(self, len, LEN_OFFSET, len);
        self
    }

    /// Return the `type` of the header.
    pub fn type_(&self) -> u16 {
        self.header.type_.into()
    }

    /// Set the `type` of the header.
    pub fn set_type(&mut self, type_: u16) -> &mut Self {
        set_header_field!(self, type_, TYPE_OFFSET, type_);
        self
    }

    /// Return the `op` of the header.
    pub fn op(&self) -> u16 {
        self.header.op.into()
    }

    /// Set the `op` of the header.
    pub fn set_op(&mut self, op: u16) -> &mut Self {
        set_header_field!(self, op, OP_OFFSET, op);
        self
    }

    /// Return the `flags` of the header.
    pub fn flags(&self) -> u32 {
        self.header.flags.into()
    }

    /// Set the `flags` of the header.
    pub fn set_flags(&mut self, flags: u32) -> &mut Self {
        set_header_field!(self, flags, FLAGS_OFFSET, flags);
        self
    }

    /// Set a specific flag of the header.
    pub fn set_flag(&mut self, flag: u32) -> &mut Self {
        self.set_flags(self.flags() | flag);
        self
    }

    /// Return the `buf_alloc` of the header.
    pub fn buf_alloc(&self) -> u32 {
        self.header.buf_alloc.into()
    }

    /// Set the `buf_alloc` of the header.
    pub fn set_buf_alloc(&mut self, buf_alloc: u32) -> &mut Self {
        set_header_field!(self, buf_alloc, BUF_ALLOC_OFFSET, buf_alloc);
        self
    }

    /// Return the `fwd_cnt` of the header.
    pub fn fwd_cnt(&self) -> u32 {
        self.header.fwd_cnt.into()
    }

    /// Set the `fwd_cnt` of the header.
    pub fn set_fwd_cnt(&mut self, fwd_cnt: u32) -> &mut Self {
        set_header_field!(self, fwd_cnt, FWD_CNT_OFFSET, fwd_cnt);
        self
    }

    /// Create the packet wrapper from a TX chain.
    ///
    /// The chain head is expected to hold a valid packet header. A following packet data
    /// descriptor can optionally end the chain.
    ///
    /// # Arguments
    ///
    /// * `mem` - the `GuestMemory` object that can be used to access the queue buffers.
    /// * `desc_chain` - the descriptor chain corresponding to a packet.
    /// * `max_data_size` - the maximum size allowed for the packet payload, that was negotiated between the device and the driver. Tracking issue for defining this feature in virtio-spec [here](https://github.com/oasis-tcs/virtio-spec/issues/140).
    ///
    /// # Example
    ///
    /// ```rust
    /// # use virtio_queue::mock::MockSplitQueue;
    /// # use virtio_queue::{desc::{split::Descriptor as SplitDescriptor, RawDescriptor}, Queue, QueueT};
    /// use virtio_vsock::packet::{VsockPacket, PKT_HEADER_SIZE};
    /// # use vm_memory::{Bytes, GuestAddress, GuestAddressSpace, GuestMemoryMmap};
    ///
    /// const MAX_PKT_BUF_SIZE: u32 = 64 * 1024;
    /// const OP_RW: u16 = 5;
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
    /// let mem = GuestMemoryMmap::<()>::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap();
    /// // Create a queue and populate it with a descriptor chain.
    /// let mut queue = create_queue_with_chain(&mem);
    ///
    /// while let Some(mut head) = queue.pop_descriptor_chain(&mem) {
    ///     let pkt = match VsockPacket::from_tx_virtq_chain(&mem, &mut head, MAX_PKT_BUF_SIZE) {
    ///         Ok(pkt) => pkt,
    ///         Err(_e) => {
    ///             // Do some error handling.
    ///             queue.add_used(&mem, head.head_index(), 0);
    ///             continue;
    ///         }
    ///     };
    ///     // Here we would send the packet to the backend. Depending on the operation type, a
    ///     // different type of action will be done.
    ///
    ///     // For example, if it's a RW packet, we will forward the packet payload to the backend.
    ///     if pkt.op() == OP_RW {
    ///         // Send the packet payload to the backend.
    ///     }
    ///     queue.add_used(&mem, head.head_index(), 0);
    /// }
    /// ```
    pub fn from_tx_virtq_chain<M, T>(
        mem: &'a M,
        desc_chain: &mut DescriptorChain<T>,
        max_data_size: u32,
    ) -> Result<Self>
    where
        M: GuestMemory,
        <<M as GuestMemory>::R as GuestMemoryRegion>::B: WithBitmapSlice<'a, S = B>,
        T: Deref,
        T::Target: GuestMemory,
    {
        let chain_head = desc_chain.next().ok_or(Error::DescriptorChainTooShort)?;
        // All TX buffers must be device-readable.
        if chain_head.is_write_only() {
            return Err(Error::UnexpectedWriteOnlyDescriptor);
        }

        // The packet header should fit inside the buffer corresponding to the head descriptor.
        if (chain_head.len() as usize) < PKT_HEADER_SIZE {
            return Err(Error::DescriptorLengthTooSmall);
        }

        let header_slice = mem
            .get_slice(chain_head.addr(), PKT_HEADER_SIZE)
            .map_err(Error::InvalidMemoryAccess)?;

        let header = mem
            .read_obj(chain_head.addr())
            .map_err(Error::InvalidMemoryAccess)?;

        let mut pkt = Self {
            header_slice,
            header,
            data_slice: None,
        };

        // If the `len` field of the header is zero, then the packet doesn't have a `data` element.
        if pkt.is_empty() {
            return Ok(pkt);
        }

        // Reject packets that exceed the maximum allowed value for payload.
        if pkt.len() > max_data_size {
            return Err(Error::InvalidHeaderLen(pkt.len()));
        }

        // Starting from Linux 6.2 the virtio-vsock driver can use a single descriptor for both
        // header and data.
        let data_slice =
            if !chain_head.has_next() && chain_head.len() - PKT_HEADER_SIZE as u32 >= pkt.len() {
                mem.get_slice(
                    chain_head
                        .addr()
                        .checked_add(PKT_HEADER_SIZE as u64)
                        .ok_or(Error::DescriptorLengthTooSmall)?,
                    pkt.len() as usize,
                )
                .map_err(Error::InvalidMemoryAccess)?
            } else {
                if !chain_head.has_next() {
                    return Err(Error::DescriptorChainTooShort);
                }

                let data_desc = desc_chain.next().ok_or(Error::DescriptorChainTooShort)?;

                if data_desc.is_write_only() {
                    return Err(Error::UnexpectedWriteOnlyDescriptor);
                }

                // The data buffer should be large enough to fit the size of the data, as described by
                // the header descriptor.
                if data_desc.len() < pkt.len() {
                    return Err(Error::DescriptorLengthTooSmall);
                }

                mem.get_slice(data_desc.addr(), pkt.len() as usize)
                    .map_err(Error::InvalidMemoryAccess)?
            };

        pkt.data_slice = Some(data_slice);
        Ok(pkt)
    }

    /// Create the packet wrapper from an RX chain.
    ///
    /// There must be two descriptors in the chain, both writable: a header descriptor and a data
    /// descriptor.
    ///
    /// # Arguments
    ///
    /// * `mem` - the `GuestMemory` object that can be used to access the queue buffers.
    /// * `desc_chain` - the descriptor chain corresponding to a packet.
    /// * `max_data_size` - the maximum size allowed for the packet payload, that was negotiated between the device and the driver. Tracking issue for defining this feature in virtio-spec [here](https://github.com/oasis-tcs/virtio-spec/issues/140).
    ///
    /// # Example
    ///
    /// ```rust
    /// # use virtio_bindings::bindings::virtio_ring::VRING_DESC_F_WRITE;
    /// # use virtio_queue::mock::MockSplitQueue;
    /// # use virtio_queue::{desc::{split::Descriptor as SplitDescriptor, RawDescriptor}, Queue, QueueT};
    /// use virtio_vsock::packet::{VsockPacket, PKT_HEADER_SIZE};
    /// # use vm_memory::{Bytes, GuestAddress, GuestAddressSpace, GuestMemoryMmap};
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
    /// while let Some(mut head) = queue.pop_descriptor_chain(&mem) {
    ///     let used_len = match VsockPacket::from_rx_virtq_chain(&mem, &mut head, MAX_PKT_BUF_SIZE) {
    ///         Ok(mut pkt) => {
    ///             // Make sure the header is zeroed out first.
    ///             pkt.header_slice()
    ///                 .write(&[0u8; PKT_HEADER_SIZE], 0)
    ///                 .unwrap();
    ///             // Write data to the packet, using the setters.
    ///             pkt.set_src_cid(SRC_CID)
    ///                 .set_dst_cid(DST_CID)
    ///                 .set_src_port(SRC_PORT)
    ///                 .set_dst_port(DST_PORT)
    ///                 .set_type(TYPE_STREAM)
    ///                 .set_buf_alloc(BUF_ALLOC)
    ///                 .set_fwd_cnt(FWD_CNT);
    ///             // In this example, we are sending a RW packet.
    ///             pkt.data_slice()
    ///                 .unwrap()
    ///                 .write_slice(&[1u8; LEN as usize], 0);
    ///             pkt.set_op(OP_RW).set_len(LEN);
    ///             pkt.header_slice().len() as u32 + LEN
    ///         }
    ///         Err(_e) => {
    ///             // Do some error handling.
    ///             0
    ///         }
    ///     };
    ///     queue.add_used(&mem, head.head_index(), used_len);
    /// }
    /// ```
    pub fn from_rx_virtq_chain<M, T>(
        mem: &'a M,
        desc_chain: &mut DescriptorChain<T>,
        max_data_size: u32,
    ) -> Result<Self>
    where
        M: GuestMemory,
        <<M as GuestMemory>::R as GuestMemoryRegion>::B: WithBitmapSlice<'a, S = B>,
        T: Deref,
        T::Target: GuestMemory,
    {
        let chain_head = desc_chain.next().ok_or(Error::DescriptorChainTooShort)?;
        // All RX buffers must be device-writable.
        if !chain_head.is_write_only() {
            return Err(Error::UnexpectedReadOnlyDescriptor);
        }

        // The packet header should fit inside the head descriptor.
        if (chain_head.len() as usize) < PKT_HEADER_SIZE {
            return Err(Error::DescriptorLengthTooSmall);
        }

        let header_slice = mem
            .get_slice(chain_head.addr(), PKT_HEADER_SIZE)
            .map_err(Error::InvalidMemoryAccess)?;

        // Starting from Linux 6.2 the virtio-vsock driver can use a single descriptor for both
        // header and data.
        let data_slice = if !chain_head.has_next() && chain_head.len() as usize > PKT_HEADER_SIZE {
            mem.get_slice(
                chain_head
                    .addr()
                    .checked_add(PKT_HEADER_SIZE as u64)
                    .ok_or(Error::DescriptorLengthTooSmall)?,
                chain_head.len() as usize - PKT_HEADER_SIZE,
            )
            .map_err(Error::InvalidMemoryAccess)?
        } else {
            if !chain_head.has_next() {
                return Err(Error::DescriptorChainTooShort);
            }

            let data_desc = desc_chain.next().ok_or(Error::DescriptorChainTooShort)?;

            if !data_desc.is_write_only() {
                return Err(Error::UnexpectedReadOnlyDescriptor);
            }

            if data_desc.len() > max_data_size {
                return Err(Error::DescriptorLengthTooLong);
            }

            mem.get_slice(data_desc.addr(), data_desc.len() as usize)
                .map_err(Error::InvalidMemoryAccess)?
        };

        Ok(Self {
            header_slice,
            header: Default::default(),
            data_slice: Some(data_slice),
        })
    }
}

impl<'a> VsockPacket<'a, ()> {
    /// Create a packet based on one pointer for the header, and an optional one for data.
    ///
    /// # Safety
    ///
    /// To use this safely, the caller must guarantee that the memory pointed to by the `hdr` and
    /// `data` slices is available for the duration of the lifetime of the new `VolatileSlice`. The
    /// caller must also guarantee that all other users of the given chunk of memory are using
    /// volatile accesses.
    ///
    /// # Example
    ///
    /// ```rust
    /// use virtio_vsock::packet::{VsockPacket, PKT_HEADER_SIZE};
    ///
    /// const LEN: usize = 16;
    ///
    /// let mut pkt_raw = [0u8; PKT_HEADER_SIZE + LEN];
    /// let (hdr_raw, data_raw) = pkt_raw.split_at_mut(PKT_HEADER_SIZE);
    /// // Safe because `hdr_raw` and `data_raw` live for as long as the scope of the current
    /// // example.
    /// let packet = unsafe { VsockPacket::new(hdr_raw, Some(data_raw)).unwrap() };
    /// ```
    pub unsafe fn new(header: &mut [u8], data: Option<&mut [u8]>) -> Result<VsockPacket<'a, ()>> {
        if header.len() != PKT_HEADER_SIZE {
            return Err(Error::InvalidHeaderInputSize(header.len()));
        }
        Ok(VsockPacket {
            header_slice: VolatileSlice::new(header.as_mut_ptr(), PKT_HEADER_SIZE),
            header: Default::default(),
            data_slice: data.map(|data| VolatileSlice::new(data.as_mut_ptr(), data.len())),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use vm_memory::{GuestAddress, GuestMemoryMmap};

    use virtio_bindings::bindings::virtio_ring::VRING_DESC_F_WRITE;
    use virtio_queue::desc::{split::Descriptor as SplitDescriptor, RawDescriptor};
    use virtio_queue::mock::MockSplitQueue;

    impl PartialEq for Error {
        fn eq(&self, other: &Self) -> bool {
            use self::Error::*;
            match (self, other) {
                (DescriptorChainTooShort, DescriptorChainTooShort) => true,
                (DescriptorLengthTooSmall, DescriptorLengthTooSmall) => true,
                (DescriptorLengthTooLong, DescriptorLengthTooLong) => true,
                (InvalidHeaderInputSize(size), InvalidHeaderInputSize(other_size)) => {
                    size == other_size
                }
                (InvalidHeaderLen(size), InvalidHeaderLen(other_size)) => size == other_size,
                (InvalidMemoryAccess(ref e), InvalidMemoryAccess(ref other_e)) => {
                    format!("{e}").eq(&format!("{other_e}"))
                }
                (InvalidVolatileAccess(ref e), InvalidVolatileAccess(ref other_e)) => {
                    format!("{e}").eq(&format!("{other_e}"))
                }
                (UnexpectedReadOnlyDescriptor, UnexpectedReadOnlyDescriptor) => true,
                (UnexpectedWriteOnlyDescriptor, UnexpectedWriteOnlyDescriptor) => true,
                _ => false,
            }
        }
    }

    // Random values to be used by the tests for the header fields.
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
            RawDescriptor::from(SplitDescriptor::new(
                0x20_0000,
                0x100,
                VRING_DESC_F_WRITE as u16,
                0,
            )),
        ];
        let queue = MockSplitQueue::new(&mem, 16);
        let mut chain = queue.build_desc_chain(&v).unwrap();
        assert_eq!(
            VsockPacket::from_rx_virtq_chain(&mem, &mut chain, MAX_PKT_BUF_SIZE).unwrap_err(),
            Error::UnexpectedReadOnlyDescriptor
        );

        let v = vec![
            // A header length < PKT_HEADER_SIZE is invalid.
            RawDescriptor::from(SplitDescriptor::new(
                0x10_0000,
                PKT_HEADER_SIZE as u32 - 1,
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
        let mut chain = queue.build_desc_chain(&v).unwrap();
        assert_eq!(
            VsockPacket::from_rx_virtq_chain(&mem, &mut chain, MAX_PKT_BUF_SIZE).unwrap_err(),
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
        let mut chain = queue.build_desc_chain(&v).unwrap();
        assert_eq!(
            VsockPacket::from_rx_virtq_chain(&mem, &mut chain, MAX_PKT_BUF_SIZE).unwrap_err(),
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
        let mut chain = queue.build_desc_chain(&v).unwrap();
        assert_eq!(
            VsockPacket::from_rx_virtq_chain(&mem, &mut chain, MAX_PKT_BUF_SIZE).unwrap_err(),
            Error::DescriptorChainTooShort
        );

        let v = vec![
            RawDescriptor::from(SplitDescriptor::new(0x10_0000, 0x100, 0, 0)),
            RawDescriptor::from(SplitDescriptor::new(
                0x20_0000,
                0x100,
                VRING_DESC_F_WRITE as u16,
                0,
            )),
        ];
        let mut chain = queue.build_desc_chain(&v).unwrap();
        assert_eq!(
            VsockPacket::from_rx_virtq_chain(&mem, &mut chain, MAX_PKT_BUF_SIZE).unwrap_err(),
            Error::UnexpectedReadOnlyDescriptor
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
        let mut chain = queue.build_desc_chain(&v).unwrap();
        assert_eq!(
            VsockPacket::from_rx_virtq_chain(&mem, &mut chain, MAX_PKT_BUF_SIZE).unwrap_err(),
            Error::InvalidMemoryAccess(GuestMemoryError::InvalidBackendAddress)
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
        let mut chain = queue.build_desc_chain(&v).unwrap();
        assert_eq!(
            VsockPacket::from_rx_virtq_chain(&mem, &mut chain, MAX_PKT_BUF_SIZE).unwrap_err(),
            Error::InvalidMemoryAccess(GuestMemoryError::InvalidGuestAddress(GuestAddress(
                0x20_0000
            )))
        );

        let v = vec![
            RawDescriptor::from(SplitDescriptor::new(
                0x5_0000,
                0x100,
                VRING_DESC_F_WRITE as u16,
                0,
            )),
            // A device-readable packet data descriptor should be invalid.
            RawDescriptor::from(SplitDescriptor::new(0x8_0000, 0x100, 0, 0)),
        ];
        let mut chain = queue.build_desc_chain(&v).unwrap();
        assert_eq!(
            VsockPacket::from_rx_virtq_chain(&mem, &mut chain, MAX_PKT_BUF_SIZE).unwrap_err(),
            Error::UnexpectedReadOnlyDescriptor
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
        let mut chain = queue.build_desc_chain(&v).unwrap();
        assert_eq!(
            VsockPacket::from_rx_virtq_chain(&mem, &mut chain, MAX_PKT_BUF_SIZE).unwrap_err(),
            Error::InvalidMemoryAccess(GuestMemoryError::InvalidBackendAddress)
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
        let mut chain = queue.build_desc_chain(&v).unwrap();
        assert_eq!(
            VsockPacket::from_rx_virtq_chain(&mem, &mut chain, MAX_PKT_BUF_SIZE).unwrap_err(),
            Error::InvalidMemoryAccess(GuestMemoryError::InvalidGuestAddress(GuestAddress(
                0x20_0000
            )))
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
        let mut chain = queue.build_desc_chain(&v).unwrap();

        let packet = VsockPacket::from_rx_virtq_chain(&mem, &mut chain, MAX_PKT_BUF_SIZE).unwrap();
        assert_eq!(packet.header, PacketHeader::default());
        let header = packet.header_slice();
        assert_eq!(
            header.ptr_guard().as_ptr(),
            mem.get_host_address(GuestAddress(0x5_0000)).unwrap()
        );
        assert_eq!(header.len(), PKT_HEADER_SIZE);

        let data = packet.data_slice().unwrap();
        assert_eq!(
            data.ptr_guard().as_ptr(),
            mem.get_host_address(GuestAddress(0x8_0000)).unwrap()
        );
        assert_eq!(data.len(), 0x100);

        // If we try to get a vsock packet again, it fails because we already consumed all the
        // descriptors from the chain.
        assert_eq!(
            VsockPacket::from_rx_virtq_chain(&mem, &mut chain, MAX_PKT_BUF_SIZE).unwrap_err(),
            Error::DescriptorChainTooShort
        );

        // Let's also test a valid descriptor chain, with both header and data on a single
        // descriptor.
        let v = vec![RawDescriptor::from(SplitDescriptor::new(
            0x5_0000,
            PKT_HEADER_SIZE as u32 + 0x100,
            VRING_DESC_F_WRITE as u16,
            0,
        ))];
        let mut chain = queue.build_desc_chain(&v).unwrap();

        let packet = VsockPacket::from_rx_virtq_chain(&mem, &mut chain, MAX_PKT_BUF_SIZE).unwrap();
        assert_eq!(packet.header, PacketHeader::default());
        let header = packet.header_slice();
        assert_eq!(
            header.ptr_guard().as_ptr(),
            mem.get_host_address(GuestAddress(0x5_0000)).unwrap()
        );
        assert_eq!(header.len(), PKT_HEADER_SIZE);

        let data = packet.data_slice().unwrap();
        assert_eq!(
            data.ptr_guard().as_ptr(),
            mem.get_host_address(GuestAddress(0x5_0000 + PKT_HEADER_SIZE as u64))
                .unwrap()
        );
        assert_eq!(data.len(), 0x100);
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
            RawDescriptor::from(SplitDescriptor::new(0x20_0000, 0x100, 0, 0)),
        ];
        let queue = MockSplitQueue::new(&mem, 16);
        let mut chain = queue.build_desc_chain(&v).unwrap();
        assert_eq!(
            VsockPacket::from_tx_virtq_chain(&mem, &mut chain, MAX_PKT_BUF_SIZE).unwrap_err(),
            Error::UnexpectedWriteOnlyDescriptor
        );

        let v = vec![
            // A header length < PKT_HEADER_SIZE is invalid.
            RawDescriptor::from(SplitDescriptor::new(
                0x10_0000,
                PKT_HEADER_SIZE as u32 - 1,
                0,
                0,
            )),
            RawDescriptor::from(SplitDescriptor::new(0x20_0000, 0x100, 0, 0)),
        ];
        let mut chain = queue.build_desc_chain(&v).unwrap();
        assert_eq!(
            VsockPacket::from_tx_virtq_chain(&mem, &mut chain, MAX_PKT_BUF_SIZE).unwrap_err(),
            Error::DescriptorLengthTooSmall
        );

        // On the TX path, it is allowed to not have a data descriptor.
        let v = vec![RawDescriptor::from(SplitDescriptor::new(
            0x10_0000,
            PKT_HEADER_SIZE as u32,
            0,
            0,
        ))];
        let mut chain = queue.build_desc_chain(&v).unwrap();

        let header = PacketHeader {
            src_cid: SRC_CID.into(),
            dst_cid: DST_CID.into(),
            src_port: SRC_PORT.into(),
            dst_port: DST_PORT.into(),
            len: 0.into(),
            type_: 0.into(),
            op: 0.into(),
            flags: 0.into(),
            buf_alloc: 0.into(),
            fwd_cnt: 0.into(),
        };
        mem.write_obj(header, GuestAddress(0x10_0000)).unwrap();

        let packet = VsockPacket::from_tx_virtq_chain(&mem, &mut chain, MAX_PKT_BUF_SIZE).unwrap();
        assert_eq!(packet.header, header);
        let header_slice = packet.header_slice();
        assert_eq!(
            header_slice.ptr_guard().as_ptr(),
            mem.get_host_address(GuestAddress(0x10_0000)).unwrap()
        );
        assert_eq!(header_slice.len(), PKT_HEADER_SIZE);
        assert!(packet.data_slice().is_none());

        let mem: GuestMemoryMmap =
            GuestMemoryMmap::from_ranges(&[(GuestAddress(0), 0x10_0004)]).unwrap();

        let v = vec![
            // The header doesn't fit entirely in the memory bounds.
            RawDescriptor::from(SplitDescriptor::new(0x10_0000, 0x100, 0, 0)),
            RawDescriptor::from(SplitDescriptor::new(0x20_0000, 0x100, 0, 0)),
        ];
        let queue = MockSplitQueue::new(&mem, 16);
        let mut chain = queue.build_desc_chain(&v).unwrap();
        assert_eq!(
            VsockPacket::from_tx_virtq_chain(&mem, &mut chain, MAX_PKT_BUF_SIZE).unwrap_err(),
            Error::InvalidMemoryAccess(GuestMemoryError::InvalidBackendAddress)
        );

        let v = vec![
            // The header is outside the memory bounds.
            RawDescriptor::from(SplitDescriptor::new(0x20_0000, 0x100, 0, 0)),
            RawDescriptor::from(SplitDescriptor::new(0x30_0000, 0x100, 0, 0)),
        ];
        let mut chain = queue.build_desc_chain(&v).unwrap();
        assert_eq!(
            VsockPacket::from_tx_virtq_chain(&mem, &mut chain, MAX_PKT_BUF_SIZE).unwrap_err(),
            Error::InvalidMemoryAccess(GuestMemoryError::InvalidGuestAddress(GuestAddress(
                0x20_0000
            )))
        );

        // Write some non-zero value to the `len` field of the header, which means there is also
        // a data descriptor in the chain, first with a value that exceeds the maximum allowed one.
        let header = PacketHeader {
            src_cid: SRC_CID.into(),
            dst_cid: DST_CID.into(),
            src_port: SRC_PORT.into(),
            dst_port: DST_PORT.into(),
            len: (MAX_PKT_BUF_SIZE + 1).into(),
            type_: 0.into(),
            op: 0.into(),
            flags: 0.into(),
            buf_alloc: 0.into(),
            fwd_cnt: 0.into(),
        };
        mem.write_obj(header, GuestAddress(0x5_0000)).unwrap();
        let v = vec![
            RawDescriptor::from(SplitDescriptor::new(0x5_0000, 0x100, 0, 0)),
            RawDescriptor::from(SplitDescriptor::new(0x8_0000, 0x100, 0, 0)),
        ];
        let mut chain = queue.build_desc_chain(&v).unwrap();
        assert_eq!(
            VsockPacket::from_tx_virtq_chain(&mem, &mut chain, MAX_PKT_BUF_SIZE).unwrap_err(),
            Error::InvalidHeaderLen(MAX_PKT_BUF_SIZE + 1)
        );

        // Write some non-zero, valid value to the `len` field of the header.
        let header = PacketHeader {
            src_cid: SRC_CID.into(),
            dst_cid: DST_CID.into(),
            src_port: SRC_PORT.into(),
            dst_port: DST_PORT.into(),
            len: LEN.into(),
            type_: 0.into(),
            op: 0.into(),
            flags: 0.into(),
            buf_alloc: 0.into(),
            fwd_cnt: 0.into(),
        };
        mem.write_obj(header, GuestAddress(0x5_0000)).unwrap();
        let v = vec![
            // The data descriptor is missing.
            RawDescriptor::from(SplitDescriptor::new(0x5_0000, PKT_HEADER_SIZE as u32, 0, 0)),
        ];
        let mut chain = queue.build_desc_chain(&v).unwrap();
        assert_eq!(
            VsockPacket::from_tx_virtq_chain(&mem, &mut chain, MAX_PKT_BUF_SIZE).unwrap_err(),
            Error::DescriptorChainTooShort
        );

        let v = vec![
            RawDescriptor::from(SplitDescriptor::new(0x5_0000, 0x100, 0, 0)),
            // The data array doesn't fit entirely in the memory bounds.
            RawDescriptor::from(SplitDescriptor::new(0x10_0000, 0x100, 0, 0)),
        ];
        let mut chain = queue.build_desc_chain(&v).unwrap();
        assert_eq!(
            VsockPacket::from_tx_virtq_chain(&mem, &mut chain, MAX_PKT_BUF_SIZE).unwrap_err(),
            Error::InvalidMemoryAccess(GuestMemoryError::InvalidBackendAddress)
        );

        let v = vec![
            RawDescriptor::from(SplitDescriptor::new(0x5_0000, 0x100, 0, 0)),
            // The data array is outside the memory bounds.
            RawDescriptor::from(SplitDescriptor::new(0x20_0000, 0x100, 0, 0)),
        ];
        let mut chain = queue.build_desc_chain(&v).unwrap();
        assert_eq!(
            VsockPacket::from_tx_virtq_chain(&mem, &mut chain, MAX_PKT_BUF_SIZE).unwrap_err(),
            Error::InvalidMemoryAccess(GuestMemoryError::InvalidGuestAddress(GuestAddress(
                0x20_0000
            )))
        );

        let v = vec![
            RawDescriptor::from(SplitDescriptor::new(0x5_0000, 0x100, 0, 0)),
            // A device-writable packet data descriptor should be invalid.
            RawDescriptor::from(SplitDescriptor::new(
                0x8_0000,
                0x100,
                VRING_DESC_F_WRITE as u16,
                0,
            )),
        ];
        let mut chain = queue.build_desc_chain(&v).unwrap();
        assert_eq!(
            VsockPacket::from_tx_virtq_chain(&mem, &mut chain, MAX_PKT_BUF_SIZE).unwrap_err(),
            Error::UnexpectedWriteOnlyDescriptor
        );

        let v = vec![
            RawDescriptor::from(SplitDescriptor::new(0x5_0000, 0x100, 0, 0)),
            // A data length < the length of data as described by the header.
            RawDescriptor::from(SplitDescriptor::new(0x8_0000, LEN - 1, 0, 0)),
        ];
        let mut chain = queue.build_desc_chain(&v).unwrap();
        assert_eq!(
            VsockPacket::from_tx_virtq_chain(&mem, &mut chain, MAX_PKT_BUF_SIZE).unwrap_err(),
            Error::DescriptorLengthTooSmall
        );

        // Let's also test a valid descriptor chain, with both header and data.
        let v = vec![
            RawDescriptor::from(SplitDescriptor::new(0x5_0000, 0x100, 0, 0)),
            RawDescriptor::from(SplitDescriptor::new(0x8_0000, 0x100, 0, 0)),
        ];
        let mut chain = queue.build_desc_chain(&v).unwrap();

        let packet = VsockPacket::from_tx_virtq_chain(&mem, &mut chain, MAX_PKT_BUF_SIZE).unwrap();
        assert_eq!(packet.header, header);
        let header_slice = packet.header_slice();
        assert_eq!(
            header_slice.ptr_guard().as_ptr(),
            mem.get_host_address(GuestAddress(0x5_0000)).unwrap()
        );
        assert_eq!(header_slice.len(), PKT_HEADER_SIZE);
        // The `len` field of the header was set to 16.
        assert_eq!(packet.len(), LEN);

        let data = packet.data_slice().unwrap();
        assert_eq!(
            data.ptr_guard().as_ptr(),
            mem.get_host_address(GuestAddress(0x8_0000)).unwrap()
        );
        assert_eq!(data.len(), LEN as usize);

        // If we try to get a vsock packet again, it fails because we already consumed all the
        // descriptors from the chain.
        assert_eq!(
            VsockPacket::from_tx_virtq_chain(&mem, &mut chain, MAX_PKT_BUF_SIZE).unwrap_err(),
            Error::DescriptorChainTooShort
        );

        // Let's also test a valid descriptor chain, with both header and data on a single
        // descriptor.
        let v = vec![RawDescriptor::from(SplitDescriptor::new(
            0x5_0000,
            PKT_HEADER_SIZE as u32 + 0x100,
            0,
            0,
        ))];
        let mut chain = queue.build_desc_chain(&v).unwrap();

        let packet = VsockPacket::from_tx_virtq_chain(&mem, &mut chain, MAX_PKT_BUF_SIZE).unwrap();
        assert_eq!(packet.header, header);
        let header_slice = packet.header_slice();
        assert_eq!(
            header_slice.ptr_guard().as_ptr(),
            mem.get_host_address(GuestAddress(0x5_0000)).unwrap()
        );
        assert_eq!(header_slice.len(), PKT_HEADER_SIZE);
        // The `len` field of the header was set to 16.
        assert_eq!(packet.len(), LEN);

        let data = packet.data_slice().unwrap();
        assert_eq!(
            data.ptr_guard().as_ptr(),
            mem.get_host_address(GuestAddress(0x5_0000 + PKT_HEADER_SIZE as u64))
                .unwrap()
        );
        assert_eq!(data.len(), LEN as usize);
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
        let mut chain = queue.build_desc_chain(&v).unwrap();

        let mut packet =
            VsockPacket::from_rx_virtq_chain(&mem, &mut chain, MAX_PKT_BUF_SIZE).unwrap();
        packet
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

        assert_eq!(packet.flags(), FLAGS | FLAG);
        assert_eq!(packet.op(), OP);
        assert_eq!(packet.type_(), TYPE);
        assert_eq!(packet.dst_cid(), DST_CID);
        assert_eq!(packet.dst_port(), DST_PORT);
        assert_eq!(packet.src_cid(), SRC_CID);
        assert_eq!(packet.src_port(), SRC_PORT);
        assert_eq!(packet.fwd_cnt(), FWD_CNT);
        assert_eq!(packet.len(), LEN);
        assert_eq!(packet.buf_alloc(), BUF_ALLOC);

        let expected_header = PacketHeader {
            src_cid: SRC_CID.into(),
            dst_cid: DST_CID.into(),
            src_port: SRC_PORT.into(),
            dst_port: DST_PORT.into(),
            len: LEN.into(),
            type_: TYPE.into(),
            op: OP.into(),
            flags: (FLAGS | FLAG).into(),
            buf_alloc: BUF_ALLOC.into(),
            fwd_cnt: FWD_CNT.into(),
        };

        assert_eq!(packet.header, expected_header);
        assert_eq!(
            u64::from_le(
                packet
                    .header_slice()
                    .read_obj::<u64>(SRC_CID_OFFSET)
                    .unwrap()
            ),
            SRC_CID
        );
        assert_eq!(
            u64::from_le(
                packet
                    .header_slice()
                    .read_obj::<u64>(DST_CID_OFFSET)
                    .unwrap()
            ),
            DST_CID
        );
        assert_eq!(
            u32::from_le(
                packet
                    .header_slice()
                    .read_obj::<u32>(SRC_PORT_OFFSET)
                    .unwrap()
            ),
            SRC_PORT
        );
        assert_eq!(
            u32::from_le(
                packet
                    .header_slice()
                    .read_obj::<u32>(DST_PORT_OFFSET)
                    .unwrap()
            ),
            DST_PORT,
        );
        assert_eq!(
            u32::from_le(packet.header_slice().read_obj::<u32>(LEN_OFFSET).unwrap()),
            LEN
        );
        assert_eq!(
            u16::from_le(packet.header_slice().read_obj::<u16>(TYPE_OFFSET).unwrap()),
            TYPE
        );
        assert_eq!(
            u16::from_le(packet.header_slice().read_obj::<u16>(OP_OFFSET).unwrap()),
            OP
        );
        assert_eq!(
            u32::from_le(packet.header_slice().read_obj::<u32>(FLAGS_OFFSET).unwrap()),
            FLAGS | FLAG
        );
        assert_eq!(
            u32::from_le(
                packet
                    .header_slice()
                    .read_obj::<u32>(BUF_ALLOC_OFFSET)
                    .unwrap()
            ),
            BUF_ALLOC
        );
        assert_eq!(
            u32::from_le(
                packet
                    .header_slice()
                    .read_obj::<u32>(FWD_CNT_OFFSET)
                    .unwrap()
            ),
            FWD_CNT
        );
    }

    #[test]
    fn test_set_header_from_raw() {
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
        let mut chain = queue.build_desc_chain(&v).unwrap();

        let mut packet =
            VsockPacket::from_rx_virtq_chain(&mem, &mut chain, MAX_PKT_BUF_SIZE).unwrap();

        let header = PacketHeader {
            src_cid: SRC_CID.into(),
            dst_cid: DST_CID.into(),
            src_port: SRC_PORT.into(),
            dst_port: DST_PORT.into(),
            len: LEN.into(),
            type_: TYPE.into(),
            op: OP.into(),
            flags: (FLAGS | FLAG).into(),
            buf_alloc: BUF_ALLOC.into(),
            fwd_cnt: FWD_CNT.into(),
        };

        // SAFETY: created from an existing packet header.
        let slice = unsafe {
            std::slice::from_raw_parts(
                (&header as *const PacketHeader) as *const u8,
                std::mem::size_of::<PacketHeader>(),
            )
        };
        assert_eq!(packet.header, PacketHeader::default());
        packet.set_header_from_raw(slice).unwrap();
        assert_eq!(packet.header, header);
        let header_from_slice: PacketHeader = packet.header_slice().read_obj(0).unwrap();
        assert_eq!(header_from_slice, header);

        let invalid_slice = [0; PKT_HEADER_SIZE - 1];
        assert_eq!(
            packet.set_header_from_raw(&invalid_slice).unwrap_err(),
            Error::InvalidHeaderInputSize(PKT_HEADER_SIZE - 1)
        );
    }

    #[test]
    fn test_packet_new() {
        let mut pkt_raw = [0u8; PKT_HEADER_SIZE + LEN as usize];
        let (hdr_raw, data_raw) = pkt_raw.split_at_mut(PKT_HEADER_SIZE);
        // SAFETY: safe because ``hdr_raw` and `data_raw` live for as long as
        // the scope of the current test.
        let packet = unsafe { VsockPacket::new(hdr_raw, Some(data_raw)).unwrap() };
        assert_eq!(
            packet.header_slice.ptr_guard().as_ptr(),
            hdr_raw.as_mut_ptr(),
        );
        assert_eq!(packet.header_slice.len(), PKT_HEADER_SIZE);
        assert_eq!(packet.header, PacketHeader::default());
        assert_eq!(
            packet.data_slice.unwrap().ptr_guard().as_ptr(),
            data_raw.as_mut_ptr(),
        );
        assert_eq!(packet.data_slice.unwrap().len(), LEN as usize);

        // SAFETY: Safe because ``hdr_raw` and `data_raw` live as long as the
        // scope of the current test.
        let packet = unsafe { VsockPacket::new(hdr_raw, None).unwrap() };
        assert_eq!(
            packet.header_slice.ptr_guard().as_ptr(),
            hdr_raw.as_mut_ptr(),
        );
        assert_eq!(packet.header, PacketHeader::default());
        assert!(packet.data_slice.is_none());

        let mut hdr_raw = [0u8; PKT_HEADER_SIZE - 1];
        assert_eq!(
            // SAFETY: Safe because ``hdr_raw` lives for as long as the scope of the current test.
            unsafe { VsockPacket::new(&mut hdr_raw, None).unwrap_err() },
            Error::InvalidHeaderInputSize(PKT_HEADER_SIZE - 1)
        );
    }

    #[test]
    #[should_panic]
    fn test_set_header_field_with_invalid_offset() {
        const INVALID_OFFSET: usize = 50;

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
        let mut chain = queue.build_desc_chain(&v).unwrap();

        let mut packet =
            VsockPacket::from_rx_virtq_chain(&mem, &mut chain, MAX_PKT_BUF_SIZE).unwrap();
        // Set the `src_cid` of the header, but use an invalid offset for that.
        set_header_field!(packet, src_cid, INVALID_OFFSET, SRC_CID);
    }
}
