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
//! and an optional `data` array of bytes. The methods mentioned above assume that each of the
//! packet elements occupies exactly one descriptor. For the usual drivers, this assumption stands,
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
    ByteValued, Bytes, GuestMemory, GuestMemoryError, GuestMemoryRegion, Le16, Le32, Le64,
    VolatileMemoryError, VolatileSlice,
};

/// Vsock packet parsing errors.
#[derive(Debug)]
pub enum Error {
    /// Too few descriptors in a descriptor chain.
    DescriptorChainTooShort,
    /// Descriptor that was too short to use.
    DescriptorLengthTooSmall,
    /// The slice for creating a header has an invalid length.
    InvalidHeaderInputSize(usize),
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
            Error::InvalidHeaderInputSize(size) => {
                write!(f, "Invalid header input size: {}", size)
            }
            Error::InvalidMemoryAccess(error) => {
                write!(f, "Invalid guest memory access: {}", error)
            }
            Error::InvalidVolatileAccess(error) => {
                write!(f, "Invalid volatile memory access: {}", error)
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
#[derive(Clone, Copy, Debug, Default, PartialEq)]
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

// This is safe because `PacketHeader` contains only wrappers over POD types and all accesses
// through safe `vm-memory` API will validate any garbage that could be included in there.
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
    pub fn from_tx_virtq_chain<M, T>(
        mem: &'a M,
        desc_chain: &mut DescriptorChain<T>,
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

        let data_desc = desc_chain.next().ok_or(Error::DescriptorChainTooShort)?;

        if data_desc.is_write_only() {
            return Err(Error::UnexpectedWriteOnlyDescriptor);
        }

        // The data buffer should be large enough to fit the size of the data, as described by
        // the header descriptor.
        if data_desc.len() < pkt.len() {
            return Err(Error::DescriptorLengthTooSmall);
        }

        let data_slice = {
            mem.get_slice(data_desc.addr(), data_desc.len() as usize)
                .map_err(Error::InvalidMemoryAccess)?
        };

        pkt.data_slice = Some(data_slice);
        Ok(pkt)
    }

    /// Create the packet wrapper from an RX chain.
    ///
    /// There must be two descriptors in the chain, both writable: a header descriptor and a data
    /// descriptor.
    pub fn from_rx_virtq_chain<M, T>(
        mem: &'a M,
        desc_chain: &mut DescriptorChain<T>,
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

        // All RX descriptor chains should have a header and a data descriptor.
        if !chain_head.has_next() {
            return Err(Error::DescriptorChainTooShort);
        }

        let header_slice = mem
            .get_slice(chain_head.addr(), PKT_HEADER_SIZE)
            .map_err(Error::InvalidMemoryAccess)?;
        let data_desc = desc_chain.next().ok_or(Error::DescriptorChainTooShort)?;

        if !data_desc.is_write_only() {
            return Err(Error::UnexpectedReadOnlyDescriptor);
        }

        let data_slice = mem
            .get_slice(data_desc.addr(), data_desc.len() as usize)
            .map_err(Error::InvalidMemoryAccess)?;

        Ok(Self {
            header_slice,
            header: Default::default(),
            data_slice: Some(data_slice),
        })
    }
}

impl<'a> VsockPacket<'a, ()> {
    /// Create a packet based on one pointer for the header, and an optional one for data.
    pub fn new(hdr: &mut [u8], data: Option<(&mut [u8], usize)>) -> VsockPacket<'a, ()> {
        VsockPacket {
            header_slice: unsafe { VolatileSlice::new(hdr.as_mut_ptr(), PKT_HEADER_SIZE) },
            header: Default::default(),
            data_slice: data.map(|data| unsafe { VolatileSlice::new(data.0.as_mut_ptr(), data.1) }),
        }
    }
}
