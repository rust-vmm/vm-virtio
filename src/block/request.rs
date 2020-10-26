// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Copyright © 2019 Intel Corporation
//
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

//! Virtio block request parsing abstraction.
//!
//! This module provides the following abstraction for parsing a virtio block device request:
//!
//! - [`Request`](struct.Request.html) which handles the parsing of the block device request via
//! [`Request::parse`](struct.Request.html#method.parse) method. For now this method assumes that
//! the request descriptor chain contains:
//!     - one device-readable descriptor for the request header.
//!     - zero, one or more device-readable/writable descriptor(s) for the request data buffers.
//!     - one device-writable descriptor for the request status.
//! For the usual drivers, this assumption stands, but in the future we might make the `parse`
//! implementation more generic by removing any constraint regarding the number of descriptors
//! that each request element can occupy. Basically, the only hard requirement regarding the
//! request descriptors is: The driver MUST place any device-writable descriptor elements after any
//! device-readable descriptor elements (see
//! [this](https://docs.oasis-open.org/virtio/virtio/v1.1/csprd01/virtio-v1.1-csprd01.html#x1-280004)).
//! However, we expect the `Request` interface won't change even if we switch to the general
//! approach.

use std::fmt::{self, Display};
use std::{mem, result};

use crate::{queue::DescriptorChain, Descriptor};
use vm_memory::{
    ByteValued, Bytes, GuestAddress, GuestAddressSpace, GuestMemory, GuestMemoryError,
};

const VIRTIO_BLK_T_IN: u32 = 0;
const VIRTIO_BLK_T_OUT: u32 = 1;
const VIRTIO_BLK_T_FLUSH: u32 = 4;

/// Block request parsing errors.
#[derive(Debug)]
pub enum Error {
    /// Too few descriptors in a descriptor chain.
    DescriptorChainTooShort,
    /// Descriptor that was too short to use.
    DescriptorLengthTooSmall,
    /// Invalid memory access.
    GuestMemory(GuestMemoryError),
    /// Invalid sector value for a flush request.
    InvalidFlushSector,
    /// Read only descriptor that protocol says to write to.
    UnexpectedReadOnlyDescriptor,
    /// Write only descriptor that protocol says to read from.
    UnexpectedWriteOnlyDescriptor,
}

impl Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Error::*;

        match self {
            DescriptorChainTooShort => write!(f, "descriptor chain too short"),
            DescriptorLengthTooSmall => write!(f, "descriptor length too small"),
            GuestMemory(ref err) => write!(f, "error accessing guest memory: {}", err),
            InvalidFlushSector => write!(f, "invalid sector in flush request, it should be 0"),
            UnexpectedReadOnlyDescriptor => write!(f, "unexpected read only descriptor"),
            UnexpectedWriteOnlyDescriptor => write!(f, "unexpected write only descriptor"),
        }
    }
}

/// Dedicated [`Result`](https://doc.rust-lang.org/std/result/) type.
pub type Result<T> = result::Result<T, Error>;

/// Type of request from driver to device.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum RequestType {
    /// Read request.
    In,
    /// Write request.
    Out,
    /// Flush request.
    Flush,
    /// Unknown request.
    Unsupported(u32),
}

impl From<u32> for RequestType {
    fn from(value: u32) -> Self {
        match value {
            VIRTIO_BLK_T_IN => RequestType::In,
            VIRTIO_BLK_T_OUT => RequestType::Out,
            VIRTIO_BLK_T_FLUSH => RequestType::Flush,
            t => RequestType::Unsupported(t),
        }
    }
}

/// Block request header.
#[derive(Copy, Clone, Debug, Default)]
#[repr(C)]
struct RequestHeader {
    request_type: u32,
    _reserved: u32,
    sector: u64,
}

/// Stores the necessary information for further execution of a block request.
#[derive(Debug, PartialEq)]
pub struct Request {
    /// The type of the request.
    request_type: RequestType,
    /// Stores the (address, data length) pairs where the data descriptors
    /// point to.
    data: Vec<(GuestAddress, u32)>,
    /// The offset (multiplied by 512) where the read or write is to occur.
    sector: u64,
    /// The address where the device should write the request status.
    status_addr: GuestAddress,
}

// Safe because RequestHeader contains only plain data.
unsafe impl ByteValued for RequestHeader {}

impl Request {
    /// Returns the request type.
    pub fn request_type(&self) -> RequestType {
        self.request_type
    }

    /// Returns the (address, len) pairs where the request data is in the guest memory.
    pub fn data(&self) -> &[(GuestAddress, u32)] {
        &self.data
    }

    /// Returns the sector.
    pub fn sector(&self) -> u64 {
        self.sector
    }

    /// Returns the status address.
    pub fn status_addr(&self) -> GuestAddress {
        self.status_addr
    }

    // Checks that a descriptor meets the minimal requirements for a valid status descriptor.
    fn check_status_desc<M: GuestMemory>(mem: &M, desc: Descriptor) -> Result<()> {
        // The status MUST always be writable.
        if !desc.is_write_only() {
            return Err(Error::UnexpectedReadOnlyDescriptor);
        }
        // It makes sense to check the data length from descriptor, since we're going to
        // keep from now on only the address of the status buffer in the `Request` object
        // so we won't be able to validate this at some other point.
        if desc.len() < 1 {
            return Err(Error::DescriptorLengthTooSmall);
        }

        // Check that the address of the status descriptor is valid in guest memory.
        // We will write an u8 status here after executing the request.
        let _ = mem
            .checked_offset(desc.addr(), mem::size_of::<u8>())
            .ok_or_else(|| {
                Error::GuestMemory(GuestMemoryError::InvalidGuestAddress(desc.addr()))
            })?;
        Ok(())
    }

    // Checks that a descriptor meets the minimal requirements for a valid data descriptor.
    fn check_data_desc<M: GuestMemory>(
        mem: &M,
        desc: Descriptor,
        request_type: RequestType,
    ) -> Result<()> {
        // We do this check only for the device-readable buffers, as opposed to
        // also check that the device doesn't want to read a device-writable buffer
        // because this one is not a MUST (the device MAY do that for debugging or
        // diagnostic purposes).
        if !desc.is_write_only() && request_type == RequestType::In {
            return Err(Error::UnexpectedReadOnlyDescriptor);
        }

        // Check that the address of the data descriptor is valid in guest memory.
        let _ = mem
            .checked_offset(desc.addr(), desc.len() as usize)
            .ok_or_else(|| {
                Error::GuestMemory(GuestMemoryError::InvalidGuestAddress(desc.addr()))
            })?;
        Ok(())
    }

    /// Parses a `desc_chain` and returns the associated `Request`.
    ///
    /// The checks we're doing here are mostly the `MUST`s from the virtio specification.
    /// We are also partially validating `The driver MUST place any device-writable descriptor
    /// elements after any device-readable descriptor elements` rule by checking that the
    /// expected header descriptor (the chain head) is device-readable and the expected status
    /// descriptor (the chain tail) is device-writable.
    ///
    /// # Arguments
    /// * `desc_chain` - A mutable reference to the descriptor chain that should point to the
    ///                  buffers of a virtio block request.
    pub fn parse<M: GuestAddressSpace>(desc_chain: &mut DescriptorChain<M>) -> Result<Request> {
        let chain_head = desc_chain.next().ok_or(Error::DescriptorChainTooShort)?;
        // The head contains the request type which MUST be readable.
        if chain_head.is_write_only() {
            return Err(Error::UnexpectedWriteOnlyDescriptor);
        }

        let request_header = desc_chain
            .memory()
            .read_obj::<RequestHeader>(chain_head.addr())
            .map_err(Error::GuestMemory)?;

        if request_header.request_type == VIRTIO_BLK_T_FLUSH && request_header.sector != 0 {
            return Err(Error::InvalidFlushSector);
        }

        let mut request = Request {
            request_type: RequestType::from(request_header.request_type),
            data: Vec::new(),
            sector: request_header.sector,
            status_addr: GuestAddress(0),
        };

        let mut desc = desc_chain.next().ok_or(Error::DescriptorChainTooShort)?;

        while desc.has_next() {
            Request::check_data_desc::<<M>::M>(desc_chain.memory(), desc, request.request_type)?;

            request.data.push((desc.addr(), desc.len()));
            desc = desc_chain.next().ok_or(Error::DescriptorChainTooShort)?;
        }
        let status_desc = desc;

        Request::check_status_desc::<<M>::M>(desc_chain.memory(), status_desc)?;

        request.status_addr = status_desc.addr();
        Ok(request)
    }
}
