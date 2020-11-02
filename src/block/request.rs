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

#[cfg(test)]
mod tests {
    use super::*;

    use vm_memory::{Address, GuestMemoryMmap};

    use crate::queue::tests::VirtQueue;
    use crate::{VIRTQ_DESC_F_NEXT, VIRTQ_DESC_F_WRITE};

    impl PartialEq for Error {
        fn eq(&self, other: &Self) -> bool {
            use self::Error::*;
            match (self, other) {
                (DescriptorChainTooShort, DescriptorChainTooShort) => true,
                (DescriptorLengthTooSmall, DescriptorLengthTooSmall) => true,
                (GuestMemory(ref e), GuestMemory(ref other_e)) => {
                    format!("{}", e).eq(&format!("{}", other_e))
                }
                (InvalidFlushSector, InvalidFlushSector) => true,
                (UnexpectedReadOnlyDescriptor, UnexpectedReadOnlyDescriptor) => true,
                (UnexpectedWriteOnlyDescriptor, UnexpectedWriteOnlyDescriptor) => true,
                _ => false,
            }
        }
    }

    // Helper method that writes a descriptor chain to a `GuestMemoryMmap` object and returns
    // the associated `DescriptorChain` object. `descs` represents a slice of `Descriptor` objects
    // which are used to populate the chain. This method ensures the next flags and values are
    // set properly for the desired chain, but keeps the other characteristics of the input
    // descriptors (`addr`, `len`, other flags).
    // The queue/descriptor chain related information is written in memory starting with
    // address 0. The `addr` fields of the input descriptors should start at a sufficiently
    // greater location (i.e. 1MiB, or `0x10_0000`).
    fn build_desc_chain<'a>(
        mem: &'a GuestMemoryMmap,
        descs: &[Descriptor],
    ) -> DescriptorChain<&'a GuestMemoryMmap> {
        // Support a max of 16 descriptors for now.
        let vq = VirtQueue::new(GuestAddress(0), mem, 16);
        for (idx, desc) in descs.iter().enumerate() {
            let i = idx as u16;
            vq.dtable(i).addr().store(desc.addr().0);
            vq.dtable(i).len().store(desc.len());

            if idx == descs.len() - 1 {
                // Clear the NEXT flag if it was set. The value of the next field of the
                // Descriptor doesn't matter at this point.
                vq.dtable(i)
                    .flags()
                    .store(desc.flags() & !VIRTQ_DESC_F_NEXT);
            } else {
                // Ensure the next flag is set.
                vq.dtable(i).flags().store(desc.flags() | VIRTQ_DESC_F_NEXT);
                // Ensure we are referring the following descriptor. This ignores
                // any value is actually present in `desc.next`.
                vq.dtable(i).next().store(i + 1);
            }
        }

        // Put the descriptor index 0 in the first available ring position.
        mem.write_obj(0u16, vq.avail_start().unchecked_add(4))
            .unwrap();

        // Set `avail_idx` to 1.
        mem.write_obj(1u16, vq.avail_start().unchecked_add(2))
            .unwrap();

        vq.create_queue(mem)
            .iter()
            .unwrap()
            .next()
            .expect("failed to build desc chain")
    }

    #[test]
    fn test_parse_request() {
        let mem = GuestMemoryMmap::from_ranges(&[(GuestAddress(0), 0x1000_0000)]).unwrap();
        // The `build_desc_chain` function will populate the `NEXT` related flags and field.
        let v = vec![
            // A device-writable request header descriptor.
            Descriptor::new(0x10_0000, 0x100, VIRTQ_DESC_F_WRITE, 0),
            Descriptor::new(0x20_0000, 0x100, VIRTQ_DESC_F_WRITE, 0),
            Descriptor::new(0x30_0000, 0x100, VIRTQ_DESC_F_WRITE, 0),
        ];
        let mut chain = build_desc_chain(&mem, &v[..3]);

        let req_header = RequestHeader {
            request_type: VIRTIO_BLK_T_IN,
            _reserved: 0,
            sector: 2,
        };
        mem.write_obj::<RequestHeader>(req_header, GuestAddress(0x10_0000))
            .unwrap();
        // Request header descriptor should be device-readable.
        assert_eq!(
            Request::parse(&mut chain).unwrap_err(),
            Error::UnexpectedWriteOnlyDescriptor
        );

        let v = vec![
            Descriptor::new(0x10_0000, 0x100, 0, 0),
            Descriptor::new(0x20_0000, 0x100, VIRTQ_DESC_F_WRITE, 0),
            // A device-readable request status descriptor.
            Descriptor::new(0x30_0000, 0x100, 0, 0),
        ];
        let mut chain = build_desc_chain(&mem, &v[..3]);

        // Status descriptor should be device-writable.
        assert_eq!(
            Request::parse(&mut chain).unwrap_err(),
            Error::UnexpectedReadOnlyDescriptor
        );

        let v = vec![
            Descriptor::new(0x10_0000, 0x100, 0, 0),
            Descriptor::new(0x20_0000, 0x100, VIRTQ_DESC_F_WRITE, 0),
            // Status descriptor with len = 0.
            Descriptor::new(0x30_0000, 0x0, VIRTQ_DESC_F_WRITE, 0),
        ];
        let mut chain = build_desc_chain(&mem, &v[..3]);
        assert_eq!(
            Request::parse(&mut chain).unwrap_err(),
            Error::DescriptorLengthTooSmall
        );

        let v = vec![
            Descriptor::new(0x10_0000, 0x100, 0, 0),
            Descriptor::new(0x20_0000, 0x100, 0, 0),
            Descriptor::new(0x30_0000, 0x100, VIRTQ_DESC_F_WRITE, 0),
        ];
        let mut chain = build_desc_chain(&mem, &v[..3]);

        // Flush request with sector != 0.
        let req_header = RequestHeader {
            request_type: VIRTIO_BLK_T_FLUSH,
            _reserved: 0,
            sector: 1,
        };
        mem.write_obj::<RequestHeader>(req_header, GuestAddress(0x10_0000))
            .unwrap();

        // Sector must be 0 for a VIRTIO_BLK_T_FLUSH request.
        assert_eq!(
            Request::parse(&mut chain).unwrap_err(),
            Error::InvalidFlushSector
        );

        let mut chain = build_desc_chain(&mem, &v[..3]);
        mem.write_obj::<u32>(VIRTIO_BLK_T_IN, GuestAddress(0x10_0000))
            .unwrap();
        // We shouldn't read from a device-readable buffer.
        assert_eq!(
            Request::parse(&mut chain).unwrap_err(),
            Error::UnexpectedReadOnlyDescriptor
        );

        // Invalid data buffer address.
        let v = vec![
            Descriptor::new(0x10_0000, 0x100, 0, 0),
            Descriptor::new(0xFFF_FFF0, 0x100, VIRTQ_DESC_F_WRITE, 0),
            Descriptor::new(0x30_0000, 0x200, VIRTQ_DESC_F_WRITE, 0),
            Descriptor::new(0x40_0000, 0x100, VIRTQ_DESC_F_WRITE, 0),
        ];
        let req_header = RequestHeader {
            request_type: VIRTIO_BLK_T_OUT,
            _reserved: 0,
            sector: 2,
        };
        mem.write_obj::<RequestHeader>(req_header, GuestAddress(0x10_0000))
            .unwrap();

        let mut chain = build_desc_chain(&mem, &v[..4]);

        // The first data descriptor would cause a write beyond memory capacity.
        assert_eq!(
            Request::parse(&mut chain).unwrap_err(),
            Error::GuestMemory(GuestMemoryError::InvalidGuestAddress(GuestAddress(
                0xFFF_FFF0,
            )))
        );

        // Invalid status address.
        let v = vec![
            Descriptor::new(0x10_0000, 0x100, 0, 0),
            Descriptor::new(0x20_0000, 0x100, VIRTQ_DESC_F_WRITE, 0),
            Descriptor::new(0x30_0000, 0x200, VIRTQ_DESC_F_WRITE, 0),
            Descriptor::new(0x1100_0000, 0x100, VIRTQ_DESC_F_WRITE, 0),
        ];
        let req_header = RequestHeader {
            request_type: VIRTIO_BLK_T_OUT,
            _reserved: 0,
            sector: 2,
        };
        mem.write_obj::<RequestHeader>(req_header, GuestAddress(0x10_0000))
            .unwrap();

        let mut chain = build_desc_chain(&mem, &v[..4]);

        // The status descriptor would cause a write beyond capacity.
        assert_eq!(
            Request::parse(&mut chain).unwrap_err(),
            Error::GuestMemory(GuestMemoryError::InvalidGuestAddress(GuestAddress(
                0x1100_0000,
            )))
        );

        // Valid descriptor chain for OUT.
        let v = vec![
            Descriptor::new(0x10_0000, 0x100, 0, 0),
            Descriptor::new(0x20_0000, 0x100, VIRTQ_DESC_F_WRITE, 0),
            Descriptor::new(0x30_0000, 0x200, VIRTQ_DESC_F_WRITE, 0),
            Descriptor::new(0x40_0000, 0x100, VIRTQ_DESC_F_WRITE, 0),
        ];
        let req_header = RequestHeader {
            request_type: VIRTIO_BLK_T_OUT,
            _reserved: 0,
            sector: 2,
        };
        mem.write_obj::<RequestHeader>(req_header, GuestAddress(0x10_0000))
            .unwrap();

        let mut chain = build_desc_chain(&mem, &v[..4]);

        let request = Request::parse(&mut chain).unwrap();
        let expected_request = Request {
            request_type: RequestType::Out,
            data: vec![
                (GuestAddress(0x20_0000), 0x100),
                (GuestAddress(0x30_0000), 0x200),
            ],
            sector: 2,
            status_addr: GuestAddress(0x40_0000),
        };
        assert_eq!(request, expected_request);
        assert_eq!(request.status_addr(), GuestAddress(0x40_0000));

        // Request header with unsupported request type.
        let req_header = RequestHeader {
            request_type: 2,
            _reserved: 0,
            sector: 2,
        };
        mem.write_obj::<RequestHeader>(req_header, GuestAddress(0x10_0000))
            .unwrap();

        let mut chain = build_desc_chain(&mem, &v[..4]);

        let request = Request::parse(&mut chain).unwrap();
        assert_eq!(request.request_type(), RequestType::Unsupported(2));

        // Valid descriptor chain for FLUSH.
        let v = vec![
            Descriptor::new(0x10_0000, 0x100, 0, 0),
            Descriptor::new(0x40_0000, 0x100, VIRTQ_DESC_F_WRITE, 0),
        ];
        let req_header = RequestHeader {
            request_type: VIRTIO_BLK_T_FLUSH,
            _reserved: 0,
            sector: 0,
        };
        mem.write_obj::<RequestHeader>(req_header, GuestAddress(0x10_0000))
            .unwrap();

        let mut chain = build_desc_chain(&mem, &v[..2]);
        assert!(Request::parse(&mut chain).is_ok());
    }
}
