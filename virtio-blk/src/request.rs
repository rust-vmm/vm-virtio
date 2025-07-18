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
use std::ops::Deref;
use std::result;

use virtio_bindings::bindings::virtio_blk::{
    VIRTIO_BLK_T_DISCARD, VIRTIO_BLK_T_FLUSH, VIRTIO_BLK_T_GET_ID, VIRTIO_BLK_T_IN,
    VIRTIO_BLK_T_OUT, VIRTIO_BLK_T_WRITE_ZEROES,
};

use virtio_queue::{
    desc::{split::Descriptor as SplitDescriptor, RawDescriptor},
    DescriptorChain,
};
use vm_memory::{ByteValued, Bytes, GuestAddress, GuestMemory, GuestMemoryError};

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
            GuestMemory(ref err) => write!(f, "error accessing guest memory: {err}"),
            InvalidFlushSector => write!(f, "invalid sector in flush request, it should be 0"),
            UnexpectedReadOnlyDescriptor => write!(f, "unexpected read only descriptor"),
            UnexpectedWriteOnlyDescriptor => write!(f, "unexpected write only descriptor"),
        }
    }
}

/// Dedicated [`Result`](https://doc.rust-lang.org/std/result/) type.
pub type Result<T> = result::Result<T, Error>;

/// Type of request from driver to device.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RequestType {
    /// Read request.
    In,
    /// Write request.
    Out,
    /// Flush request.
    Flush,
    /// Get device ID request.
    GetDeviceID,
    /// Discard request.
    Discard,
    /// Write zeroes request.
    WriteZeroes,
    /// Unknown request.
    Unsupported(u32),
}

impl From<u32> for RequestType {
    fn from(value: u32) -> Self {
        match value {
            VIRTIO_BLK_T_IN => RequestType::In,
            VIRTIO_BLK_T_OUT => RequestType::Out,
            VIRTIO_BLK_T_FLUSH => RequestType::Flush,
            VIRTIO_BLK_T_GET_ID => RequestType::GetDeviceID,
            VIRTIO_BLK_T_DISCARD => RequestType::Discard,
            VIRTIO_BLK_T_WRITE_ZEROES => RequestType::WriteZeroes,
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
#[derive(Debug, PartialEq, Eq)]
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

// SAFETY: Safe because RequestHeader contains only plain data.
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

    /// Returns the total length of request data.
    pub fn total_data_len(&self) -> u64 {
        // The maximum queue size is 32768 (2^15), which is the maximum  possible descriptor chain
        // length and since data length is an u32, this sum can not overflow an u64.
        self.data.iter().map(|x| x.1 as u64).sum()
    }

    // Checks that a descriptor meets the minimal requirements for a valid status descriptor.
    fn check_status_desc<M>(mem: &M, desc: RawDescriptor) -> Result<()>
    where
        M: GuestMemory + ?Sized,
    {
        let desc = SplitDescriptor::from(desc);
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

        // Check that the address of the status is valid in guest memory.
        // We will write an u8 status here after executing the request.
        let _ = mem.check_address(desc.addr()).ok_or_else(|| {
            Error::GuestMemory(GuestMemoryError::InvalidGuestAddress(desc.addr()))
        })?;
        Ok(())
    }

    // Checks that a descriptor meets the minimal requirements for a valid data descriptor.
    fn check_data_desc(desc: RawDescriptor, request_type: RequestType) -> Result<()> {
        let desc = SplitDescriptor::from(desc);
        // We do this check only for the device-readable buffers, as opposed to
        // also check that the device doesn't want to read a device-writable buffer
        // because this one is not a MUST (the device MAY do that for debugging or
        // diagnostic purposes).
        if !desc.is_write_only() && request_type == RequestType::In {
            return Err(Error::UnexpectedReadOnlyDescriptor);
        }
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
    ///
    /// * `desc_chain` - A mutable reference to the descriptor chain that should point to the buffers of a virtio block request.
    pub fn parse<M>(desc_chain: &mut DescriptorChain<M>) -> Result<Request>
    where
        M: Deref,
        M::Target: GuestMemory,
    {
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
            Request::check_data_desc(RawDescriptor::from(desc), request.request_type)?;

            request.data.push((desc.addr(), desc.len()));
            desc = desc_chain.next().ok_or(Error::DescriptorChainTooShort)?;
        }
        let status_desc = desc;

        Request::check_status_desc(desc_chain.memory(), RawDescriptor::from(status_desc))?;

        request.status_addr = status_desc.addr();
        Ok(request)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use vm_memory::GuestMemoryMmap;

    use virtio_bindings::bindings::virtio_ring::VRING_DESC_F_WRITE;
    use virtio_queue::mock::MockSplitQueue;

    impl PartialEq for Error {
        fn eq(&self, other: &Self) -> bool {
            use self::Error::*;
            match (self, other) {
                (DescriptorChainTooShort, DescriptorChainTooShort) => true,
                (DescriptorLengthTooSmall, DescriptorLengthTooSmall) => true,
                (GuestMemory(ref e), GuestMemory(ref other_e)) => {
                    format!("{e}").eq(&format!("{other_e}"))
                }
                (InvalidFlushSector, InvalidFlushSector) => true,
                (UnexpectedReadOnlyDescriptor, UnexpectedReadOnlyDescriptor) => true,
                (UnexpectedWriteOnlyDescriptor, UnexpectedWriteOnlyDescriptor) => true,
                _ => false,
            }
        }
    }

    impl Request {
        /// Manually create mock `Request` instances.
        pub fn new(
            request_type: RequestType,
            data: Vec<(GuestAddress, u32)>,
            sector: u64,
            status_addr: GuestAddress,
        ) -> Self {
            Request {
                request_type,
                data,
                sector,
                status_addr,
            }
        }
    }

    #[test]
    fn test_parse_request() {
        let mem: GuestMemoryMmap =
            GuestMemoryMmap::from_ranges(&[(GuestAddress(0), 0x1000_0000)]).unwrap();
        // The `build_desc_chain` function will populate the `NEXT` related flags and field.
        let v = [
            // A device-writable request header descriptor.
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
            RawDescriptor::from(SplitDescriptor::new(
                0x30_0000,
                0x100,
                VRING_DESC_F_WRITE as u16,
                0,
            )),
        ];
        // Create a queue of max 16 descriptors and a descriptor chain based on the array above.
        let queue = MockSplitQueue::new(&mem, 16);
        let mut chain = queue.build_desc_chain(&v[..3]).unwrap();

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

        let v = [
            RawDescriptor::from(SplitDescriptor::new(0x10_0000, 0x100, 0, 0)),
            RawDescriptor::from(SplitDescriptor::new(
                0x20_0000,
                0x100,
                VRING_DESC_F_WRITE as u16,
                0,
            )),
            // A device-readable request status descriptor.
            RawDescriptor::from(SplitDescriptor::new(0x30_0000, 0x100, 0, 0)),
        ];
        let mut chain = queue.build_desc_chain(&v[..3]).unwrap();

        // Status descriptor should be device-writable.
        assert_eq!(
            Request::parse(&mut chain).unwrap_err(),
            Error::UnexpectedReadOnlyDescriptor
        );

        let v = [
            RawDescriptor::from(SplitDescriptor::new(0x10_0000, 0x100, 0, 0)),
            RawDescriptor::from(SplitDescriptor::new(
                0x20_0000,
                0x100,
                VRING_DESC_F_WRITE as u16,
                0,
            )),
            // Status descriptor with len = 0.
            RawDescriptor::from(SplitDescriptor::new(
                0x30_0000,
                0x0,
                VRING_DESC_F_WRITE as u16,
                0,
            )),
        ];
        let mut chain = queue.build_desc_chain(&v[..3]).unwrap();
        assert_eq!(
            Request::parse(&mut chain).unwrap_err(),
            Error::DescriptorLengthTooSmall
        );

        let v = [
            RawDescriptor::from(SplitDescriptor::new(0x10_0000, 0x100, 0, 0)),
            RawDescriptor::from(SplitDescriptor::new(0x20_0000, 0x100, 0, 0)),
            RawDescriptor::from(SplitDescriptor::new(
                0x30_0000,
                0x100,
                VRING_DESC_F_WRITE as u16,
                0,
            )),
        ];
        let mut chain = queue.build_desc_chain(&v[..3]).unwrap();

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

        let mut chain = queue.build_desc_chain(&v[..3]).unwrap();
        mem.write_obj::<u32>(VIRTIO_BLK_T_IN, GuestAddress(0x10_0000))
            .unwrap();
        // We shouldn't read from a device-readable buffer.
        assert_eq!(
            Request::parse(&mut chain).unwrap_err(),
            Error::UnexpectedReadOnlyDescriptor
        );

        // Invalid status address.
        let v = [
            RawDescriptor::from(SplitDescriptor::new(0x10_0000, 0x100, 0, 0)),
            RawDescriptor::from(SplitDescriptor::new(
                0x20_0000,
                0x100,
                VRING_DESC_F_WRITE as u16,
                0,
            )),
            RawDescriptor::from(SplitDescriptor::new(
                0x30_0000,
                0x200,
                VRING_DESC_F_WRITE as u16,
                0,
            )),
            RawDescriptor::from(SplitDescriptor::new(
                0x1100_0000,
                0x100,
                VRING_DESC_F_WRITE as u16,
                0,
            )),
        ];
        let req_header = RequestHeader {
            request_type: VIRTIO_BLK_T_OUT,
            _reserved: 0,
            sector: 2,
        };
        mem.write_obj::<RequestHeader>(req_header, GuestAddress(0x10_0000))
            .unwrap();

        let mut chain = queue.build_desc_chain(&v[..4]).unwrap();

        // The status descriptor would cause a write beyond capacity.
        assert_eq!(
            Request::parse(&mut chain).unwrap_err(),
            Error::GuestMemory(GuestMemoryError::InvalidGuestAddress(GuestAddress(
                0x1100_0000,
            )))
        );

        // Valid descriptor chain for OUT.
        let v = [
            RawDescriptor::from(SplitDescriptor::new(0x10_0000, 0x100, 0, 0)),
            RawDescriptor::from(SplitDescriptor::new(
                0x20_0000,
                0x100,
                VRING_DESC_F_WRITE as u16,
                0,
            )),
            RawDescriptor::from(SplitDescriptor::new(
                0x30_0000,
                0x200,
                VRING_DESC_F_WRITE as u16,
                0,
            )),
            RawDescriptor::from(SplitDescriptor::new(
                0x40_0000,
                0x100,
                VRING_DESC_F_WRITE as u16,
                0,
            )),
        ];
        let req_header = RequestHeader {
            request_type: VIRTIO_BLK_T_OUT,
            _reserved: 0,
            sector: 2,
        };
        mem.write_obj::<RequestHeader>(req_header, GuestAddress(0x10_0000))
            .unwrap();

        let mut chain = queue.build_desc_chain(&v[..4]).unwrap();

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
        assert_eq!(request.total_data_len(), 0x100 + 0x200);

        // Request header with unsupported request type.
        let req_header = RequestHeader {
            request_type: 2,
            _reserved: 0,
            sector: 2,
        };
        mem.write_obj::<RequestHeader>(req_header, GuestAddress(0x10_0000))
            .unwrap();

        let mut chain = queue.build_desc_chain(&v[..4]).unwrap();

        let request = Request::parse(&mut chain).unwrap();
        assert_eq!(request.request_type(), RequestType::Unsupported(2));

        // Valid descriptor chain for FLUSH.
        let v = [
            RawDescriptor::from(SplitDescriptor::new(0x10_0000, 0x100, 0, 0)),
            RawDescriptor::from(SplitDescriptor::new(
                0x40_0000,
                0x100,
                VRING_DESC_F_WRITE as u16,
                0,
            )),
        ];
        let req_header = RequestHeader {
            request_type: VIRTIO_BLK_T_FLUSH,
            _reserved: 0,
            sector: 0,
        };
        mem.write_obj::<RequestHeader>(req_header, GuestAddress(0x10_0000))
            .unwrap();

        let mut chain = queue.build_desc_chain(&v[..2]).unwrap();
        assert!(Request::parse(&mut chain).is_ok());
    }
}
