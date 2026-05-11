// Copyright 2022 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

//! A crate that provides vsock device specific components as described
//! by the virtio specification.

#![deny(missing_docs)]

use std::fmt::{self, Display};
use vm_memory::{ByteValued, GuestMemoryError, Le16, Le32, Le64, VolatileMemoryError};

/// Contains a vsock packet abstraction.
pub mod packet;
/// Contains the Reader/Writer-based vsock packet abstractions.
pub mod packet_rw;

/// Vsock packet parsing errors.
#[derive(Debug)]
pub enum Error {
    /// The descriptor chain could not be processed.
    InvalidChain,
    /// Too few descriptors in a descriptor chain.
    DescriptorChainTooShort,
    /// Descriptor that was too short to use.
    DescriptorLengthTooSmall,
    /// Descriptor that was too long to use.
    DescriptorLengthTooLong,
    /// Data stretches over multiple memory fragments
    FragmentedMemory,
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
            Error::InvalidChain => {
                write!(f, "The descriptor chain could not be processed.")
            }
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
            Error::FragmentedMemory => {
                write!(f, "Data stretches over multiple memory fragments.")
            }
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

/// Vsock packet result type with [`Error`].
pub type Result<T> = std::result::Result<T, Error>;

/// The vsock packet header structure.
#[repr(C, packed)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PacketHeader {
    pub(crate) src_cid: Le64,
    pub(crate) dst_cid: Le64,
    pub(crate) src_port: Le32,
    pub(crate) dst_port: Le32,
    pub(crate) len: Le32,
    pub(crate) type_: Le16,
    pub(crate) op: Le16,
    pub(crate) flags: Le32,
    pub(crate) buf_alloc: Le32,
    pub(crate) fwd_cnt: Le32,
}

// SAFETY: This is safe because `PacketHeader` contains only wrappers over POD types
// and all accesses through safe `vm-memory` API will validate any garbage that could
// be included in there.
unsafe impl ByteValued for PacketHeader {}

impl PacketHeader {
    /// Set the `src_cid` field.
    pub fn set_src_cid(&mut self, src_cid: u64) -> &mut Self {
        self.src_cid = src_cid.into();
        self
    }

    /// Set the `dst_cid` field.
    pub fn set_dst_cid(&mut self, dst_cid: u64) -> &mut Self {
        self.dst_cid = dst_cid.into();
        self
    }

    /// Set the `src_port` field.
    pub fn set_src_port(&mut self, src_port: u32) -> &mut Self {
        self.src_port = src_port.into();
        self
    }

    /// Set the `dst_port` field.
    pub fn set_dst_port(&mut self, dst_port: u32) -> &mut Self {
        self.dst_port = dst_port.into();
        self
    }

    /// Set the `len` field.
    pub fn set_len(&mut self, len: u32) -> &mut Self {
        self.len = len.into();
        self
    }

    /// Set the `type_` field.
    pub fn set_type(&mut self, type_: u16) -> &mut Self {
        self.type_ = type_.into();
        self
    }

    /// Set the `op` field.
    pub fn set_op(&mut self, op: u16) -> &mut Self {
        self.op = op.into();
        self
    }

    /// Set the `flags` field.
    pub fn set_flags(&mut self, flags: u32) -> &mut Self {
        self.flags = flags.into();
        self
    }

    /// Set a single flag (bitwise OR with existing flags).
    pub fn set_flag(&mut self, flag: u32) -> &mut Self {
        self.flags = (u32::from(self.flags) | flag).into();
        self
    }

    /// Set the `buf_alloc` field.
    pub fn set_buf_alloc(&mut self, buf_alloc: u32) -> &mut Self {
        self.buf_alloc = buf_alloc.into();
        self
    }

    /// Set the `fwd_cnt` field.
    pub fn set_fwd_cnt(&mut self, fwd_cnt: u32) -> &mut Self {
        self.fwd_cnt = fwd_cnt.into();
        self
    }

    /// Get the `src_cid` field.
    pub fn src_cid(&self) -> u64 {
        self.src_cid.into()
    }

    /// Get the `dst_cid` field.
    pub fn dst_cid(&self) -> u64 {
        self.dst_cid.into()
    }

    /// Get the `src_port` field.
    pub fn src_port(&self) -> u32 {
        self.src_port.into()
    }

    /// Get the `dst_port` field.
    pub fn dst_port(&self) -> u32 {
        self.dst_port.into()
    }

    /// Get the `len` field.
    pub fn len(&self) -> u32 {
        self.len.into()
    }

    /// Returns true if there is no payload
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Get the `type_` field.
    pub fn type_(&self) -> u16 {
        self.type_.into()
    }

    /// Get the `op` field.
    pub fn op(&self) -> u16 {
        self.op.into()
    }

    /// Get the `flags` field.
    pub fn flags(&self) -> u32 {
        self.flags.into()
    }

    /// Get the `buf_alloc` field.
    pub fn buf_alloc(&self) -> u32 {
        self.buf_alloc.into()
    }

    /// Get the `fwd_cnt` field.
    pub fn fwd_cnt(&self) -> u32 {
        self.fwd_cnt.into()
    }
}

/// The size of the header structure (when packed).
pub const PKT_HEADER_SIZE: usize = std::mem::size_of::<PacketHeader>();

#[cfg(test)]
mod tests {
    use super::*;
    impl PartialEq for Error {
        fn eq(&self, other: &Self) -> bool {
            use self::Error::*;
            match (self, other) {
                (DescriptorChainTooShort, DescriptorChainTooShort) => true,
                (DescriptorLengthTooSmall, DescriptorLengthTooSmall) => true,
                (DescriptorLengthTooLong, DescriptorLengthTooLong) => true,
                (FragmentedMemory, FragmentedMemory) => true,
                (InvalidChain, InvalidChain) => true,
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
}
