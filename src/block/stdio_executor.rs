// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Copyright © 2019 Intel Corporation
//
// Portions Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

//! A virtio block request execution abstraction.
//!
//! This module provides the following minimal abstraction for executing a virtio block device
//! request:
//!
//! - [`StdIoBackend`](struct.StdIoBackend.html) which handles the execution of the block device
//! request via [`StdIoBackend::execute`](struct.StdIoBackend.html#method.execute) method.
//! The `StdIoBackend` is wrapping the block device backend and keeps the number of sectors of the
//! backing file and its negotiated features too. This backend has to be, at least for now,
//! `io::Read` and `io::Write`. In the future, we might add some abstraction for the file access
//! operations.
//!
//! For more complex executors, that need asynchronous dispatch of requests for example, we can
//! add separate modules for those abstractions as well.

use std::fmt::{self, Display};
use std::io::{Read, Seek, SeekFrom, Write};
use std::{io, result};

use vm_memory::{Bytes, GuestMemory, GuestMemoryError};
use vmm_sys_util::file_traits::FileSync;
use vmm_sys_util::write_zeroes::{PunchHole, WriteZeroes};

use crate::block::request::VIRTIO_BLK_T_FLUSH;
use crate::block::request::{Request, RequestType};

/// Read-only device.
pub const VIRTIO_BLK_F_RO: u64 = 5;
/// Flush command supported.
pub const VIRTIO_BLK_F_FLUSH: u64 = 9;

const SECTOR_SHIFT: u8 = 9;
const SECTOR_SIZE: u64 = (0x01 as u64) << SECTOR_SHIFT;

/// Trait that keeps as supertraits the ones that are necessary for the `StdIoBackend` abstraction
/// used for the virtio block request execution.
pub trait Backend: Read + Write + Seek + FileSync + PunchHole + WriteZeroes {}

impl<B: Read + Write + Seek + FileSync + PunchHole + WriteZeroes> Backend for B {}

/// Errors encountered during request execution.
#[derive(Debug)]
pub enum Error {
    /// Error during flush request execution.
    Flush(io::Error),
    /// Invalid file access.
    InvalidAccess,
    /// Invalid data length of request.
    InvalidDataLength,
    /// Error during read request execution.
    Read(GuestMemoryError),
    /// Can't execute an operation other than `read` on a read-only device.
    ReadOnly,
    /// Error during write request execution.
    Write(GuestMemoryError),
    /// Error during file seek execution.
    Seek(io::Error),
    /// Can't execute an unsupported request.
    Unsupported(u32),
}

impl Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Error::*;

        match self {
            Flush(ref err) => write!(f, "flush execution failed: {}", err),
            InvalidAccess => write!(f, "invalid file access"),
            InvalidDataLength => write!(f, "invalid data length of request"),
            Read(ref err) => write!(f, "error accessing guest memory: {}", err),
            ReadOnly => write!(
                f,
                "can't execute an operation other than `read` on a read-only device"
            ),
            Write(ref err) => write!(f, "error during write request execution: {}", err),
            Seek(ref err) => write!(f, "file seek execution failed: {}", err),
            Unsupported(t) => write!(f, "can't execute unsupported request {}", t),
        }
    }
}

/// Dedicated [`Result`](https://doc.rust-lang.org/std/result/) type.
pub type Result<T> = result::Result<T, Error>;

/// Wraps a block device file for request execution.
///
/// # Example
///
/// ```rust
/// # use std::fs::File;
/// # use vm_virtio::block::stdio_executor::{StdIoBackend, VIRTIO_BLK_F_FLUSH};
///
/// let file = File::create("foo.txt").unwrap();
/// let request_exec = StdIoBackend::new(file, 1 << VIRTIO_BLK_F_FLUSH).unwrap();
/// ```
pub struct StdIoBackend<B: Backend> {
    /// The block device backing file.
    inner: B,
    /// The number of sectors of `inner`.
    num_sectors: u64,
    /// The disk features.
    features: u64,
}

impl<B: Backend> StdIoBackend<B> {
    /// Creates a new `StdIoBackend` based on `inner` object.
    ///
    /// # Arguments
    /// * `inner` - The block device backend.
    /// * `features` - The features that were negotiated between driver and device.
    pub fn new(mut inner: B, features: u64) -> Result<Self> {
        let disk_size = inner.seek(SeekFrom::End(0)).map_err(Error::Seek)?;
        // This check makes sense only if VIRTIO_BLK_F_BLK_SIZE feature is
        // unsupported, which might be okay to assume for now.
        // If we add support for this feature as well, this will have to be
        // restricted to -> `if disk_size % blk_size != 0`.
        if disk_size % SECTOR_SIZE != 0 {
            warn!(
                "Disk size {} is not a multiple of sector size {}; \
                 the remainder will not be visible to the guest.",
                disk_size, SECTOR_SIZE
            );
        }

        Ok(Self {
            inner,
            num_sectors: disk_size >> SECTOR_SHIFT,
            features,
        })
    }

    fn has_feature(&self, feature_pos: u64) -> bool {
        (self.features & (1u64 << feature_pos)) != 0
    }

    fn num_sectors(&self) -> u64 {
        self.num_sectors
    }

    fn check_access(&self, mut sectors_count: u64, sector: u64) -> Result<()> {
        sectors_count = sectors_count
            .checked_add(sector)
            .ok_or(Error::InvalidAccess)?;
        if sectors_count > self.num_sectors() {
            return Err(Error::InvalidAccess);
        }
        Ok(())
    }

    /// Executes `request` Request on `B` and `mem` and returns the number of bytes that were
    /// read from the device.
    ///
    /// # Arguments
    /// * `mem` - A reference to the guest memory.
    /// * `request` - The request to execute.
    pub fn execute<M: GuestMemory>(&mut self, mem: &M, request: &Request) -> Result<u32> {
        let offset = request
            .sector()
            .checked_shl(u32::from(SECTOR_SHIFT))
            .ok_or(Error::InvalidAccess)?;
        self.inner
            .seek(SeekFrom::Start(offset))
            .map_err(Error::Seek)?;
        let mut bytes_from_dev = 0;
        let request_type = request.request_type();

        if self.has_feature(VIRTIO_BLK_F_RO) && request_type != RequestType::In {
            return Err(Error::ReadOnly);
        }
        if !self.has_feature(VIRTIO_BLK_F_FLUSH) && request_type == RequestType::Flush {
            return Err(Error::Unsupported(VIRTIO_BLK_T_FLUSH));
        }

        let total_len = request.total_data_len() as u64;

        if (request_type == RequestType::In || request_type == RequestType::Out)
            && (total_len % SECTOR_SIZE != 0)
        {
            return Err(Error::InvalidDataLength);
        }

        match request_type {
            RequestType::In => {
                self.check_access(total_len / SECTOR_SIZE, request.sector())?;
                for (data_addr, data_len) in request.data() {
                    mem.read_exact_from(*data_addr, &mut self.inner, *data_len as usize)
                        .map_err(Error::Read)?;
                    bytes_from_dev += data_len;
                }
            }
            RequestType::Out => {
                self.check_access(total_len / SECTOR_SIZE, request.sector())?;
                let mut bytes_to_dev = 0;
                for (data_addr, data_len) in request.data() {
                    mem.write_all_to(*data_addr, &mut self.inner, *data_len as usize)
                        .map_err(Error::Write)?;
                    bytes_to_dev += data_len;
                }
            }
            RequestType::Flush => return self.inner.fsync().map(|_| 0).map_err(Error::Flush),
            RequestType::Unsupported(t) => return Err(Error::Unsupported(t)),
        };

        Ok(bytes_from_dev)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use vm_memory::guest_memory::Error::PartialBuffer;
    use vm_memory::{GuestAddress, GuestMemoryMmap};
    use vmm_sys_util::tempfile::TempFile;

    impl PartialEq for Error {
        fn eq(&self, other: &Self) -> bool {
            use self::Error::*;
            match (self, other) {
                (Flush(ref e), Flush(ref other_e)) => format!("{}", e).eq(&format!("{}", other_e)),
                (InvalidAccess, InvalidAccess) => true,
                (InvalidDataLength, InvalidDataLength) => true,
                (Read(ref e), Read(ref other_e)) => format!("{}", e).eq(&format!("{}", other_e)),
                (ReadOnly, ReadOnly) => true,
                (Write(ref e), Write(ref other_e)) => format!("{}", e).eq(&format!("{}", other_e)),
                (Seek(ref e), Seek(ref other_e)) => format!("{}", e).eq(&format!("{}", other_e)),
                (Unsupported(val), Unsupported(other_val)) => val == other_val,
                _ => false,
            }
        }
    }

    #[test]
    fn test_execute_request() {
        const NON_ZERO_VALUE: u8 = 0x55;

        let mut f = TempFile::new().unwrap().into_file();
        f.set_len(0x1000).unwrap();

        // Write buffer of non-zero bytes to offsets 256 and 1024.
        f.seek(SeekFrom::Start(0x100)).unwrap();
        f.write_all(&[NON_ZERO_VALUE; 0x200]).unwrap();
        f.seek(SeekFrom::Start(0x400)).unwrap();
        f.write_all(&[NON_ZERO_VALUE + 1; 0x80]).unwrap();

        let mem = GuestMemoryMmap::from_ranges(&[(GuestAddress(0), 0x1000_0000)]).unwrap();
        let flush_req = Request::new(
            RequestType::Flush,
            vec![(GuestAddress(0x100), 0x400)],
            0,
            GuestAddress(0x600),
        );

        let mut req_exec = StdIoBackend::new(f, 1 << VIRTIO_BLK_F_RO).unwrap();
        assert_eq!(
            req_exec.execute(&mem, &flush_req).unwrap_err(),
            Error::ReadOnly
        );
        // VIRTIO_BLK_F_FLUSH not negotiated.
        req_exec.features = 0;
        assert_eq!(
            req_exec.execute(&mem, &flush_req).unwrap_err(),
            Error::Unsupported(VIRTIO_BLK_T_FLUSH)
        );
        // Flush should be successful if VIRTIO_BLK_F_FLUSH is supported.
        req_exec.features = 1 << VIRTIO_BLK_F_FLUSH;
        assert_eq!(req_exec.execute(&mem, &flush_req).unwrap(), 0x00);

        let in_req = Request::new(
            RequestType::In,
            vec![(GuestAddress(0x100), 0x400), (GuestAddress(0x600), 0x200)],
            0,
            GuestAddress(0x900),
        );
        // 0x600 bytes should've been written in memory.
        assert_eq!(req_exec.execute(&mem, &in_req).unwrap(), 0x600);
        for addr in 0x100..0x1ff {
            assert_eq!(mem.read_obj::<u8>(GuestAddress(addr)).unwrap(), 0x00);
        }
        for addr in 0x200..0x3ff {
            assert_eq!(
                mem.read_obj::<u8>(GuestAddress(addr)).unwrap(),
                NON_ZERO_VALUE
            );
        }
        for addr in 0x400..0x4ff {
            assert_eq!(mem.read_obj::<u8>(GuestAddress(addr)).unwrap(), 0x00);
        }
        for addr in 0x600..0x67f {
            assert_eq!(
                mem.read_obj::<u8>(GuestAddress(addr)).unwrap(),
                NON_ZERO_VALUE + 1
            );
        }
        for addr in 0x680..0x7ff {
            assert_eq!(mem.read_obj::<u8>(GuestAddress(addr)).unwrap(), 0x00);
        }

        let mem = GuestMemoryMmap::from_ranges(&[(GuestAddress(0), 0x1000_0000)]).unwrap();
        let out_req = Request::new(
            RequestType::Out,
            vec![(GuestAddress(0x100), 0x400), (GuestAddress(0x800), 0x200)],
            1,
            GuestAddress(0x200),
        );
        // Clear the file.
        req_exec.inner.seek(SeekFrom::Start(0x00)).unwrap();
        req_exec.inner.write_zeroes(0x1000).unwrap();

        mem.write_slice(&[NON_ZERO_VALUE; 0x200], GuestAddress(0x200))
            .unwrap();
        mem.write_slice(&[NON_ZERO_VALUE; 0x100], GuestAddress(0x880))
            .unwrap();
        // We will write in file at sector 1 (offset 0x200) 0x400 bytes from 0x100 guest memory
        // address and 0x200 bytes from 0x800 address. 0 bytes should've been written in memory.
        assert_eq!(req_exec.execute(&mem, &out_req).unwrap(), 0x00);

        req_exec.inner.seek(SeekFrom::Start(0x00)).unwrap();
        let mut v = vec![0x00; 0x300];
        assert_eq!(req_exec.inner.read(&mut v).unwrap(), 0x300);
        assert_eq!(v, vec![0x00; 0x300]);

        // We are at offset 0x300.
        v = vec![0x00; 0x200];
        assert_eq!(req_exec.inner.read(&mut v).unwrap(), 0x200);
        assert_eq!(v, vec![NON_ZERO_VALUE; 0x200]);

        // We are at offset 0x500.
        v = vec![0x00; 0x100];
        assert_eq!(req_exec.inner.read(&mut v).unwrap(), 0x100);
        assert_eq!(v, vec![0x00; 0x100]);

        // We are at offset 0x600.
        v = vec![0x00; 0x80];
        assert_eq!(req_exec.inner.read(&mut v).unwrap(), 0x80);
        assert_eq!(v, vec![0x00; 0x80]);

        // We are at offset 0x680.
        v = vec![0x00; 0x100];
        assert_eq!(req_exec.inner.read(&mut v).unwrap(), 0x100);
        assert_eq!(v, vec![NON_ZERO_VALUE; 0x100]);

        // We are at offset 0x780.
        v = vec![0x00; 0x80];
        assert_eq!(req_exec.inner.read(&mut v).unwrap(), 0x80);
        assert_eq!(v, vec![0x00; 0x80]);

        // Writing 512 bytes to the last sector should be successful.
        let out_req = Request::new(
            RequestType::Out,
            vec![(GuestAddress(0x100), 0x200)],
            7,
            GuestAddress(0x200),
        );
        assert!(req_exec.execute(&mem, &out_req).is_ok());

        // Writing 1024 bytes to the last sector should not be successful.
        let out_req = Request::new(
            RequestType::Out,
            vec![(GuestAddress(0x100), 0x400)],
            7,
            GuestAddress(0x200),
        );
        assert_eq!(
            req_exec.execute(&mem, &out_req).unwrap_err(),
            Error::InvalidAccess
        );

        // Invalid data length for IN/OUT request.
        let out_req = Request::new(
            RequestType::Out,
            vec![(GuestAddress(0x100), 0x400), (GuestAddress(0x500), 0x100)],
            2,
            GuestAddress(0x200),
        );
        assert_eq!(
            req_exec.execute(&mem, &out_req).unwrap_err(),
            Error::InvalidDataLength
        );
        let in_req = Request::new(
            RequestType::In,
            vec![(GuestAddress(0x100), 0x201)],
            2,
            GuestAddress(0x200),
        );
        assert_eq!(
            req_exec.execute(&mem, &in_req).unwrap_err(),
            Error::InvalidDataLength
        );

        // It's ok to have partial data lengths that are not multiple of 512 bytes as long as their
        // sum is a multiple.
        let in_req = Request::new(
            RequestType::In,
            vec![(GuestAddress(0x100), 0x500), (GuestAddress(0x500), 0x300)],
            2,
            GuestAddress(0x200),
        );
        assert_eq!(req_exec.execute(&mem, &in_req).unwrap(), 0x800);

        // Invalid memory address for write operation.
        let out_req = Request::new(
            RequestType::Out,
            vec![(GuestAddress(0xFFF_FFF0), 0x200)],
            7,
            GuestAddress(0x200),
        );
        assert_eq!(
            req_exec.execute(&mem, &out_req).unwrap_err(),
            Error::Write(PartialBuffer {
                expected: 512,
                completed: 16
            })
        );

        // Invalid memory address for read operation.
        let in_req = Request::new(
            RequestType::In,
            vec![(GuestAddress(0xFFF_FFF0), 0x200)],
            7,
            GuestAddress(0x200),
        );
        assert_eq!(
            req_exec.execute(&mem, &in_req).unwrap_err(),
            Error::Read(PartialBuffer {
                expected: 512,
                completed: 16
            })
        );

        // Invalid request type.
        let invalid_req = Request::new(
            RequestType::Unsupported(8),
            vec![(GuestAddress(0x100), 0x200)],
            7,
            GuestAddress(0x200),
        );
        assert_eq!(
            req_exec.execute(&mem, &invalid_req).unwrap_err(),
            Error::Unsupported(8)
        );
    }
}
