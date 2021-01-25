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
use std::{io, mem, result};

use vm_memory::{Address, ByteValued, Bytes, GuestMemory, GuestMemoryError};
use vmm_sys_util::file_traits::FileSync;
use vmm_sys_util::write_zeroes::{PunchHole, WriteZeroesAt};

use crate::block::defs::VIRTIO_BLK_T_GET_ID;
use crate::block::{
    defs::{
        SECTOR_SHIFT, SECTOR_SIZE, VIRTIO_BLK_F_DISCARD, VIRTIO_BLK_F_FLUSH, VIRTIO_BLK_F_RO,
        VIRTIO_BLK_F_WRITE_ZEROES, VIRTIO_BLK_ID_BYTES, VIRTIO_BLK_S_IOERR, VIRTIO_BLK_S_OK,
        VIRTIO_BLK_S_UNSUPP, VIRTIO_BLK_T_DISCARD, VIRTIO_BLK_T_FLUSH, VIRTIO_BLK_T_WRITE_ZEROES,
    },
    request::{Request, RequestType},
};

/// Trait that keeps as supertraits the ones that are necessary for the `StdIoBackend` abstraction
/// used for the virtio block request execution.
pub trait Backend: Read + Write + Seek + FileSync + PunchHole + WriteZeroesAt {}

impl<B: Read + Write + Seek + FileSync + PunchHole + WriteZeroesAt> Backend for B {}

/// One or more `DiscardWriteZeroes` structs are used to describe the data for
/// discard or write zeroes command.
#[derive(Copy, Clone, Debug, Default)]
#[repr(C)]
struct DiscardWriteZeroes {
    sector: u64,
    num_sectors: u32,
    flags: u32,
}

impl DiscardWriteZeroes {
    // The least significant bit from `flags` set -> the targeted range should be unmapped
    // (only valid for write zeroes command).
    const UNMAP: u32 = 1;
    // Size of DiscardWriteZeroes struct.
    const LEN: u64 = mem::size_of::<DiscardWriteZeroes>() as u64;
}

// Safe because DiscardWriteZeroes contains only plain data.
unsafe impl ByteValued for DiscardWriteZeroes {}

/// Errors encountered during request execution.
#[derive(Debug)]
pub enum Error {
    ///  Error during write zeroes request execution.
    DiscardWriteZeroes(io::Error),
    /// Error during flush request execution.
    Flush(io::Error),
    /// Invalid memory address.
    GuestMemory(GuestMemoryError),
    /// Invalid file access.
    InvalidAccess,
    /// Discard/Write Zeroes command has invalid flags.
    InvalidFlags,
    /// Invalid data length of request.
    InvalidDataLength,
    /// Overflow when computing memory address.
    Overflow,
    /// Error during read request execution.
    // The `u32` represents the number of bytes written to memory until the error occurred.
    Read(GuestMemoryError, u32),
    /// Can't execute an operation other than `read` on a read-only device.
    ReadOnly,
    /// Error during write request execution.
    Write(GuestMemoryError),
    /// Error during file seek execution.
    Seek(io::Error),
    /// Can't execute an unsupported request.
    Unsupported(u32),
}

impl Error {
    fn status(&self) -> u8 {
        match self {
            Error::DiscardWriteZeroes(_) => VIRTIO_BLK_S_IOERR,
            Error::Flush(_) => VIRTIO_BLK_S_IOERR,
            Error::GuestMemory(_) => VIRTIO_BLK_S_IOERR,
            Error::InvalidAccess => VIRTIO_BLK_S_IOERR,
            Error::InvalidFlags => VIRTIO_BLK_S_UNSUPP,
            Error::InvalidDataLength => VIRTIO_BLK_S_IOERR,
            Error::Overflow => VIRTIO_BLK_S_IOERR,
            Error::Read(_, _) => VIRTIO_BLK_S_IOERR,
            Error::ReadOnly => VIRTIO_BLK_S_IOERR,
            Error::Write(_) => VIRTIO_BLK_S_IOERR,
            Error::Seek(_) => VIRTIO_BLK_S_IOERR,
            Error::Unsupported(_) => VIRTIO_BLK_S_UNSUPP,
        }
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Error::*;

        match self {
            DiscardWriteZeroes(ref err) => {
                write!(f, "discard/write zeroes execution failed: {}", err)
            }
            Flush(ref err) => write!(f, "flush execution failed: {}", err),
            GuestMemory(ref err) => write!(f, "error accessing guest memory: {}", err),
            InvalidAccess => write!(f, "invalid file access"),
            InvalidDataLength => write!(f, "invalid data length of request"),
            InvalidFlags => write!(f, "invalid flags for discard/write zeroes request"),
            Overflow => write!(f, "overflow when computing memory address"),
            Read(ref err, _) => write!(f, "error during read request execution: {}", err),
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

/// Errors encountered while processing a request execution result.
#[derive(Debug)]
pub enum ProcessReqError {
    /// Bad memory access.
    GuestMemory(GuestMemoryError),
    /// Overflow occurred when computing number of bytes written to memory.
    Overflow,
}

impl From<vm_memory::GuestMemoryError> for ProcessReqError {
    fn from(e: vm_memory::GuestMemoryError) -> Self {
        ProcessReqError::GuestMemory(e)
    }
}

/// Dedicated [`Result`](https://doc.rust-lang.org/std/result/) type.
pub type Result<T> = result::Result<T, Error>;

/// Wraps a block device file for request execution.
///
/// # Example
///
/// ```rust
/// # use vm_virtio::block::{
/// #     defs::{VIRTIO_BLK_F_FLUSH, VIRTIO_BLK_ID_BYTES},
/// #     stdio_executor::StdIoBackend,
/// # };
/// # use vmm_sys_util::tempfile::TempFile;
/// let file = TempFile::new().unwrap();
/// let request_exec = StdIoBackend::new(file.into_file(), 1 << VIRTIO_BLK_F_FLUSH).unwrap();
/// ```
pub struct StdIoBackend<B: Backend> {
    /// The block device backing file.
    inner: B,
    /// The number of sectors of `inner`.
    num_sectors: u64,
    /// The disk features.
    features: u64,
    /// The device id string, which is a NUL-padded ASCII string up to 20 bytes long.
    /// If the string is 20 bytes long, then there is no NUL terminator.
    device_id: Option<[u8; VIRTIO_BLK_ID_BYTES]>,
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
            device_id: None,
        })
    }

    /// Sets the `device_id`.
    ///
    /// # Arguments
    /// * `device_id` - The block device id. On Linux guests, this information can be read from
    ///                 `/sys/block/<device>/serial`.
    pub fn with_device_id(mut self, device_id: [u8; VIRTIO_BLK_ID_BYTES]) -> Self {
        self.device_id = Some(device_id);
        self
    }

    fn has_feature(&self, feature_pos: u64) -> bool {
        (self.features & (1u64 << feature_pos)) != 0
    }

    fn num_sectors(&self) -> u64 {
        self.num_sectors
    }

    /// Processes the `request` execution result, writes its status in memory and returns the used
    /// length (i.e. the total number of bytes written into the memory buffer, including the status
    /// byte).
    ///
    /// # Arguments
    /// * `mem` - A reference to the guest memory.
    /// * `request` - The request to execute.
    pub fn process_request<M: GuestMemory>(
        &mut self,
        mem: &M,
        request: &Request,
    ) -> result::Result<u32, ProcessReqError> {
        let (status, length) = match self.execute(mem, request) {
            Ok(length) => (VIRTIO_BLK_S_OK, length),
            Err(e) => {
                error!("failed executing block request: {}", e);
                match e {
                    Error::Read(_, bytes_to_mem) => (e.status(), bytes_to_mem),
                    _ => (e.status(), 0),
                }
            }
        };
        mem.write_obj(status, request.status_addr())?;
        // Adding +1 here for the status byte. `length` should not be u32::MAX since it is expected
        // to be a multiple of SECTOR_SIZE, but using `checked_add` here for safety.
        length.checked_add(1).ok_or(ProcessReqError::Overflow)
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

    fn check_request(&self, request_type: RequestType) -> Result<()> {
        if self.has_feature(VIRTIO_BLK_F_RO) && request_type != RequestType::In {
            return Err(Error::ReadOnly);
        }
        match request_type {
            RequestType::Flush if !self.has_feature(VIRTIO_BLK_F_FLUSH) => {
                Err(Error::Unsupported(VIRTIO_BLK_T_FLUSH))
            }
            RequestType::Discard if !self.has_feature(VIRTIO_BLK_F_DISCARD) => {
                Err(Error::Unsupported(VIRTIO_BLK_T_DISCARD))
            }
            RequestType::WriteZeroes if !self.has_feature(VIRTIO_BLK_F_WRITE_ZEROES) => {
                Err(Error::Unsupported(VIRTIO_BLK_T_WRITE_ZEROES))
            }
            _ => Ok(()),
        }
    }

    /// Executes `request` Request on `B` and `mem` and returns the number of bytes that were
    /// written into the memory buffer during execution (status byte not included).
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
        // This will count the number of bytes written by the device to the memory. It must fit in
        // an u32 for further writing in the used ring.
        let mut bytes_to_mem: u32 = 0;
        let request_type = request.request_type();
        self.check_request(request_type)?;

        let total_len = request.total_data_len();

        if (request_type == RequestType::In || request_type == RequestType::Out)
            && (total_len % SECTOR_SIZE != 0)
        {
            return Err(Error::InvalidDataLength);
        }

        match request_type {
            RequestType::In => {
                self.check_access(total_len / SECTOR_SIZE, request.sector())?;
                // Total data length should fit in an u32 for further writing in the used ring.
                if total_len > u32::MAX as u64 {
                    return Err(Error::InvalidDataLength);
                }
                for (data_addr, data_len) in request.data() {
                    mem.read_exact_from(*data_addr, &mut self.inner, *data_len as usize)
                        .map_err(|e| {
                            if let GuestMemoryError::PartialBuffer {
                                completed,
                                expected: _,
                            } = e
                            {
                                // The `as u32` cast is safe, since completed < data_len (which is
                                // an u32).
                                bytes_to_mem += completed as u32
                            }
                            Error::Read(e, bytes_to_mem)
                        })?;
                    // This can not overflow since we checked right before the loop that `total_len`
                    // fits in an u32.
                    bytes_to_mem += data_len;
                }
            }
            RequestType::Out => {
                self.check_access(total_len / SECTOR_SIZE, request.sector())?;
                for (data_addr, data_len) in request.data() {
                    mem.write_all_to(*data_addr, &mut self.inner, *data_len as usize)
                        .map_err(Error::Write)?;
                }
            }
            RequestType::Flush => return self.inner.fsync().map(|_| 0).map_err(Error::Flush),
            RequestType::GetDeviceID => {
                let device_id = self
                    .device_id
                    .ok_or(Error::Unsupported(VIRTIO_BLK_T_GET_ID))?;
                // The length of data MUST be VIRTIO_BLK_ID_BYTES bytes for VIRTIO_BLK_T_GET_ID
                // requests.
                if total_len != VIRTIO_BLK_ID_BYTES as u64 {
                    return Err(Error::InvalidDataLength);
                }
                for (data_addr, data_len) in request.data() {
                    // The device_id accesses are safe because we checked that the total data length
                    // is VIRTIO_BLK_ID_BYTES, which is the size of the id as well.
                    mem.read_exact_from(
                        *data_addr,
                        &mut &device_id[bytes_to_mem as usize..(*data_len + bytes_to_mem) as usize],
                        *data_len as usize,
                    )
                    .map_err(|e| {
                        if let GuestMemoryError::PartialBuffer {
                            completed,
                            expected: _,
                        } = e
                        {
                            // The `as u32` cast is safe, since completed < data_len (which is an
                            // u32).
                            bytes_to_mem += completed as u32
                        }
                        Error::Read(e, bytes_to_mem)
                    })?;
                    // This can not overflow since total data length = VIRTIO_BLK_ID_BYTES for sure
                    // at this point.
                    bytes_to_mem += data_len;
                }
            }
            RequestType::Discard | RequestType::WriteZeroes => {
                for (data_addr, data_len) in request.data() {
                    // We support for now only data descriptors with the `len` field = multiple of
                    // the size of `virtio_blk_discard_write_zeroes` segment. The specification,
                    // however, requires that only `total_len` be such multiple (a segment can be
                    // divided between several descriptors). Once we switch to a more general
                    // approach regarding how we store and parse the device buffers, we'll fix this
                    // too.
                    if *data_len as u64 % DiscardWriteZeroes::LEN != 0 {
                        return Err(Error::InvalidDataLength);
                    }
                    let mut available_bytes = *data_len as u64;
                    let mut crt_addr = *data_addr;
                    crt_addr
                        .checked_add(*data_len as u64)
                        .ok_or(Error::Overflow)?;

                    while available_bytes >= DiscardWriteZeroes::LEN {
                        let segment = mem.read_obj(crt_addr).map_err(Error::GuestMemory)?;
                        self.handle_discard_write_zeroes(&segment, request.request_type())?;
                        // Using `unchecked_add` here, since the overflow is not possible at this
                        // point (it is checked right before the current loop) and `read_obj` fails
                        // if the memory access is invalid.
                        crt_addr = crt_addr.unchecked_add(DiscardWriteZeroes::LEN);
                        available_bytes -= DiscardWriteZeroes::LEN;
                    }
                }
            }
            RequestType::Unsupported(t) => return Err(Error::Unsupported(t)),
        };

        Ok(bytes_to_mem)
    }

    fn handle_discard_write_zeroes(
        &mut self,
        segment: &DiscardWriteZeroes,
        request_type: RequestType,
    ) -> Result<u32> {
        let sector = segment.sector;
        let num_sectors = segment.num_sectors;
        let flags = segment.flags;

        // For Discard, unmap bit (the least significant bit from segment flags) MUST be 0, for
        // Write Zeroes it can be either 0 or 1.
        // The other bits are reserved and MUST not be set (for both request types).
        // If any of these conditions are not met, status must be set to VIRTIO_BLK_S_UNSUPP.
        let valid_flags = if request_type == RequestType::WriteZeroes {
            DiscardWriteZeroes::UNMAP
        } else {
            0
        };
        if (flags & !valid_flags) != 0 {
            return Err(Error::InvalidFlags);
        }

        let offset = sector
            .checked_shl(u32::from(SECTOR_SHIFT))
            .ok_or(Error::InvalidAccess)?;
        let length = u64::from(num_sectors)
            .checked_shl(u32::from(SECTOR_SHIFT))
            .ok_or(Error::InvalidAccess)?;
        self.check_access(num_sectors as u64, sector)?;

        if request_type == RequestType::Discard {
            // Since Discard is just a hint and some filesystems may not implement
            // FALLOC_FL_PUNCH_HOLE, ignore punch_hole() errors.
            let _ = self.inner.punch_hole(offset, length);
        } else {
            // If unmap is set, try at first to punch a hole, if it fails, fall back to just
            // writing zeroes.
            // After a write zeroes command is completed, reads of the specified ranges of sectors
            // MUST return zeroes, independent of unmap value.
            if flags & DiscardWriteZeroes::UNMAP == 0
                || self.inner.punch_hole(offset, length).is_err()
            {
                self.inner
                    .write_all_zeroes_at(offset, length as usize)
                    .map_err(Error::DiscardWriteZeroes)?;
            }
        }
        Ok(0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use vm_memory::guest_memory::Error::{InvalidGuestAddress, PartialBuffer};
    use vm_memory::{GuestAddress, GuestMemoryMmap};
    use vmm_sys_util::tempfile::TempFile;

    impl PartialEq for Error {
        fn eq(&self, other: &Self) -> bool {
            use self::Error::*;
            match (self, other) {
                (DiscardWriteZeroes(ref e), DiscardWriteZeroes(ref other_e)) => {
                    format!("{}", e).eq(&format!("{}", other_e))
                }
                (Flush(ref e), Flush(ref other_e)) => format!("{}", e).eq(&format!("{}", other_e)),
                (GuestMemory(ref e), GuestMemory(ref other_e)) => {
                    format!("{}", e).eq(&format!("{}", other_e))
                }
                (InvalidAccess, InvalidAccess) => true,
                (InvalidDataLength, InvalidDataLength) => true,
                (InvalidFlags, InvalidFlags) => true,
                (Overflow, Overflow) => true,
                (Read(ref e, bytes), Read(ref other_e, other_bytes)) => {
                    format!("{}", e).eq(&format!("{}", other_e)) && bytes == other_bytes
                }
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
        req_exec.inner.write_zeroes_at(0x00, 0x1000).unwrap();

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
            Error::Read(
                PartialBuffer {
                    expected: 512,
                    completed: 16
                },
                16
            )
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

        // Let's create a file large enough for the request.
        let f = TempFile::new().unwrap().into_file();
        f.set_len(u32::MAX as u64 * 2).unwrap();
        let mut req_exec = StdIoBackend::new(f, 0).unwrap();

        // Total data length > u32::MAX.
        let invalid_req = Request::new(
            RequestType::In,
            vec![
                (GuestAddress(0x100), u32::MAX - SECTOR_SIZE as u32 + 1),
                (GuestAddress(0x1000), SECTOR_SIZE as u32),
            ],
            0,
            GuestAddress(0x200),
        );
        assert_eq!(
            req_exec.execute(&mem, &invalid_req).unwrap_err(),
            Error::InvalidDataLength
        );
    }

    #[test]
    fn test_discard_wr_zeroes_request() {
        const NON_ZERO_VALUE: u8 = 0x55;

        let f = TempFile::new().unwrap().into_file();
        f.set_len(0x1000).unwrap();

        let mem = GuestMemoryMmap::from_ranges(&[(GuestAddress(0), 0x1000_0000)]).unwrap();

        let mut req_exec = StdIoBackend::new(
            f,
            (1 << VIRTIO_BLK_F_DISCARD) | (1 << VIRTIO_BLK_F_WRITE_ZEROES),
        )
        .unwrap();

        let out_req = Request::new(
            RequestType::Out,
            vec![(GuestAddress(0x100), 0x400), (GuestAddress(0x800), 0x200)],
            1,
            GuestAddress(0x200),
        );

        mem.write_slice(&[NON_ZERO_VALUE; 0x200], GuestAddress(0x200))
            .unwrap();
        mem.write_slice(&[NON_ZERO_VALUE; 0x100], GuestAddress(0x880))
            .unwrap();
        // We will write in file at sector 1 (offset 0x200) 0x400 bytes from 0x100 guest memory
        // address and 0x200 bytes from 0x800 address. 0 bytes should've been written in memory.
        assert_eq!(req_exec.execute(&mem, &out_req).unwrap(), 0x00);

        // Let's write some more bytes to the file.
        mem.write_slice(&[NON_ZERO_VALUE + 1; 0x600], GuestAddress(0x3100))
            .unwrap();

        // Write at offset 0x600 in file, 800 bytes: the first 100 bytes = 0, the next 600 bytes =
        // = NON_ZERO_VALUE + 1 and the last 100 bytes = 0; and then at offset 0x600 + 0x800 =
        // = 0xE00, which is the last sector, 200 bytes = NON_ZERO_VALUE.
        let out_req = Request::new(
            RequestType::Out,
            vec![(GuestAddress(0x3000), 0x800), (GuestAddress(0x200), 0x200)],
            3,
            GuestAddress(0x200),
        );
        assert!(req_exec.execute(&mem, &out_req).is_ok());

        // Test write zeroes request.
        let wr_zeroes_1 = DiscardWriteZeroes {
            sector: 2,
            num_sectors: 2,
            flags: 0,
        };
        mem.write_obj::<DiscardWriteZeroes>(wr_zeroes_1, GuestAddress(0x1000))
            .unwrap();
        let wr_zeroes_2 = DiscardWriteZeroes {
            sector: 5,
            num_sectors: 1,
            flags: 0,
        };
        mem.write_obj::<DiscardWriteZeroes>(wr_zeroes_2, GuestAddress(0x4000))
            .unwrap();

        let wr_zeroes_req = Request::new(
            RequestType::WriteZeroes,
            vec![
                (GuestAddress(0x1000), DiscardWriteZeroes::LEN as u32),
                (GuestAddress(0x4000), DiscardWriteZeroes::LEN as u32),
            ],
            2,
            GuestAddress(0x2000),
        );

        // 0 bytes should've been written in memory.
        assert_eq!(req_exec.execute(&mem, &wr_zeroes_req).unwrap(), 0x00);

        req_exec.inner.seek(SeekFrom::Start(0x00)).unwrap();
        let mut v = vec![0x00; 0x300];
        assert_eq!(req_exec.inner.read(&mut v).unwrap(), 0x300);
        assert_eq!(v, vec![0x00; 0x300]);

        // We are at offset 0x300.
        v = vec![0x00; 0x100];
        assert_eq!(req_exec.inner.read(&mut v).unwrap(), 0x100);
        assert_eq!(v, vec![NON_ZERO_VALUE; 0x100]);

        // We are at offset 0x400 -> 0x400 bytes should've been zeroed out.
        v = vec![0x00; 0x400];
        assert_eq!(req_exec.inner.read(&mut v).unwrap(), 0x400);
        assert_eq!(v, vec![0x00; 0x400]);

        // We are at offset 0x800.
        v = vec![0x00; 0x200];
        assert_eq!(req_exec.inner.read(&mut v).unwrap(), 0x200);
        assert_eq!(v, vec![NON_ZERO_VALUE + 1; 0x200]);

        // We are at offset 0xA00 -> 0x200 bytes should've been zeroed out.
        v = vec![0x00; 0x200];
        assert_eq!(req_exec.inner.read(&mut v).unwrap(), 0x200);
        assert_eq!(v, vec![0; 0x200]);

        // We are at offset 0xC00.
        v = vec![0x00; 0x100];
        assert_eq!(req_exec.inner.read(&mut v).unwrap(), 0x100);
        assert_eq!(v, vec![NON_ZERO_VALUE + 1; 0x100]);

        // We are at offset 0xD00.
        v = vec![0x00; 0x100];
        assert_eq!(req_exec.inner.read(&mut v).unwrap(), 0x100);
        assert_eq!(v, vec![0; 0x100]);

        // We are at offset 0xE00.
        v = vec![0x00; 0x200];
        assert_eq!(req_exec.inner.read(&mut v).unwrap(), 0x200);
        assert_eq!(v, vec![NON_ZERO_VALUE; 0x200]);

        // Test discard request.
        let discard_req = DiscardWriteZeroes {
            sector: 7,
            num_sectors: 1,
            flags: 0,
        };
        mem.write_obj::<DiscardWriteZeroes>(discard_req, GuestAddress(0x1000))
            .unwrap();

        let discard_req = Request::new(
            RequestType::Discard,
            vec![(GuestAddress(0x1000), DiscardWriteZeroes::LEN as u32)],
            7,
            GuestAddress(0x2000),
        );

        // 0 bytes should've been written in memory.
        assert_eq!(req_exec.execute(&mem, &discard_req).unwrap(), 0x00);

        req_exec.inner.seek(SeekFrom::Start(0xE00)).unwrap();
        let mut v = vec![0x00; 0x200];
        assert_eq!(req_exec.inner.read(&mut v).unwrap(), 0x200);
        assert_eq!(v, vec![0x00; 0x200]);

        // Even though we punched a hole at the end of the file, the file size should remain the
        // same since FALLOC_FL_PUNCH_HOLE is used with FALLOC_FL_KEEP_SIZE.
        assert_eq!(req_exec.inner.metadata().unwrap().len(), 0x1000);

        // Test that write zeroes request with unmap bit set is okay.
        let wr_zeroes_req = DiscardWriteZeroes {
            sector: 4,
            num_sectors: 1,
            flags: 0x0001,
        };
        mem.write_obj::<DiscardWriteZeroes>(wr_zeroes_req, GuestAddress(0x1000))
            .unwrap();

        let wr_zeroes_req = Request::new(
            RequestType::WriteZeroes,
            vec![(GuestAddress(0x1000), DiscardWriteZeroes::LEN as u32)],
            7,
            GuestAddress(0x2000),
        );

        req_exec.inner.seek(SeekFrom::Start(0x800)).unwrap();
        let mut v = vec![0x00; 0x200];
        assert_eq!(req_exec.inner.read(&mut v).unwrap(), 0x200);
        // Data is != 0 before the write zeroes request.
        assert_eq!(v, vec![NON_ZERO_VALUE + 1; 0x200]);
        // Let's write some data in the file right before and after the fourth sector to confirm
        // that those regions won't be zeroed out.
        // After the fourth sector:
        let v = vec![NON_ZERO_VALUE + 2; 0x200];
        assert_eq!(req_exec.inner.write(&v).unwrap(), 0x200);
        // Before the fourth sector:
        req_exec.inner.seek(SeekFrom::Start(0x600)).unwrap();
        assert_eq!(req_exec.inner.write(&v).unwrap(), 0x200);

        // 0 bytes should've been written in memory.
        assert_eq!(req_exec.execute(&mem, &wr_zeroes_req).unwrap(), 0x00);

        req_exec.inner.seek(SeekFrom::Start(0x600)).unwrap();
        let mut v = vec![0x00; 0x200];
        assert_eq!(req_exec.inner.read(&mut v).unwrap(), 0x200);
        assert_eq!(v, vec![NON_ZERO_VALUE + 2; 0x200]);
        assert_eq!(req_exec.inner.read(&mut v).unwrap(), 0x200);
        assert_eq!(v, vec![0; 0x200]);
        assert_eq!(req_exec.inner.read(&mut v).unwrap(), 0x200);
        assert_eq!(v, vec![NON_ZERO_VALUE + 2; 0x200]);

        // VIRTIO_BLK_F_DISCARD not negotiated.
        req_exec.features = 0;
        assert_eq!(
            req_exec.execute(&mem, &discard_req).unwrap_err(),
            Error::Unsupported(VIRTIO_BLK_T_DISCARD)
        );
        req_exec.features = (1 << VIRTIO_BLK_F_DISCARD) | (1 << VIRTIO_BLK_F_WRITE_ZEROES);

        // Test discard request with invalid data length.
        let discard_req = Request::new(
            RequestType::Discard,
            vec![
                (GuestAddress(0x5000), DiscardWriteZeroes::LEN as u32 / 2),
                (GuestAddress(0x1000), DiscardWriteZeroes::LEN as u32 / 2),
            ],
            7,
            GuestAddress(0x2000),
        );
        assert_eq!(
            req_exec.execute(&mem, &discard_req).unwrap_err(),
            Error::InvalidDataLength
        );

        let discard_req = Request::new(
            RequestType::Discard,
            vec![(GuestAddress(0x1000), DiscardWriteZeroes::LEN as u32 - 1)],
            7,
            GuestAddress(0x2000),
        );
        assert_eq!(
            req_exec.execute(&mem, &discard_req).unwrap_err(),
            Error::InvalidDataLength
        );

        // Test discard request with an invalid memory access that would cause an overflow.
        let discard_req = Request::new(
            RequestType::Discard,
            vec![(
                GuestAddress(u64::MAX - DiscardWriteZeroes::LEN),
                2 * DiscardWriteZeroes::LEN as u32,
            )],
            7,
            GuestAddress(0x2000),
        );
        assert_eq!(
            req_exec.execute(&mem, &discard_req).unwrap_err(),
            Error::Overflow
        );

        // Test discard request with invalid sectors.
        let discard_req = DiscardWriteZeroes {
            sector: 7,
            num_sectors: 2,
            flags: 0,
        };
        mem.write_obj::<DiscardWriteZeroes>(discard_req, GuestAddress(0x1000))
            .unwrap();

        let discard_req = Request::new(
            RequestType::Discard,
            vec![(GuestAddress(0x1000), DiscardWriteZeroes::LEN as u32)],
            7,
            GuestAddress(0x2000),
        );
        assert_eq!(
            req_exec.execute(&mem, &discard_req).unwrap_err(),
            Error::InvalidAccess
        );

        // Test discard request with invalid flags (unmap bit set).
        let discard_req = DiscardWriteZeroes {
            sector: 3,
            num_sectors: 2,
            flags: 0x0001,
        };
        mem.write_obj::<DiscardWriteZeroes>(discard_req, GuestAddress(0x1000))
            .unwrap();

        let discard_req = Request::new(
            RequestType::Discard,
            vec![(GuestAddress(0x1000), DiscardWriteZeroes::LEN as u32)],
            7,
            GuestAddress(0x2000),
        );
        assert_eq!(
            req_exec.execute(&mem, &discard_req).unwrap_err(),
            Error::InvalidFlags
        );

        // Test write zeroes request with invalid flags (reserved bit set).
        let wr_zeroes_req = DiscardWriteZeroes {
            sector: 3,
            num_sectors: 2,
            flags: 0xA000,
        };
        mem.write_obj::<DiscardWriteZeroes>(wr_zeroes_req, GuestAddress(0x1000))
            .unwrap();

        let wr_zeroes_req = Request::new(
            RequestType::WriteZeroes,
            vec![(GuestAddress(0x1000), DiscardWriteZeroes::LEN as u32)],
            7,
            GuestAddress(0x2000),
        );
        assert_eq!(
            req_exec.execute(&mem, &wr_zeroes_req).unwrap_err(),
            Error::InvalidFlags
        );

        // Invalid data address.
        let wr_zeroes_req = Request::new(
            RequestType::WriteZeroes,
            vec![(GuestAddress(0x1100_0000), DiscardWriteZeroes::LEN as u32)],
            7,
            GuestAddress(0x2000),
        );

        assert_eq!(
            req_exec.execute(&mem, &wr_zeroes_req).unwrap_err(),
            Error::GuestMemory(InvalidGuestAddress(GuestAddress(0x1100_0000)))
        );
    }

    #[test]
    fn test_get_device_id() {
        let f = TempFile::new().unwrap().into_file();
        f.set_len(0x1000).unwrap();

        let mem = GuestMemoryMmap::from_ranges(&[(GuestAddress(0), 0x1000_0000)]).unwrap();
        let dev_id = [
            0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x00A, 0x0B, 0x0C, 0x0D, 0x0E,
            0x0F, 0x10, 0x11, 0x12, 0x13, 0x14,
        ];
        let mut req_exec = StdIoBackend::new(f, 0).unwrap();

        let get_id_req = Request::new(
            RequestType::GetDeviceID,
            vec![(GuestAddress(0x100), VIRTIO_BLK_ID_BYTES as u32)],
            1,
            GuestAddress(0x200),
        );

        // Device id was not set, so a GetDeviceID request is unsupported.
        assert_eq!(
            req_exec.execute(&mem, &get_id_req).unwrap_err(),
            Error::Unsupported(VIRTIO_BLK_T_GET_ID)
        );

        req_exec = req_exec.with_device_id(dev_id);

        // Invalid get device ID request, data length should be VIRTIO_BLK_ID_BYTES.
        let get_id_req = Request::new(
            RequestType::GetDeviceID,
            vec![(GuestAddress(0x100), VIRTIO_BLK_ID_BYTES as u32 - 1)],
            1,
            GuestAddress(0x200),
        );

        assert_eq!(
            req_exec.execute(&mem, &get_id_req).unwrap_err(),
            Error::InvalidDataLength
        );

        let get_id_req = Request::new(
            RequestType::GetDeviceID,
            vec![(GuestAddress(0x100), VIRTIO_BLK_ID_BYTES as u32)],
            1,
            GuestAddress(0x200),
        );

        // VIRTIO_BLK_ID_BYTES bytes should've been written in memory.
        assert_eq!(
            req_exec.execute(&mem, &get_id_req).unwrap(),
            VIRTIO_BLK_ID_BYTES as u32
        );
        let mut buf = [0x00; VIRTIO_BLK_ID_BYTES];
        mem.read_slice(&mut buf, GuestAddress(0x100)).unwrap();
        assert_eq!(buf, dev_id);

        let get_id_req = Request::new(
            RequestType::GetDeviceID,
            vec![(GuestAddress(0x100), 0x08), (GuestAddress(0x200), 0x0C)],
            1,
            GuestAddress(0x200),
        );

        mem.write_slice(&[0; 20], GuestAddress(0x100)).unwrap();

        // VIRTIO_BLK_ID_BYTES bytes should've been written in memory.
        assert_eq!(
            req_exec.execute(&mem, &get_id_req).unwrap(),
            VIRTIO_BLK_ID_BYTES as u32
        );
        let mut buf = [0x00; 8];
        mem.read_slice(&mut buf, GuestAddress(0x100)).unwrap();
        assert_eq!(buf, dev_id[0..8]);
        let mut buf = [0x00; 12];
        mem.read_slice(&mut buf, GuestAddress(0x200)).unwrap();
        assert_eq!(buf, dev_id[8..VIRTIO_BLK_ID_BYTES]);
    }

    #[test]
    fn test_process_request() {
        let f = TempFile::new().unwrap().into_file();
        f.set_len(0x1000).unwrap();

        let mem = GuestMemoryMmap::from_ranges(&[(GuestAddress(0), 0x1000_0000)]).unwrap();
        let flush_req = Request::new(
            RequestType::Flush,
            vec![(GuestAddress(0x100), 0x400)],
            0,
            GuestAddress(0x600),
        );

        // VIRTIO_BLK_F_FLUSH not negotiated.
        let mut req_exec = StdIoBackend::new(f, 0).unwrap();
        assert_eq!(req_exec.process_request(&mem, &flush_req).unwrap(), 1);
        assert_eq!(
            mem.read_obj::<u8>(GuestAddress(0x600)).unwrap(),
            VIRTIO_BLK_S_UNSUPP
        );

        // VIRTIO_BLK_F_FLUSH negotiated.
        req_exec.features = 1 << VIRTIO_BLK_F_FLUSH;
        assert_eq!(req_exec.process_request(&mem, &flush_req).unwrap(), 1);
        assert_eq!(
            mem.read_obj::<u8>(GuestAddress(0x600)).unwrap(),
            VIRTIO_BLK_S_OK
        );

        // Ok In request.
        let in_req = Request::new(
            RequestType::In,
            vec![(GuestAddress(0x100), 0x400), (GuestAddress(0x600), 0x200)],
            0,
            GuestAddress(0x900),
        );
        // 0x600 bytes should've been written in memory.
        assert_eq!(req_exec.process_request(&mem, &in_req).unwrap(), 0x601);
        assert_eq!(
            mem.read_obj::<u8>(GuestAddress(0x900)).unwrap(),
            VIRTIO_BLK_S_OK
        );

        // Invalid status address.
        let in_req = Request::new(
            RequestType::In,
            vec![(GuestAddress(0x100), 0x400), (GuestAddress(0x600), 0x200)],
            0,
            GuestAddress(0x1000_0001),
        );
        assert!(matches!(
            req_exec.process_request(&mem, &in_req).unwrap_err(),
            ProcessReqError::GuestMemory(InvalidGuestAddress(GuestAddress(0x1000_0001)))
        ));

        req_exec.features = 1 << VIRTIO_BLK_F_DISCARD;
        // Test discard request with invalid flags.
        let discard_req = DiscardWriteZeroes {
            sector: 3,
            num_sectors: 2,
            flags: 0x0001,
        };
        mem.write_obj::<DiscardWriteZeroes>(discard_req, GuestAddress(0x1000))
            .unwrap();
        let discard_req = Request::new(
            RequestType::Discard,
            vec![(
                GuestAddress(0x1000),
                mem::size_of::<DiscardWriteZeroes>() as u32,
            )],
            7,
            GuestAddress(0x2000),
        );
        assert_eq!(req_exec.process_request(&mem, &discard_req).unwrap(), 1);
        assert_eq!(
            mem.read_obj::<u8>(GuestAddress(0x2000)).unwrap(),
            VIRTIO_BLK_S_UNSUPP
        );

        // Invalid memory address for write operation.
        let out_req = Request::new(
            RequestType::Out,
            vec![(GuestAddress(0xFFF_FFF0), 0x200)],
            7,
            GuestAddress(0x200),
        );
        assert_eq!(req_exec.process_request(&mem, &out_req).unwrap(), 1);
        assert_eq!(
            mem.read_obj::<u8>(GuestAddress(0x200)).unwrap(),
            VIRTIO_BLK_S_IOERR
        );

        // Invalid memory address for read operation.
        let in_req = Request::new(
            RequestType::In,
            vec![(GuestAddress(0xFFF_FFF0), 0x200)],
            7,
            GuestAddress(0x200),
        );
        assert_eq!(
            req_exec.process_request(&mem, &in_req).unwrap(),
            0x1000_0000 - 0xFFF_FFF0 + 1
        );
        assert_eq!(
            mem.read_obj::<u8>(GuestAddress(0x200)).unwrap(),
            VIRTIO_BLK_S_IOERR
        );

        let dev_id = [
            0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x00A, 0x0B, 0x0C, 0x0D, 0x0E,
            0x0F, 0x10, 0x11, 0x12, 0x13, 0x14,
        ];
        req_exec = req_exec.with_device_id(dev_id);

        // Invalid memory address for get device id operation.
        let get_id_req = Request::new(
            RequestType::GetDeviceID,
            vec![(GuestAddress(0xFFF_FFFA), VIRTIO_BLK_ID_BYTES as u32)],
            7,
            GuestAddress(0x200),
        );
        assert_eq!(
            req_exec.process_request(&mem, &get_id_req).unwrap(),
            0x1000_0000 - 0xFFF_FFFA + 1
        );
        assert_eq!(
            mem.read_obj::<u8>(GuestAddress(0x200)).unwrap(),
            VIRTIO_BLK_S_IOERR
        );
    }
}
