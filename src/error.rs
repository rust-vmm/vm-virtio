// Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Portions Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// Copyright © 2019 Intel Corporation
//
// Copyright (C) 2020 Alibaba Cloud. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0 AND BSD-3-Clause

use std::fmt::{self, Display};
use std::result;

use vm_memory::{GuestMemoryError, VolatileMemoryError};

/// Virtio Queue related errors.
#[derive(Debug)]
pub enum Error {
    /// Failed to access guest memory.
    GuestMemory(GuestMemoryError),
    /// Invalid indirect descriptor.
    InvalidIndirectDescriptor,
    /// Invalid indirect descriptor table.
    InvalidIndirectDescriptorTable,
    /// Invalid descriptor chain.
    InvalidChain,
    /// Invalid descriptor index.
    InvalidDescriptorIndex,
    /// Volatile memory related error.
    VolatileMemoryError(VolatileMemoryError),
    /// Descriptor chain overflow.
    DescriptorChainOverflow,
    /// Descriptor chain split is out of bounds.
    DescriptorChainSplitOOB(usize),
    /// Memory region error.
    FindMemoryRegion,
}

impl Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Error::*;

        match self {
            GuestMemory(_) => write!(f, "error accessing guest memory"),
            InvalidChain => write!(f, "invalid descriptor chain"),
            InvalidIndirectDescriptor => write!(f, "invalid indirect descriptor"),
            InvalidIndirectDescriptorTable => write!(f, "invalid indirect descriptor table"),
            InvalidDescriptorIndex => write!(f, "invalid descriptor index"),
            VolatileMemoryError(e) => write!(f, "volatile memory error: {}", e),
            DescriptorChainOverflow => write!(
                f,
                "the combined length of all the buffers in a `DescriptorChain` would overflow"
            ),
            DescriptorChainSplitOOB(off) => {
                write!(f, "`DescriptorChain` split is out of bounds: {}", off)
            }
            FindMemoryRegion => write!(f, "no memory region for this address range"),
        }
    }
}

impl std::error::Error for Error {}

/// Alias for a `Result` with the error type `vm_virtio::Error`.
pub type Result<T> = result::Result<T, Error>;
