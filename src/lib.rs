// Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Portions Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the THIRD-PARTY file.
#![deny(missing_docs)]

//! Implements virtio devices, queues, and transport mechanisms.
extern crate epoll;
#[macro_use]
extern crate log;
extern crate vm_memory;
extern crate vmm_sys_util;

mod device;
mod queue;

pub use self::device::*;
pub use self::queue::*;

#[derive(Debug)]
/// Virtio device activation errors.
pub enum ActivateError {
    /// Virtio device epoll control interface error.
    EpollCtl(std::io::Error),

    /// Could not activate the virtio device.
    BadActivate,
}

/// Virtio device activation result type.
pub type ActivateResult = std::result::Result<(), ActivateError>;
