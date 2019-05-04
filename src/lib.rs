// Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Portions Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the THIRD-PARTY file.
#![deny(missing_docs)]

//! Implements virtio devices, queues, and transport mechanisms.
#[macro_use]
extern crate log;
extern crate vm_memory;

mod queue;

pub use self::queue::*;
