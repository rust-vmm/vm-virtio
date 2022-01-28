// Copyright 2022 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

//! Adds serialization capabilities to the state objects from `virtio-queue`.
//!
//! Provides wrappers over the state objects from `virtio-queue` crate that
//! implement the `Serialize`, `Deserialize` and `Versionize` traits.

#![deny(missing_docs)]

mod state;

pub use state::QueueStateSer;
