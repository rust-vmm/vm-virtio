// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

/// Contains virtio block constant definitions.
pub mod defs;
/// Contains block request parsing abstraction.
pub mod request;
/// Contains a block request execution abstraction that is based on
/// [`std::io::Read`](https://doc.rust-lang.org/std/io/trait.Read.html)
/// and [`std::io::Write`](https://doc.rust-lang.org/std/io/trait.Write.html).
#[cfg(feature = "backend-stdio")]
pub mod stdio_executor;
