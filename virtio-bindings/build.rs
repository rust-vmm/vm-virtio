// Copyright Red Hat, Inc.
// SPDX-License-Identifier: (BSD-3-Clause OR Apache-2.0)

use std::env;
use std::path::PathBuf;

fn generate_bindings(header: &str) {
    let bindings = bindgen::Builder::default()
        .header(format!("include/linux/{header}.h"))
        .allowlist_file(format!("include/linux/{header}.h"))
        .derive_default(true)
        .derive_partialeq(true)
        .clang_arg("-Iinclude")
        .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
        .generate()
        .unwrap_or_else(|_| panic!("Unable to generate bindings for {header}"));

    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    bindings
        .write_to_file(out_path.join(format!("{header}.rs")))
        .unwrap_or_else(|_| panic!("Couldn't write bindings for {header}"));
}

fn main() {
    // If you change this list, remember to update src/lib.rs
    for header in [
        "virtio_blk",
        "virtio_config",
        "virtio_gpu",
        "virtio_ids",
        "virtio_input",
        "virtio_mmio",
        "virtio_net",
        "virtio_ring",
        "virtio_scsi",
    ] {
        generate_bindings(header);
    }
}
