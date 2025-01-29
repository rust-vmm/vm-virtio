#!/bin/bash
# SPDX-License-Identifier: (BSD-3-Clause OR Apache-2.0)
# Copyright Red Hat, Inc.
#
# ./import-linux-headers.sh path/to/kernel/headers
#
# Import header files from a Linux kernel header tree. Be sure to run `cargo
# build` to test that bindgen succeeds before committing the updated headers.

src=$1
dst=include/linux

import_header() {
	# Use our local header files rather than system headers
	sed -e 's%#include <\([^>]*\)>%#include "\1"%' "$1" >"$2"
}

mkdir -p "$dst"

# If you change this list, remember to update build.rs
for header in \
	virtio_blk \
	virtio_config \
	virtio_gpu \
	virtio_ids \
	virtio_input \
	virtio_mmio \
	virtio_net \
	virtio_ring \
	virtio_scsi \
	virtio_types; do
	import_header "$src/include/linux/$header.h" "$dst/$header.h"
done
