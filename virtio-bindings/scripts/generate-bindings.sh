# Copyright 2025 Alyssa Ross <hi@alyssa.is>
# SPDX-License-Identifier: BSD-3-Clause OR Apache-2.0

headers="$(mktemp -d --suffix .generate-bindings)"
trap 'rm -rf -- "$headers"' EXIT

make -C "$1" INSTALL_HDR_PATH="$headers" headers_install

while read -r rust_arch clang_target; do
    mkdir -p "src/bindings/$rust_arch"

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
            ; do \
	bindgen "$headers/include/linux/$header.h" \
	    -o "src/bindings/$rust_arch/$header.rs" \
	    --allowlist-file "$headers/include/linux/$header.h" \
	    --with-derive-default \
	    --with-derive-partialeq \
	    -- \
	    --target="$clang_target" \
	    -I"$headers/include"
    done
done <<EOF
arm arm-linux-gnueabi
aarch64 aarch64-linux-gnu
hexagon hexagon-linux-musl
loongarch64 loongarch64-linux-gnusf
m68k m68k-linux-gnu
mips mips-linux-gnu
mips32r6 mipsisa32r6-linux-gnu
mips64 mips64-linux-gnu
mips64r6 mipsisa64r6-linux-gnu
powerpc64 powerpc64-linux-gnu
powerpc64le powerpc64le-linux-gnu
riscv32 riscv32-linux-gnu
riscv64 riscv64-linux-gnu
s390x s390x-linux-gnu
sparc sparc-linux-gnu
sparc64 sparc64-linux-gnu
x86_64 x86_64-linux-gnu
x86 i686-linux-gnu
EOF
