# Contributing to virtio-bindings

## Overview

virtio-bindings is periodically updated with imported virtio headers from the
Linux kernel. The Linux header files have kernel header dependencies that are
removed during import so that bindgen can process them in isolation without a
full set of kernel headers. This is also necessary because the licenses of
individual kernel header files varies and we only want to distribute
BSD-licensed virtio headers.

## Importing kernel headers
Generating bindings depends on the Linux kernel, so you need to have the
repository on your machine:

```bash
git clone https://github.com/torvalds/linux.git
```

Install the headers so they can be used for import:
```bash
cd linux
git checkout <linux-version>
make headers_install INSTALL_HDR_PATH=headers-<linux-version>
```

Import kernel headers into `include/`:
```bash
cd ~/vm-virtio/virtio-bindings
./import-linux-headers.sh path/to/headers-<linux-version>
```

Test that the build still works:
```bash
cargo build
```

## Adding bindings for new header files
New kernel headers can be added as follows:
1. Add the new file to import-linux-headers.sh so it is imported from the Linux
   kernel header directory into include/.
2. Add the new file to build.rs so bindgen generates bindings.
3. Add the new module to src/lib.rs so the generated bindings are exposed in
   the crate.
4. Check if `cargo build` still succeeds. If the header has new kernel header
   dependencies then you need to add them (if they are BSD licensed) or stub
   them out (if they are not BSD licensed).
