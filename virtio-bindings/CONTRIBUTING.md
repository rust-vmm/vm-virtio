# Contributing to virtio-bindings

## Dependencies

### Bindgen
The bindings are currently generated using
[bindgen](https://rust-lang.github.io/rust-bindgen/) version 0.71.1:
```bash
cargo install bindgen-cli --vers 0.71.1
```

### Linux Kernel
Generating bindings depends on the Linux kernel, so you need to have the
repository on your machine:

```bash
git clone https://github.com/torvalds/linux.git
```

## Example for updating to a new kernel version

For this example we assume that you have both linux and virtio-bindings
repositories in your home directory.

```bash
cd ~/vm-virtio/virtio-bindings
scripts/generate-bindings.sh ~/linux
```
