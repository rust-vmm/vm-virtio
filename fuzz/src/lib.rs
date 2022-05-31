use std::convert::Into;
use virtio_queue::Descriptor;
use libfuzzer_sys::arbitrary::Arbitrary;

/// Similar to a Descriptor structure, the only difference is that instead of having fields of types
/// Le64, Le32, Le16 (the way the Descriptor structure has) it has fields of types u64, u32, u16.
/// This is needed because the Arbitrary trait is already implemented for base types like the ones
/// used in FuzzingDescriptor, but not for Le64, Le32, Le16.
#[derive(Arbitrary, Debug, Copy, Clone)]
pub struct FuzzingDescriptor {
    /// Guest physical address of device specific data.
    pub addr: u64,

    /// Length of device specific data.
    pub len: u32,

    /// Includes next, write, and indirect bits.
    pub flags: u16,

    /// Index into the descriptor table of the next descriptor if flags has the `next` bit set.
    pub next: u16,
}

/// The virtio queue functions that are called from the driver side
#[derive(Arbitrary, Debug)]
pub enum VirtioQueueFunctionType {
    MaxSize,
    SetSize { size: u16 },
    Ready,
    SetReady { ready: bool },
    SetDescTableAddress { low: Option<u32>, high: Option<u32> },
    SetAvailRingAddress { low: Option<u32>, high: Option<u32> },
    SetUsedRingAddress { low: Option<u32>, high: Option<u32> },
    SetEventIdx { enabled: bool },
}

#[derive(Arbitrary, Debug)]
pub struct VirtioQueueInput {
    pub fuzzing_descriptors: Vec<FuzzingDescriptor>,
    pub functions: Vec<VirtioQueueFunctionType>,
}

impl Into<Descriptor> for FuzzingDescriptor {
    fn into(self) -> Descriptor {
        Descriptor::new(self.addr, self.len, self.flags, self.next)
    }
}
