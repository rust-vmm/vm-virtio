use std::convert::Into;
use std::sync::atomic::Ordering;
use virtio_queue::{Descriptor, QueueState, QueueStateT};
use vm_memory::GuestMemoryMmap;
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

// Identical to Ordering except it derives the Arbitrary trait
#[derive(Arbitrary, Debug, Copy, Clone)]
pub enum LoadOrdering {
    Relaxed,
    Acquire,
    SeqCst,
}

/// The QueueState functions
#[derive(Arbitrary, Debug)]
pub enum VirtioQueueFunction {
    IsValid,
    Reset,
    MaxSize,
    Size,
    SetSize { size: u16 },
    Ready,
    SetReady { ready: bool },
    SetDescTableAddress { low: Option<u32>, high: Option<u32> },
    SetAvailRingAddress { low: Option<u32>, high: Option<u32> },
    SetUsedRingAddress { low: Option<u32>, high: Option<u32> },
    SetEventIdx { enabled: bool },
    AvailIdx { order: LoadOrdering },
    UsedIdx { order: LoadOrdering },
    AddUsed { head_index: u16, len: u32 },
    EnableNotification,
    DisableNotification,
    NeedsNotification,
    NextAvail,
    SetNextAvail { next_avail: u16 },
    NextUsed,
    SetNextUsed { next_used: u16 },
    PopDescriptorChain,
}

impl VirtioQueueFunction {
    pub fn call(&self, q: &mut QueueState, m: &GuestMemoryMmap ) {
        match self {
            VirtioQueueFunction::IsValid => { q.is_valid(m); },
            VirtioQueueFunction::Reset => { q.reset(); },
            VirtioQueueFunction::MaxSize => { q.max_size(); },
            VirtioQueueFunction::Size => { q.size(); },
            VirtioQueueFunction::SetSize { size } => { q.set_size(*size); },
            VirtioQueueFunction::Ready => { q.ready(); },
            VirtioQueueFunction::SetReady { ready }=> { q.set_ready(*ready); },
            VirtioQueueFunction::SetDescTableAddress { low, high } => { q.set_desc_table_address(*low, *high); },
            VirtioQueueFunction::SetAvailRingAddress { low, high } => { q.set_avail_ring_address(*low, *high); },
            VirtioQueueFunction::SetUsedRingAddress { low, high } => { q.set_used_ring_address(*low, *high); },
            VirtioQueueFunction::SetEventIdx { enabled } => { q.set_event_idx(*enabled); },
            VirtioQueueFunction::AvailIdx { order } => { let _ = q.avail_idx(m, (*order).into()); },
            VirtioQueueFunction::UsedIdx { order } => { let _ = q.used_idx(m, (*order).into()); },
            VirtioQueueFunction::AddUsed { head_index, len } => { let _ = q.add_used(m, *head_index, *len); },
            VirtioQueueFunction::EnableNotification => { let _ = q.enable_notification(m); },
            VirtioQueueFunction::DisableNotification => { let _ = q.disable_notification(m); },
            VirtioQueueFunction::NeedsNotification => { let _ = q.needs_notification(m); },
            VirtioQueueFunction::NextAvail => { q.next_avail(); },
            VirtioQueueFunction::SetNextAvail { next_avail } => { q.set_next_avail(*next_avail); },
            VirtioQueueFunction::NextUsed => { q.next_used(); },
            VirtioQueueFunction::SetNextUsed { next_used } => { q.set_next_used(*next_used); },
            VirtioQueueFunction::PopDescriptorChain => { q.pop_descriptor_chain(m); },
        }
    }
}

impl Into<Ordering> for LoadOrdering {
    fn into(self) -> Ordering {
        match self {
            LoadOrdering::Relaxed => Ordering::Relaxed,
            LoadOrdering::Acquire => Ordering::Acquire,
            LoadOrdering::SeqCst => Ordering::SeqCst,
        }
    }
}

impl Into<Descriptor> for FuzzingDescriptor {
    fn into(self) -> Descriptor {
        Descriptor::new(self.addr, self.len, self.flags, self.next)
    }
}
