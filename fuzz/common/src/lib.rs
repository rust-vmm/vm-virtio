use ::virtio_queue::{Descriptor, Queue, QueueT};
use std::sync::atomic::Ordering;
use vm_memory::GuestMemoryMmap;

use serde::{Deserialize, Serialize};

pub mod virtio_queue;
pub mod virtio_queue_ser;
pub mod vsock;

/// Similar to a Descriptor structure, the only difference is that instead of having fields of types
/// Le64, Le32, Le16 (the way the Descriptor structure has) it has fields of types u64, u32, u16.
/// This is needed because the Arbitrary trait is already implemented for base types like the ones
/// used in FuzzingDescriptor, but not for Le64, Le32, Le16.
#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq)]
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
#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq)]
pub enum LoadOrdering {
    Relaxed,
    Acquire,
    SeqCst,
}

/// The QueueState functions
#[derive(Serialize, Deserialize, Debug, PartialEq)]
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
    AvailRing,
    UsedRing,
    EventIdxEnabled,
    PopDescriptorChain,
}

impl VirtioQueueFunction {
    pub fn call(&self, q: &mut Queue, m: &GuestMemoryMmap) {
        use VirtioQueueFunction::*;
        match self {
            IsValid => {
                q.is_valid(m);
            }
            Reset => {
                q.reset();
            }
            MaxSize => {
                q.max_size();
            }
            Size => {
                q.size();
            }
            SetSize { size } => {
                q.set_size(*size);
            }
            Ready => {
                q.ready();
            }
            SetReady { ready } => {
                q.set_ready(*ready);
            }
            SetDescTableAddress { low, high } => {
                q.set_desc_table_address(*low, *high);
            }
            SetAvailRingAddress { low, high } => {
                q.set_avail_ring_address(*low, *high);
            }
            SetUsedRingAddress { low, high } => {
                q.set_used_ring_address(*low, *high);
            }
            SetEventIdx { enabled } => {
                q.set_event_idx(*enabled);
            }
            AvailIdx { order } => {
                let _ = q.avail_idx(m, (*order).into());
            }
            UsedIdx { order } => {
                let _ = q.used_idx(m, (*order).into());
            }
            AddUsed { head_index, len } => {
                let _ = q.add_used(m, *head_index, *len);
            }
            EnableNotification => {
                let _ = q.enable_notification(m);
            }
            DisableNotification => {
                let _ = q.disable_notification(m);
            }
            NeedsNotification => {
                let _ = q.needs_notification(m);
            }
            NextAvail => {
                q.next_avail();
            }
            SetNextAvail { next_avail } => {
                q.set_next_avail(*next_avail);
            }
            NextUsed => {
                q.next_used();
            }
            SetNextUsed { next_used } => {
                q.set_next_used(*next_used);
            }
            AvailRing => {
                q.avail_ring();
            }
            UsedRing => {
                q.used_ring();
            }
            EventIdxEnabled => {
                q.event_idx_enabled();
            }
            PopDescriptorChain => {
                q.pop_descriptor_chain(m);
            }
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
