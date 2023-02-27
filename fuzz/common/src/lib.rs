use ::virtio_queue::{Descriptor, Queue, QueueOwnedT, QueueT};
use std::fs::{self, File};
use std::path::{Path, PathBuf};
use std::sync::atomic::Ordering;
use vm_memory::GuestMemoryMmap;

use serde::{Deserialize, Serialize};

pub mod virtio_queue;
pub mod virtio_queue_ser;
pub mod vsock;

/// Similar to a Descriptor structure, the only difference is that instead of having fields of types
/// Le64, Le32, Le16 (the way the Descriptor structure has) it has fields of types u64, u32, u16.
/// This is needed because the constructor of the `Descriptor` uses the primitive types, and
/// serialize/deserialize is only implemented for primitive types and not for the corresponding
/// little endian types.
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

/// The `LoadOrdering` defines the valid ordering for the Load operation. This structures is needed
/// to avoid crashes when `load` is called with an invalid ordering, and because the
/// serialize/deserialize traits are not implemented for the `Ordering` enum.
#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq)]
pub enum LoadOrdering {
    Relaxed,
    Acquire,
    SeqCst,
}

/// The QueueState functions
#[derive(Clone, Serialize, Deserialize, Debug, PartialEq)]
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
    DescTable,
    NextUsed,
    SetNextUsed { next_used: u16 },
    AvailRing,
    UsedRing,
    EventIdxEnabled,
    PopDescriptorChain,
    _PopDescriptorChainLoop,
    Iter,
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
            DescTable => {
                q.desc_table();
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
            // This is not actually a function of the Queue interface. We are calling
            // the Queue function `pop_descriptor_chain` in a loop as this is the way
            // descriptors are typically processed.
            _PopDescriptorChainLoop => {
                while let Some(mut desc_chain) = q.pop_descriptor_chain(m) {
                    // this empty loop is here to check that there are no side effects
                    // in terms of memory & execution time.
                    while desc_chain.next().is_some() {}
                }
            }
            Iter => {
                let _ = q.iter(m).and_then(|mut i| {
                    // this empty loop is here to check that there are no side effects
                    // in terms of memory & execution time.
                    while i.next().is_some() {}
                    Ok(())
                });
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

/// For now this function makes sure that we don't introduce more than one loop to iterate over the
/// descriptors. This cannot happen as part of the normal operation of a device because we
/// consider the device implementation to be trusted. Bugs in the device implementations that
/// allow processing the same descriptor chain multiple times should be caught at the device level
/// as it is impossible here to differentiate between implementation problems and malicious
/// drivers.
pub fn sanitize_virtio_queue_functions(
    functions: &Vec<VirtioQueueFunction>,
) -> Vec<VirtioQueueFunction> {
    let mut has_desc_iter = false;
    functions
        .iter()
        .cloned()
        .filter(|func| {
            if *func == VirtioQueueFunction::_PopDescriptorChainLoop
                || *func == VirtioQueueFunction::Iter
            {
                if !has_desc_iter {
                    has_desc_iter = true;
                    true
                } else {
                    false
                }
            } else {
                true
            }
        })
        .collect::<Vec<VirtioQueueFunction>>()
}

/// Create a file in the dedicated corpus directory for the Fuzz Target specified in `target_name`.
///
/// This function is used in creating the custom input for the fuzz targets, and can panic when
/// creating the file fails.
///
/// Returns both the path and the file as the former is needed to be able to read the contents of
/// the file.
pub fn create_corpus_file(target_name: &str, filename: &str) -> (File, PathBuf) {
    // The CARGO_MANIFEST_DIR is the only sane way right now to get a path that can
    // be used for writing directly into the fuzz/input directory.
    // The env will output the absolute path of the `common` crate.
    let dest = format!("{}/../corpus/{}/", env!("CARGO_MANIFEST_DIR"), target_name);
    let corpus_path = Path::new(&dest);
    fs::create_dir_all(corpus_path).unwrap();

    let path = corpus_path.join(filename);
    (File::create(&path).unwrap(), path)
}
