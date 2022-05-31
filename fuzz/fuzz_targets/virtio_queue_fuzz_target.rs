#![no_main]
use rust_vmm_fuzz::{VirtioQueueInput, VirtioQueueFunctionType};
use vm_memory::{GuestAddress, GuestMemoryMmap};
use virtio_queue::{mock::MockSplitQueue, Descriptor};
use libfuzzer_sys::fuzz_target;

fuzz_target!(|virtio_queue_input: VirtioQueueInput| {
    let m = &GuestMemoryMmap::<()>::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap();
    let fuzzing_descriptors = virtio_queue_input.fuzzing_descriptors;
    let vq = MockSplitQueue::new(m, fuzzing_descriptors.len() as u16);
    let mut descriptors: Vec<Descriptor> = Vec::with_capacity(fuzzing_descriptors.len());
    for fuzzing_descriptor in fuzzing_descriptors {
        descriptors.push(fuzzing_descriptor.into());
    }
    vq.build_multiple_desc_chains(&descriptors[..]);
    let mut q = vq.create_queue(m);

    for function in virtio_queue_input.functions {
        match function {
            VirtioQueueFunctionType::MaxSize => { q.max_size(); },
            VirtioQueueFunctionType::SetSize { size } => { q.set_size(size); },
            VirtioQueueFunctionType::Ready => { q.ready(); },
            VirtioQueueFunctionType::SetReady { ready } => { q.set_ready(ready); },
            VirtioQueueFunctionType::SetDescTableAddress { low, high } => { q.set_desc_table_address(low, high); },
            VirtioQueueFunctionType::SetAvailRingAddress { low, high } => { q.set_avail_ring_address(low, high); },
            VirtioQueueFunctionType::SetUsedRingAddress { low, high } => { q.set_used_ring_address(low, high); },
            VirtioQueueFunctionType::SetEventIdx { enabled } => { q.set_event_idx(enabled); },
        }
    }
});
