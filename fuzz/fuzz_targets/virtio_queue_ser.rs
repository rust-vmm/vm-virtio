#![no_main]
use common::virtio_queue_ser::QueueStateInput;
use libfuzzer_sys::fuzz_target;
use std::convert::{Into, TryFrom};
use virtio_queue::{mock::MockSplitQueue, Descriptor, Queue, QueueState};
use vm_memory::{GuestAddress, GuestMemoryMmap};

fuzz_target!(|data: &[u8]| {
    let fuzz_input = match bincode::deserialize::<QueueStateInput>(data) {
        Ok(input) => input,
        Err(_) => return,
    };

    let m = &GuestMemoryMmap::<()>::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap();
    let vq = MockSplitQueue::new(m, fuzz_input.descriptors.len() as u16);

    let descriptors: Vec<Descriptor> = fuzz_input
        .descriptors
        .iter()
        .map(|desc| (*desc).into())
        .collect();
    // we return early because the coverage is not increasing, we expect the fuzzer to abandon the
    // paths that would generate invalid descriptors
    if vq.build_multiple_desc_chains(&descriptors).is_err() {
        return;
    }
    let q_state: QueueState = fuzz_input.queue_state.into();

    if let Ok(mut q) = Queue::try_from(q_state) {
        fuzz_input.functions.iter().for_each(|f| f.call(&mut q, m));
    }
});
