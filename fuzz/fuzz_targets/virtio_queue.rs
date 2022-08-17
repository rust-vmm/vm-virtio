#![no_main]
use common::virtio_queue::{VirtioQueueInput, DEFAULT_QUEUE_SIZE};
use libfuzzer_sys::fuzz_target;
use virtio_queue::{mock::MockSplitQueue, Descriptor};
use vm_memory::{GuestAddress, GuestMemoryMmap};

fuzz_target!(|data: &[u8]| {
    let fuzz_input = match bincode::deserialize::<VirtioQueueInput>(data) {
        Ok(input) => input,
        Err(_) => return,
    };

    let m = &GuestMemoryMmap::<()>::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap();
    let vq = MockSplitQueue::new(m, DEFAULT_QUEUE_SIZE);
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

    if let Ok(mut q) = vq.create_queue() {
        fuzz_input.functions.iter().for_each(|f| f.call(&mut q, m));
    }
});
