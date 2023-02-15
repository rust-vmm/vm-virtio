#![no_main]
use common::{virtio_queue::DEFAULT_QUEUE_SIZE, virtio_queue_ser::QueueStateInput};
use libfuzzer_sys::fuzz_target;
use std::convert::{Into, TryFrom};
use virtio_queue::{mock::MockSplitQueue, Descriptor, Queue, QueueState};
use vm_memory::{GuestAddress, GuestMemoryMmap};

fuzz_target!(|data: &[u8]| {
    let fuzz_input = match bincode::deserialize::<QueueStateInput>(data) {
        Ok(input) => input,
        Err(_) => return,
    };

    // We are not starting from GuestAddress(0x0) because that's the address that is set
    // for the descriptor table when doing a reset. Setting this to 0 would make us process the
    // same descriptors multiple times when pop_descriptor is called in a loop after a reset.
    // In the normal operation of a device we would not start from address 0 anyway.
    let start_addr = GuestAddress(0x1000);
    let m = &GuestMemoryMmap::<()>::from_ranges(&[(start_addr, 0x11000)]).unwrap();
    let vq = MockSplitQueue::create(m, start_addr, DEFAULT_QUEUE_SIZE);

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
