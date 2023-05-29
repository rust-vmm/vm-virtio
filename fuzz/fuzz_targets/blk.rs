#![no_main]

use common::blk::BlkInput;
use common::virtio_queue::DEFAULT_QUEUE_SIZE;
use libfuzzer_sys::fuzz_target;
use std::hint::black_box;
use virtio_blk::request::Request;
use virtio_blk::stdio_executor::StdIoBackend;
use virtio_queue::{mock::MockSplitQueue, Descriptor};
use vm_memory::{Bytes, GuestAddress, GuestMemoryMmap};

fuzz_target!(|data: &[u8]| {
    let Ok(fuzz_input) = bincode::deserialize::<BlkInput>(data) else {
        return;
    };

    let start_addr = GuestAddress(0x1000);
    // Create and randomly populate the guest memory
    let m = GuestMemoryMmap::<()>::from_ranges(&[(start_addr, 0x11000)]).unwrap();
    for (addr, mem) in fuzz_input.guestmem.iter() {
        let _ = m.write_slice(mem, GuestAddress(*addr));
    }

    let vq = MockSplitQueue::create(&m, start_addr, DEFAULT_QUEUE_SIZE);

    let descriptors: Vec<Descriptor> = fuzz_input
        .descriptors
        .iter()
        .map(|desc| (*desc).into())
        .collect();

    // A backing in-memory file
    let memfile = memfd::MemfdOptions::default()
        .create("fuzzfile")
        .unwrap()
        .into_file();

    // A backend that can execute a virtio-blk request
    let mut backend = StdIoBackend::new(memfile, fuzz_input.features).unwrap();
    if let Some(id) = fuzz_input.device_id {
        backend = backend.with_device_id(id);
    }

    // Build a descriptor chain, parse and execute a request
    if let Ok(mut chain) = vq.build_desc_chain(&descriptors) {
        if let Ok(req) = Request::parse(&mut chain) {
            // Ensure the compiler does not optimize the request away
            let _ = black_box(backend.process_request(&m, &req));
        };
    }
});
