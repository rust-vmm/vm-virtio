#![no_main]
use common::virtio_queue::DEFAULT_QUEUE_SIZE;
use common::vsock::{InitFunction, VsockInput};
use libfuzzer_sys::fuzz_target;
use virtio_queue::{mock::MockSplitQueue, Descriptor};
use virtio_vsock::packet::VsockPacket;
use vm_memory::{GuestAddress, GuestMemoryMmap};

fuzz_target!(|data: &[u8]| {
    let fuzz_input = match bincode::deserialize::<VsockInput>(data) {
        Ok(input) => input,
        Err(_) => return,
    };

    let m = GuestMemoryMmap::<()>::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap();
    let vq = MockSplitQueue::new(&m, DEFAULT_QUEUE_SIZE);

    let descriptors: Vec<Descriptor> = fuzz_input
        .descriptors
        .iter()
        .map(|desc| (*desc).into())
        .collect();

    if let Ok(mut chain) = vq.build_desc_chain(&descriptors) {
        let packet = match fuzz_input.init_function {
            InitFunction::FromRX => {
                VsockPacket::from_rx_virtq_chain(&m, &mut chain, fuzz_input.pkt_max_data)
            }
            InitFunction::FromTX => {
                VsockPacket::from_tx_virtq_chain(&m, &mut chain, fuzz_input.pkt_max_data)
            }
        };
        if let Ok(mut p) = packet {
            fuzz_input
                .functions
                .iter()
                .for_each(|f| f.call(&mut p, &mut m.clone()));
        }
    }
});
