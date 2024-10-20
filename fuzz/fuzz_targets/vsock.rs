#![no_main]
use common::virtio_queue::DEFAULT_QUEUE_SIZE;
use common::vsock::{InitFunction, VsockInput};
use libfuzzer_sys::fuzz_target;
use virtio_queue::{desc::RawDescriptor, mock::MockSplitQueue};
use virtio_vsock::packet::VsockPacket;
use vm_memory::{GuestAddress, GuestMemoryMmap};

fuzz_target!(|data: &[u8]| {
    let fuzz_input = match bincode::deserialize::<VsockInput>(data) {
        Ok(input) => input,
        Err(_) => return,
    };

    // We are not starting from GuestAddress(0x0) because that's the address that is set
    // for the descriptor table when doing a reset. Setting this to 0 would make us process the
    // same descriptors multiple times.
    let start_addr = GuestAddress(0x1000);
    let m = GuestMemoryMmap::<()>::from_ranges(&[(GuestAddress(0x1000), 0x11000)]).unwrap();
    let vq = MockSplitQueue::create(&m, start_addr, DEFAULT_QUEUE_SIZE);

    let descriptors: Vec<RawDescriptor> = fuzz_input
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
