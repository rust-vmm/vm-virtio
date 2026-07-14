#![no_main]
use common::virtio_queue::DEFAULT_QUEUE_SIZE;
use common::vsock_rw::{InitFunction, VsockRwInput};
use libfuzzer_sys::fuzz_target;
use virtio_queue::{desc::RawDescriptor, mock::MockSplitQueue};
use virtio_vsock::packet_rw::{VsockPacketRx, VsockPacketTx};
use vm_memory::{GuestAddress, GuestMemoryMmap};

fuzz_target!(|data: &[u8]| {
    let fuzz_input = match bincode::deserialize::<VsockRwInput>(data) {
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

    if let Ok(chain) = vq.build_desc_chain(&descriptors) {
        match fuzz_input.init_function {
            InitFunction::FromTx => {
                if let Ok(mut packet) =
                    VsockPacketTx::from_tx_virtq_chain(&m, chain, fuzz_input.pkt_max_data)
                {
                    fuzz_input
                        .tx_functions
                        .iter()
                        .for_each(|f| f.call(&mut packet, &m));
                }
            }
            InitFunction::FromRx => {
                if let Ok(mut packet) =
                    VsockPacketRx::from_rx_virtq_chain(&m, chain, fuzz_input.pkt_max_data)
                {
                    fuzz_input
                        .rx_functions
                        .iter()
                        .for_each(|f| f.call(&mut packet));
                }
            }
        }
    }
});
