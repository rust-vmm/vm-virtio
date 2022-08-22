use crate::{FuzzingDescriptor, VirtioQueueFunction};
use serde::{Deserialize, Serialize};

/// Default size of the queue.
/// This number does not bear any particular meaning, but it is what we've been using
/// in Virtio Device implementations in the VMM. This number MUST be a power of 2 to be valid.
pub const DEFAULT_QUEUE_SIZE: u16 = 256;

/// Input generated by the fuzzer for fuzzing virtio_queue
#[derive(Serialize, Deserialize, Debug, PartialEq)]
pub struct VirtioQueueInput {
    pub descriptors: Vec<FuzzingDescriptor>,
    pub functions: Vec<VirtioQueueFunction>,
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use std::io::Write;

    use crate::create_corpus_file;
    use virtio_bindings::bindings::virtio_ring::{VRING_DESC_F_NEXT, VRING_DESC_F_WRITE};
    use virtio_queue::{mock::MockSplitQueue, Descriptor, Queue, QueueT};
    use vm_memory::{GuestAddress, GuestMemoryMmap};

    pub fn create_basic_virtio_queue_ops() -> VirtioQueueInput {
        // We are actually calling the functions that we want the fuzzer to call to validate
        // the test case. To easily track the functions and their order, we just add them to
        // the list as they're being called instead of adding them all at once.
        let mut functions = Vec::new();

        // The chains are (0, 1), (2, 3, 4), (5, 6), (7, 8), (9, 10, 11, 12).
        let mut descriptors = Vec::new();
        let desc_len: u32 = 0x1000;
        for i in 0u16..7 {
            let flags = match i {
                1 | 6 => 0,
                2 | 5 => VRING_DESC_F_NEXT | VRING_DESC_F_WRITE,
                4 => VRING_DESC_F_WRITE,
                _ => VRING_DESC_F_NEXT,
            } as u16;

            descriptors.push(FuzzingDescriptor {
                addr: (desc_len * (i + 1) as u32) as u64,
                len: desc_len as u32,
                flags,
                next: i + 1,
            });
        }

        // To be able to call the functions we actually need to create the environment for running.
        let mem = GuestMemoryMmap::<()>::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap();
        let vq = MockSplitQueue::new(&mem, DEFAULT_QUEUE_SIZE);
        let q_descriptors: Vec<Descriptor> =
            descriptors.iter().map(|desc| (*desc).into()).collect();
        vq.build_multiple_desc_chains(&q_descriptors).unwrap();
        let mut q: Queue = vq.create_queue().unwrap();

        // Call functions on the Queue and add them to the function list.
        q.set_ready(true);
        functions.push(VirtioQueueFunction::SetReady { ready: true });

        q.disable_notification(&mem).unwrap();
        functions.push(VirtioQueueFunction::DisableNotification);

        // Setting an invalid size (i.e. a number that's not a power of 2) is not influencing the
        // operation of the queue.
        q.set_size(15);
        functions.push(VirtioQueueFunction::SetSize { size: 15 });
        assert_eq!(q.size(), DEFAULT_QUEUE_SIZE);
        functions.push(VirtioQueueFunction::Size);

        // Consume the (0, 1) chain.
        let head_index = 0;
        let len = desc_len * 2; // there are 2 descriptors in this chain
        q.add_used(&mem, head_index, len).unwrap();
        functions.push(VirtioQueueFunction::AddUsed { head_index, len });

        q.enable_notification(&mem).unwrap();
        functions.push(VirtioQueueFunction::EnableNotification);

        // Consume the (2, 3, 4) chain as well which is the second chain.
        let head_index = 2;
        let len = desc_len * 3; // there are 3 descriptors in this chain
        q.add_used(&mem, head_index, len).unwrap();
        functions.push(VirtioQueueFunction::AddUsed { head_index, len });

        // There are still unused descriptor chains, so retrieving one should be ok.
        q.pop_descriptor_chain(&mem).unwrap();
        functions.push(VirtioQueueFunction::PopDescriptorChain);

        // Now that we ran the functions and validated that they work as expected, we can create the
        // test case that we can later write to the file.
        VirtioQueueInput {
            descriptors,
            functions,
        }
    }

    #[test]
    // Running this test will write to the fuzz input directory the
    // `basic_virtio_queue` file which contains the virtio queue descriptors
    // and operations on the queues as exemplified in the following test.
    fn write_basic_virtio_queue_ops() {
        let (mut out_file, path) = create_corpus_file("virtio_queue", "basic_virtio_queue");

        let virtq_fuzz_input = create_basic_virtio_queue_ops();
        out_file
            .write_all(bincode::serialize(&virtq_fuzz_input).unwrap().as_slice())
            .unwrap();

        // Let's validate that we have in the file what we actually wrote.
        let written_input =
            bincode::deserialize::<VirtioQueueInput>(&std::fs::read(path).unwrap()).unwrap();
        assert_eq!(virtq_fuzz_input, written_input);
    }
}
