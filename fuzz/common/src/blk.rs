use crate::FuzzingDescriptor;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
pub struct BlkInput {
    pub descriptors: Vec<FuzzingDescriptor>,
    pub guestmem: Vec<(u64, Vec<u8>)>,
    pub features: u64,
    pub device_id: Option<[u8; 20]>,
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::create_corpus_file;
    use crate::virtio_queue::DEFAULT_QUEUE_SIZE;
    use std::io::Write;
    use std::mem;
    use virtio_bindings::bindings::virtio_blk::VIRTIO_BLK_T_IN;
    use virtio_bindings::bindings::virtio_ring::{VRING_DESC_F_NEXT, VRING_DESC_F_WRITE};
    use virtio_blk::request::{Request, RequestType};
    use virtio_queue::{mock::MockSplitQueue, Descriptor};
    use vm_memory::{ByteValued, Bytes, GuestAddress, GuestMemoryMmap};

    // The same as the RequestHeader type in virtio_blk, with exposed fields
    #[derive(Clone, Copy, Debug, Default, PartialEq)]
    #[repr(C)]
    struct FuzzingBlkRequestHdr {
        request_type: u32,
        _reserved: u32,
        sector: u64,
    }

    unsafe impl ByteValued for FuzzingBlkRequestHdr {}

    // Test values for the descriptor chain
    const REQ_TYPE: u32 = VIRTIO_BLK_T_IN;
    const REQ_SECTOR: u64 = 1;
    const HEADER_ADDR: u64 = 0x100;
    const HEADER_LEN: u32 = mem::size_of::<FuzzingBlkRequestHdr>() as u32;
    const REQ_DATA_ADDRS: &[u64] = &[0x3000, 0x4000];
    const REQ_STATUS_ADDR: u64 = 0x5000;
    const DESC_LEN: usize = 0x1000;

    #[test]
    fn test_blk_basic_descriptor_chain() {
        let mem = GuestMemoryMmap::<()>::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap();
        let vq = MockSplitQueue::new(&mem, DEFAULT_QUEUE_SIZE);

        // Create header and write it to memory
        let header = FuzzingBlkRequestHdr {
            request_type: REQ_TYPE,
            _reserved: 0,
            sector: REQ_SECTOR,
        };
        mem.write_slice(header.as_slice(), GuestAddress(HEADER_ADDR))
            .unwrap();

        // Initialize data and status memory
        for data_addr in REQ_DATA_ADDRS.iter().copied() {
            mem.write_slice(&[0u8; DESC_LEN], GuestAddress(data_addr))
                .unwrap();
        }
        mem.write_slice(&[0u8; DESC_LEN], GuestAddress(REQ_STATUS_ADDR))
            .unwrap();

        let descriptors = [
            FuzzingDescriptor {
                addr: HEADER_ADDR,
                len: HEADER_LEN,
                flags: VRING_DESC_F_NEXT as u16,
                next: 1,
            },
            FuzzingDescriptor {
                addr: REQ_DATA_ADDRS[0],
                len: DESC_LEN as u32,
                flags: (VRING_DESC_F_NEXT | VRING_DESC_F_WRITE) as u16,
                next: 2,
            },
            FuzzingDescriptor {
                addr: REQ_DATA_ADDRS[1],
                len: DESC_LEN as u32,
                flags: (VRING_DESC_F_NEXT | VRING_DESC_F_WRITE) as u16,
                next: 3,
            },
            FuzzingDescriptor {
                addr: REQ_STATUS_ADDR,
                len: DESC_LEN as u32,
                flags: VRING_DESC_F_WRITE as u16,
                next: 0,
            },
        ];

        let q_descriptors: Vec<Descriptor> =
            descriptors.into_iter().map(|desc| desc.into()).collect();
        let mut chain = vq.build_multiple_desc_chains(&q_descriptors).unwrap();

        let req = Request::parse(&mut chain).unwrap();
        let data = req.data();
        assert_eq!(data.len(), 2);
        assert_eq!(
            data.get(0),
            Some(&(GuestAddress(REQ_DATA_ADDRS[0]), DESC_LEN as u32))
        );
        assert_eq!(
            data.get(1),
            Some(&(GuestAddress(REQ_DATA_ADDRS[1]), DESC_LEN as u32))
        );
        assert_eq!(req.sector(), REQ_SECTOR);
        assert_eq!(req.status_addr(), GuestAddress(REQ_STATUS_ADDR));
        assert_eq!(
            req.total_data_len(),
            (DESC_LEN * REQ_DATA_ADDRS.len()) as u64
        );
        assert_eq!(req.request_type(), RequestType::In);

        let fuzz_input = BlkInput {
            descriptors: descriptors.to_vec(),
            guestmem: Vec::new(),
            features: 0,
            device_id: Some([1; 20]),
        };

        let (mut out_file, path) = create_corpus_file("blk", "descriptor_chain");
        out_file
            .write_all(bincode::serialize(&fuzz_input).unwrap().as_slice())
            .unwrap();

        // Let's validate that we have in the file what we actually wrote.
        let written_input =
            bincode::deserialize::<BlkInput>(&std::fs::read(path).unwrap()).unwrap();
        assert_eq!(fuzz_input, written_input);
    }
}
