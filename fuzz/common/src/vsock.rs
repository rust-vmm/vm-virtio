use crate::FuzzingDescriptor;
use virtio_vsock::packet::VsockPacket;

use serde::{Deserialize, Serialize};
use vm_memory::{ByteValued, Bytes, GuestAddress, GuestMemoryMmap, Le16, Le32, Le64};

#[derive(Clone, Copy, Default, Debug, PartialEq)]
/// A copy of the virtio-vsock PacketHeader structure. All the fields are the same and must be
/// kept exactly the same because we are using this structure to write into Guest Memory
/// a Vsock Header that can be read during fuzzing. We cannot use the PacketHeader because
/// for security reasons the fields of the upstream structure are private.
pub struct FuzzingPacketHeader {
    pub src_cid: Le64,
    pub dst_cid: Le64,
    pub src_port: Le32,
    pub dst_port: Le32,
    pub len: Le32,
    pub type_: Le16,
    pub op: Le16,
    pub flags: Le32,
    pub buf_alloc: Le32,
    pub fwd_cnt: Le32,
}

// This is safe because `FuzzingPacketHeader` contains only wrappers over POD types and all
// accesses through safe `vm-memory` API will validate any garbage that could be included in there.
unsafe impl ByteValued for FuzzingPacketHeader {}

/// All the functions that can be called when fuzzing the VsockPacket.
#[derive(Serialize, Deserialize, Debug, PartialEq)]
pub enum VsockFunction {
    HeaderSlice,
    Len,
    DataSlice,
    SrcCid,
    SetSrcCid { cid: u64 },
    DstCid,
    SetDstCid { cid: u64 },
    SrcPort,
    SetSrcPort { port: u32 },
    DstPort,
    SetDstPort { port: u32 },
    IsEmpty,
    SetLen { len: u32 },
    Type_,
    SetType { type_: u16 },
    Op,
    SetOp { op: u16 },
    Flags,
    SetFlags { flags: u32 },
    SetFlag { flag: u32 },
    BufAlloc,
    SetBufAlloc { buf_alloc: u32 },
    FwdCnt,
    SetFwdCnt { fwd_cnt: u32 },
    SetHeaderFromRaw { bytes: Vec<u8> },
    // This function is not part of the VsockPacket interface but it is needed
    // to be able to read non-zero bytes from Guest Memory.
    // We're using this to generate custom input for the fuzzer by writing a
    // VsockPacket to Guest Memory that is later going to be read and altered
    // during fuzzing.
    _WriteToMem { addr: u64, bytes: Vec<u8> },
}

impl VsockFunction {
    pub fn call<B: vm_memory::bitmap::BitmapSlice>(
        &self,
        packet: &mut VsockPacket<B>,
        mem: &mut GuestMemoryMmap,
    ) {
        match self {
            VsockFunction::HeaderSlice => {
                packet.header_slice();
            }
            VsockFunction::Len => {
                packet.len();
            }
            VsockFunction::DataSlice => {
                packet.data_slice();
            }
            VsockFunction::SrcCid => {
                packet.src_cid();
            }
            VsockFunction::SetSrcCid { cid } => {
                packet.set_src_cid(*cid);
            }
            VsockFunction::DstCid => {
                packet.dst_cid();
            }
            VsockFunction::SetDstCid { cid } => {
                packet.set_dst_cid(*cid);
            }
            VsockFunction::SrcPort => {
                packet.src_port();
            }
            VsockFunction::SetSrcPort { port } => {
                packet.set_src_port(*port);
            }
            VsockFunction::DstPort => {
                packet.dst_port();
            }
            VsockFunction::SetDstPort { port } => {
                packet.set_dst_port(*port);
            }
            VsockFunction::IsEmpty => {
                packet.is_empty();
            }
            VsockFunction::SetLen { len } => {
                packet.set_len(*len);
            }
            VsockFunction::Type_ => {
                packet.type_();
            }
            VsockFunction::SetType { type_ } => {
                packet.set_type(*type_);
            }
            VsockFunction::Op => {
                packet.op();
            }
            VsockFunction::SetOp { op } => {
                packet.set_op(*op);
            }
            VsockFunction::Flags => {
                packet.flags();
            }
            VsockFunction::SetFlags { flags } => {
                packet.set_flags(*flags);
            }
            VsockFunction::SetFlag { flag } => {
                packet.set_flag(*flag);
            }
            VsockFunction::BufAlloc => {
                packet.buf_alloc();
            }
            VsockFunction::SetBufAlloc { buf_alloc } => {
                packet.set_buf_alloc(*buf_alloc);
            }
            VsockFunction::FwdCnt => {
                packet.fwd_cnt();
            }
            VsockFunction::SetFwdCnt { fwd_cnt } => {
                packet.set_fwd_cnt(*fwd_cnt);
            }
            VsockFunction::SetHeaderFromRaw { bytes } => {
                let _ = packet.set_header_from_raw(bytes.as_slice());
            }
            VsockFunction::_WriteToMem { bytes, addr } => {
                let _ = mem.write_slice(bytes.as_slice(), GuestAddress(*addr));
            }
        }
    }
}

// Whether we create a VsockPacket from_rx_virtq_chain or from_tx_virtq_chain
#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq)]
pub enum InitFunction {
    FromRX,
    FromTX,
}

/// Input generated by the fuzzer for fuzzing vsock_rx and vsock_tx
#[derive(Serialize, Deserialize, Debug, PartialEq)]
pub struct VsockInput {
    pub pkt_max_data: u32,
    pub init_function: InitFunction,
    pub descriptors: Vec<FuzzingDescriptor>,
    pub functions: Vec<VsockFunction>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::create_corpus_file;
    use crate::virtio_queue::DEFAULT_QUEUE_SIZE;
    use std::io::Write;
    use virtio_bindings::bindings::virtio_ring::{VRING_DESC_F_NEXT, VRING_DESC_F_WRITE};
    use virtio_queue::desc::RawDescriptor;
    use virtio_queue::mock::MockSplitQueue;
    use virtio_vsock::packet::VsockPacket;
    use vm_memory::{Bytes, GuestAddress, GuestMemory, GuestMemoryMmap};

    // Random values to be used by the tests for the header fields.
    const SRC_CID: u64 = 1;
    const DST_CID: u64 = 2;
    const SRC_PORT: u32 = 3;
    const DST_PORT: u32 = 4;
    const LEN: u32 = 16;
    const TYPE: u16 = 5;
    const OP: u16 = 6;
    const FLAGS: u32 = 7;
    const FLAG: u32 = 8;
    const BUF_ALLOC: u32 = 256;
    const FWD_CNT: u32 = 9;

    const MAX_PKT_BUF_SIZE: u32 = 64 * 1024;

    const DESC_LEN: u32 = 0x100;

    const HEADER_WRITE_ADDR: u64 = 0x100;
    const DATA_WRITE_ADDR: u64 = 0x1000;

    /// For `get_mem_ptr()`: Whether we access the RX or TX ring.
    #[derive(Copy, Clone, Debug, Eq, PartialEq)]
    enum RxTx {
        /// Receive ring
        Rx,
        /// Transmission ring
        Tx,
    }

    /// Return a host pointer to the slice at `[addr, addr + length)`.  Use this only for
    /// comparison in `assert_eq!()`.
    fn get_mem_ptr<M: GuestMemory>(
        mem: &M,
        addr: GuestAddress,
        length: usize,
        _rx_tx: RxTx,
    ) -> *const u8 {
        assert!(length > 0);
        let slice = mem
            .get_slices(addr, length)
            .next()
            .unwrap()
            .unwrap();
        assert_eq!(slice.len(), length, "Fragmented guest memory area");
        slice.ptr_guard().as_ptr()
    }

    // We are generating the same operations for packets created from either RX or TX.
    // Because we need as a first function the write to memory, we are passing the functions as
    // both an input & output parameter even though this is typically an anti-pattern.
    fn create_basic_vsock_packet_ops<B: vm_memory::bitmap::BitmapSlice>(
        packet: &mut VsockPacket<B>,
        mem: &GuestMemoryMmap,
        functions: &mut Vec<VsockFunction>,
        rx_tx: RxTx,
    ) {
        // We are actually calling the functions that we want the fuzzer to call to validate
        // the test case. To easily track the functions and their order, we just add them to
        // the list as they're being called instead of adding them all at once.
        let header_slice = packet.header_slice();
        functions.push(VsockFunction::HeaderSlice);
        assert_eq!(
            header_slice.ptr_guard().as_ptr(),
            get_mem_ptr(
                mem,
                GuestAddress(HEADER_WRITE_ADDR),
                header_slice.len(),
                rx_tx
            )
        );

        let data_slice = packet.data_slice().unwrap();
        functions.push(VsockFunction::DataSlice);
        assert_eq!(
            data_slice.ptr_guard().as_ptr(),
            get_mem_ptr(mem, GuestAddress(DATA_WRITE_ADDR), data_slice.len(), rx_tx)
        );

        packet.set_src_cid(SRC_CID);
        functions.push(VsockFunction::SetSrcCid { cid: SRC_CID });
        assert_eq!(packet.src_cid(), SRC_CID);
        functions.push(VsockFunction::SrcCid);

        packet.set_dst_cid(DST_CID);
        functions.push(VsockFunction::SetDstCid { cid: DST_CID });
        assert_eq!(packet.src_cid(), SRC_CID);
        functions.push(VsockFunction::DstCid);

        packet.set_src_port(SRC_PORT);
        functions.push(VsockFunction::SetSrcPort { port: SRC_PORT });
        assert_eq!(packet.src_port(), SRC_PORT);
        functions.push(VsockFunction::SrcPort);

        packet.set_dst_port(DST_PORT);
        functions.push(VsockFunction::SetDstPort { port: DST_PORT });
        assert_eq!(packet.dst_port(), DST_PORT);
        functions.push(VsockFunction::DstPort);

        packet.set_len(LEN);
        functions.push(VsockFunction::SetLen { len: LEN });
        assert_eq!(packet.len(), LEN);
        functions.push(VsockFunction::Len);

        packet.set_type(TYPE);
        functions.push(VsockFunction::SetType { type_: TYPE });
        assert_eq!(packet.type_(), TYPE);
        functions.push(VsockFunction::Type_);

        packet.set_op(OP);
        functions.push(VsockFunction::SetOp { op: OP });
        assert_eq!(packet.op(), OP);
        functions.push(VsockFunction::Op);

        packet.set_flags(FLAGS);
        functions.push(VsockFunction::SetFlags { flags: FLAGS });
        assert_eq!(packet.flags(), FLAGS);
        functions.push(VsockFunction::Flags);

        packet.set_flag(FLAG);
        functions.push(VsockFunction::SetFlag { flag: FLAG });

        packet.set_buf_alloc(BUF_ALLOC);
        functions.push(VsockFunction::SetBufAlloc {
            buf_alloc: BUF_ALLOC,
        });
        assert_eq!(packet.buf_alloc(), BUF_ALLOC);
        functions.push(VsockFunction::BufAlloc);

        packet.set_fwd_cnt(FWD_CNT);
        functions.push(VsockFunction::SetFwdCnt { fwd_cnt: FWD_CNT });
        assert_eq!(packet.fwd_cnt(), FWD_CNT);
        functions.push(VsockFunction::FwdCnt);
    }

    #[test]
    // Running this test will write to the fuzz input directory corresponding to the
    // vsock fuzz target the `tx_vsock_packet` file, containing the virtio queue descriptors,
    // the operations on the queues, and the other configurations for the Vsock Packet as
    // exemplified below.
    fn write_tx_vsock_packet_ops() {
        let (mut out_file, path) = create_corpus_file("vsock", "tx_vsock_packet");

        // To be able to call the functions we actually need to create the environment for running.
        let mem = GuestMemoryMmap::<()>::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap();
        let vq = MockSplitQueue::new(&mem, DEFAULT_QUEUE_SIZE);

        let mut functions = Vec::new();

        let header = FuzzingPacketHeader {
            src_cid: SRC_CID.into(),
            dst_cid: DST_CID.into(),
            src_port: SRC_PORT.into(),
            dst_port: DST_PORT.into(),
            len: LEN.into(),
            type_: TYPE.into(),
            op: OP.into(),
            flags: FLAGS.into(),
            buf_alloc: BUF_ALLOC.into(),
            fwd_cnt: FWD_CNT.into(),
        };
        let header_bytes = header.as_slice();

        mem.write_slice(header_bytes, GuestAddress(HEADER_WRITE_ADDR))
            .unwrap();
        // Write the PacketHeader to guest memory so that the read is successful, and we can
        // call operations on it.
        functions.push(VsockFunction::_WriteToMem {
            addr: HEADER_WRITE_ADDR,
            bytes: Vec::from(header_bytes),
        });

        let descriptors = vec![
            FuzzingDescriptor {
                addr: HEADER_WRITE_ADDR,
                len: DESC_LEN,
                flags: VRING_DESC_F_NEXT as u16,
                next: 1,
            },
            FuzzingDescriptor {
                addr: DATA_WRITE_ADDR,
                len: DESC_LEN,
                flags: 0,
                next: 0,
            },
        ];
        let q_descriptors: Vec<RawDescriptor> =
            descriptors.iter().map(|desc| (*desc).into()).collect();
        let mut chain = vq.build_multiple_desc_chains(&q_descriptors).unwrap();

        let mut packet =
            VsockPacket::from_tx_virtq_chain(&mem, &mut chain, MAX_PKT_BUF_SIZE).unwrap();
        create_basic_vsock_packet_ops(&mut packet, &mem, &mut functions, RxTx::Tx);
        let vsock_fuzz_input = VsockInput {
            functions,
            descriptors,
            init_function: InitFunction::FromTX,
            pkt_max_data: MAX_PKT_BUF_SIZE,
        };

        out_file
            .write_all(bincode::serialize(&vsock_fuzz_input).unwrap().as_slice())
            .unwrap();

        // Let's validate that we have in the file what we actually wrote.
        let written_input =
            bincode::deserialize::<VsockInput>(&std::fs::read(path).unwrap()).unwrap();
        assert_eq!(vsock_fuzz_input, written_input);
    }

    #[test]
    // Running this test will write to the fuzz input directory corresponding to the
    // vsock fuzz target the `rx_vsock_packet` file, containing the virtio queue descriptors,
    // the operations on the queues, and the other configurations for the Vsock Packet as
    // exemplified below.
    fn write_rx_vsock_packet_ops() {
        let (mut out_file, path) = create_corpus_file("vsock", "rx_vsock_packet");

        // To be able to call the functions we actually need to create the environment for running.
        let mem = GuestMemoryMmap::<()>::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap();
        let vq = MockSplitQueue::new(&mem, DEFAULT_QUEUE_SIZE);

        let descriptors = vec![
            FuzzingDescriptor {
                addr: HEADER_WRITE_ADDR,
                len: DESC_LEN,
                flags: (VRING_DESC_F_NEXT | VRING_DESC_F_WRITE) as u16,
                next: 1,
            },
            FuzzingDescriptor {
                addr: DATA_WRITE_ADDR,
                len: DESC_LEN,
                flags: VRING_DESC_F_WRITE as u16,
                next: 0,
            },
        ];
        let q_descriptors: Vec<RawDescriptor> =
            descriptors.iter().map(|desc| (*desc).into()).collect();
        let mut chain = vq.build_multiple_desc_chains(&q_descriptors).unwrap();

        let mut packet =
            VsockPacket::from_rx_virtq_chain(&mem, &mut chain, MAX_PKT_BUF_SIZE).unwrap();
        let mut functions = Vec::new();
        create_basic_vsock_packet_ops(&mut packet, &mem, &mut functions, RxTx::Rx);
        let vsock_fuzz_input = VsockInput {
            functions,
            descriptors,
            init_function: InitFunction::FromRX,
            pkt_max_data: MAX_PKT_BUF_SIZE,
        };

        out_file
            .write_all(bincode::serialize(&vsock_fuzz_input).unwrap().as_slice())
            .unwrap();

        // Let's validate that we have in the file what we actually wrote.
        let written_input =
            bincode::deserialize::<VsockInput>(&std::fs::read(path).unwrap()).unwrap();
        assert_eq!(vsock_fuzz_input, written_input);
    }
}
