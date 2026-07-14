use std::io::{Read, Write};

use serde::{Deserialize, Serialize};
use virtio_vsock::packet_rw::{VsockPacketRx, VsockPacketTx};
use virtio_vsock::PacketHeader;
use vm_memory::{Bytes, GuestAddress, GuestMemoryMmap};

use crate::FuzzingDescriptor;

/// All the functions that can be called when fuzzing a [`VsockPacketTx`].
#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
pub enum VsockTxFunction {
    SrcCid,
    DstCid,
    SrcPort,
    DstPort,
    Len,
    IsEmpty,
    Type_,
    Op,
    Flags,
    BufAlloc,
    FwdCnt,
    SetSrcCid {
        cid: u64,
    },
    SetDstCid {
        cid: u64,
    },
    SetSrcPort {
        port: u32,
    },
    SetDstPort {
        port: u32,
    },
    SetLen {
        len: u32,
    },
    SetType {
        type_: u16,
    },
    SetOp {
        op: u16,
    },
    SetFlags {
        flags: u32,
    },
    SetFlag {
        flag: u32,
    },
    SetBufAlloc {
        buf_alloc: u32,
    },
    SetFwdCnt {
        fwd_cnt: u32,
    },
    /// Read up to `len` bytes from the data Reader, if present.
    ReadData {
        len: u32,
    },
    // This function is not part of the VsockPacketTx interface but is needed to seed the
    // fuzzer with interesting header bytes at a known guest address, so mutations can
    // explore the effect of different header values on packet construction.
    _WriteToMem {
        addr: u64,
        bytes: Vec<u8>,
    },
}

impl VsockTxFunction {
    pub fn call<B: vm_memory::bitmap::BitmapSlice>(
        &self,
        packet: &mut VsockPacketTx<B>,
        mem: &GuestMemoryMmap,
    ) {
        match self {
            VsockTxFunction::SrcCid => {
                packet.header().src_cid();
            }
            VsockTxFunction::DstCid => {
                packet.header().dst_cid();
            }
            VsockTxFunction::SrcPort => {
                packet.header().src_port();
            }
            VsockTxFunction::DstPort => {
                packet.header().dst_port();
            }
            VsockTxFunction::Len => {
                packet.header().len();
            }
            VsockTxFunction::IsEmpty => {
                packet.header().is_empty();
            }
            VsockTxFunction::Type_ => {
                packet.header().type_();
            }
            VsockTxFunction::Op => {
                packet.header().op();
            }
            VsockTxFunction::Flags => {
                packet.header().flags();
            }
            VsockTxFunction::BufAlloc => {
                packet.header().buf_alloc();
            }
            VsockTxFunction::FwdCnt => {
                packet.header().fwd_cnt();
            }
            VsockTxFunction::SetSrcCid { cid } => {
                packet.header_mut().set_src_cid(*cid);
            }
            VsockTxFunction::SetDstCid { cid } => {
                packet.header_mut().set_dst_cid(*cid);
            }
            VsockTxFunction::SetSrcPort { port } => {
                packet.header_mut().set_src_port(*port);
            }
            VsockTxFunction::SetDstPort { port } => {
                packet.header_mut().set_dst_port(*port);
            }
            VsockTxFunction::SetLen { len } => {
                packet.header_mut().set_len(*len);
            }
            VsockTxFunction::SetType { type_ } => {
                packet.header_mut().set_type(*type_);
            }
            VsockTxFunction::SetOp { op } => {
                packet.header_mut().set_op(*op);
            }
            VsockTxFunction::SetFlags { flags } => {
                packet.header_mut().set_flags(*flags);
            }
            VsockTxFunction::SetFlag { flag } => {
                packet.header_mut().set_flag(*flag);
            }
            VsockTxFunction::SetBufAlloc { buf_alloc } => {
                packet.header_mut().set_buf_alloc(*buf_alloc);
            }
            VsockTxFunction::SetFwdCnt { fwd_cnt } => {
                packet.header_mut().set_fwd_cnt(*fwd_cnt);
            }
            VsockTxFunction::ReadData { len } => {
                if let Some(reader) = packet.data_slice_mut() {
                    let to_read = (*len as usize).min(reader.available_bytes());
                    let mut buf = vec![0u8; to_read];
                    let _ = reader.read(&mut buf);
                }
            }
            VsockTxFunction::_WriteToMem { addr, bytes } => {
                let _ = mem.write_slice(bytes.as_slice(), GuestAddress(*addr));
            }
        }
    }
}

/// All the functions that can be called when fuzzing a [`VsockPacketRx`].
#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
pub enum VsockRxFunction {
    /// Write a complete packet header via the header Writer.
    WriteHeader {
        src_cid: u64,
        dst_cid: u64,
        src_port: u32,
        dst_port: u32,
        len: u32,
        type_: u16,
        op: u16,
        flags: u32,
        buf_alloc: u32,
        fwd_cnt: u32,
    },
    /// Write arbitrary bytes via the data Writer.
    WriteData { bytes: Vec<u8> },
    /// Query how many bytes are available in the header Writer.
    HeaderAvailableBytes,
    /// Query how many bytes are available in the data Writer.
    DataAvailableBytes,
}

impl VsockRxFunction {
    pub fn call<B: vm_memory::bitmap::BitmapSlice>(&self, packet: &mut VsockPacketRx<B>) {
        match self {
            VsockRxFunction::WriteHeader {
                src_cid,
                dst_cid,
                src_port,
                dst_port,
                len,
                type_,
                op,
                flags,
                buf_alloc,
                fwd_cnt,
            } => {
                let mut header = PacketHeader::default();
                header
                    .set_src_cid(*src_cid)
                    .set_dst_cid(*dst_cid)
                    .set_src_port(*src_port)
                    .set_dst_port(*dst_port)
                    .set_len(*len)
                    .set_type(*type_)
                    .set_op(*op)
                    .set_flags(*flags)
                    .set_buf_alloc(*buf_alloc)
                    .set_fwd_cnt(*fwd_cnt);
                let _ = packet.header_slice().write_obj(header);
            }
            VsockRxFunction::WriteData { bytes } => {
                let _ = packet.data_slice().write(bytes.as_slice());
            }
            VsockRxFunction::HeaderAvailableBytes => {
                packet.header_slice().available_bytes();
            }
            VsockRxFunction::DataAvailableBytes => {
                packet.data_slice().available_bytes();
            }
        }
    }
}

/// Whether we create a packet from the TX or RX virtqueue.
#[derive(Serialize, Deserialize, Debug, Copy, Clone, PartialEq)]
pub enum InitFunction {
    FromTx,
    FromRx,
}

/// Input generated by the fuzzer for fuzzing [`VsockPacketTx`] and [`VsockPacketRx`].
#[derive(Serialize, Deserialize, Debug, PartialEq)]
pub struct VsockRwInput {
    pub pkt_max_data: u32,
    pub init_function: InitFunction,
    pub descriptors: Vec<FuzzingDescriptor>,
    pub tx_functions: Vec<VsockTxFunction>,
    pub rx_functions: Vec<VsockRxFunction>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::create_corpus_file;
    use crate::virtio_queue::DEFAULT_QUEUE_SIZE;
    use crate::vsock_common::test_utils::*;
    use std::io::Write;
    use virtio_bindings::bindings::virtio_ring::VRING_DESC_F_WRITE;
    use virtio_queue::desc::RawDescriptor;
    use virtio_queue::mock::MockSplitQueue;
    use virtio_vsock::packet_rw::{VsockPacketRx, VsockPacketTx};
    use vm_memory::{ByteValued, Bytes, GuestAddress, GuestMemoryMmap};

    #[test]
    // Running this test will write to the fuzz corpus directory for the vsock_rw fuzz target
    // a `tx_vsock_rw_packet` file containing a valid TX descriptor chain configuration,
    // the header bytes, and a sequence of TX operations to seed the fuzzer.
    fn write_tx_vsock_rw_packet_ops() {
        let (mut out_file, path) = create_corpus_file("vsock_rw", "tx_vsock_rw_packet");

        let mem = GuestMemoryMmap::<()>::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap();
        let vq = MockSplitQueue::new(&mem, DEFAULT_QUEUE_SIZE);

        // Build a PacketHeader with known values and write it to guest memory so the TX
        // chain constructor can parse it.
        let mut header = PacketHeader::default();
        header
            .set_src_cid(SRC_CID)
            .set_dst_cid(DST_CID)
            .set_src_port(SRC_PORT)
            .set_dst_port(DST_PORT)
            .set_len(LEN)
            .set_type(TYPE)
            .set_op(OP)
            .set_flags(FLAGS)
            .set_buf_alloc(BUF_ALLOC)
            .set_fwd_cnt(FWD_CNT);
        mem.write_obj(header, GuestAddress(HEADER_WRITE_ADDR))
            .unwrap();

        // Device-readable descriptors (no VRING_DESC_F_WRITE) for the TX path.
        let descriptors = vec![
            FuzzingDescriptor {
                addr: HEADER_WRITE_ADDR,
                len: DESC_LEN,
                flags: 0,
                next: 0,
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
        let chain = vq.build_desc_chain(&q_descriptors).unwrap();

        let mut packet = VsockPacketTx::from_tx_virtq_chain(&mem, chain, MAX_PKT_BUF_SIZE).unwrap();

        let mut tx_functions = Vec::new();

        // Seed the fuzzer with the header bytes at the known address so it can discover
        // the effect of different header values on packet construction.
        tx_functions.push(VsockTxFunction::_WriteToMem {
            addr: HEADER_WRITE_ADDR,
            bytes: header.as_slice().to_vec(),
        });

        // Exercise all header getters.
        assert_eq!(packet.header().src_cid(), SRC_CID);
        tx_functions.push(VsockTxFunction::SrcCid);
        assert_eq!(packet.header().dst_cid(), DST_CID);
        tx_functions.push(VsockTxFunction::DstCid);
        assert_eq!(packet.header().src_port(), SRC_PORT);
        tx_functions.push(VsockTxFunction::SrcPort);
        assert_eq!(packet.header().dst_port(), DST_PORT);
        tx_functions.push(VsockTxFunction::DstPort);
        assert_eq!(packet.header().len(), LEN);
        tx_functions.push(VsockTxFunction::Len);
        assert!(!packet.header().is_empty());
        tx_functions.push(VsockTxFunction::IsEmpty);
        assert_eq!(packet.header().type_(), TYPE);
        tx_functions.push(VsockTxFunction::Type_);
        assert_eq!(packet.header().op(), OP);
        tx_functions.push(VsockTxFunction::Op);
        assert_eq!(packet.header().flags(), FLAGS);
        tx_functions.push(VsockTxFunction::Flags);
        assert_eq!(packet.header().buf_alloc(), BUF_ALLOC);
        tx_functions.push(VsockTxFunction::BufAlloc);
        assert_eq!(packet.header().fwd_cnt(), FWD_CNT);
        tx_functions.push(VsockTxFunction::FwdCnt);

        // Read all available payload data.
        assert!(packet.data_slice().is_some());
        tx_functions.push(VsockTxFunction::ReadData { len: LEN });

        // Exercise header mutation via header_mut().
        packet.header_mut().set_flags(0).set_flag(FLAG);
        tx_functions.push(VsockTxFunction::SetFlags { flags: 0 });
        tx_functions.push(VsockTxFunction::SetFlag { flag: FLAG });

        let vsock_rw_input = VsockRwInput {
            pkt_max_data: MAX_PKT_BUF_SIZE,
            init_function: InitFunction::FromTx,
            descriptors,
            tx_functions,
            rx_functions: Vec::new(),
        };

        out_file
            .write_all(bincode::serialize(&vsock_rw_input).unwrap().as_slice())
            .unwrap();

        let written_input =
            bincode::deserialize::<VsockRwInput>(&std::fs::read(path).unwrap()).unwrap();
        assert_eq!(vsock_rw_input, written_input);
    }

    #[test]
    // Running this test will write to the fuzz corpus directory for the vsock_rw fuzz target
    // a `rx_vsock_rw_packet` file containing a valid RX descriptor chain configuration
    // and a sequence of RX operations to seed the fuzzer.
    fn write_rx_vsock_rw_packet_ops() {
        let (mut out_file, path) = create_corpus_file("vsock_rw", "rx_vsock_rw_packet");

        let mem = GuestMemoryMmap::<()>::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap();
        let vq = MockSplitQueue::new(&mem, DEFAULT_QUEUE_SIZE);

        // Device-writable descriptors (VRING_DESC_F_WRITE) for the RX path.
        let descriptors = vec![
            FuzzingDescriptor {
                addr: HEADER_WRITE_ADDR,
                len: DESC_LEN,
                flags: VRING_DESC_F_WRITE as u16,
                next: 0,
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
        let chain = vq.build_desc_chain(&q_descriptors).unwrap();

        let mut packet = VsockPacketRx::from_rx_virtq_chain(&mem, chain, MAX_PKT_BUF_SIZE).unwrap();

        let mut rx_functions = Vec::new();

        // Check space available in both writers.
        rx_functions.push(VsockRxFunction::HeaderAvailableBytes);
        rx_functions.push(VsockRxFunction::DataAvailableBytes);

        // Write a complete header.
        let mut header = PacketHeader::default();
        header
            .set_src_cid(SRC_CID)
            .set_dst_cid(DST_CID)
            .set_src_port(SRC_PORT)
            .set_dst_port(DST_PORT)
            .set_len(LEN)
            .set_type(TYPE)
            .set_op(OP)
            .set_flags(FLAGS)
            .set_buf_alloc(BUF_ALLOC)
            .set_fwd_cnt(FWD_CNT);
        packet.header_slice().write_obj(header).unwrap();
        rx_functions.push(VsockRxFunction::WriteHeader {
            src_cid: SRC_CID,
            dst_cid: DST_CID,
            src_port: SRC_PORT,
            dst_port: DST_PORT,
            len: LEN,
            type_: TYPE,
            op: OP,
            flags: FLAGS,
            buf_alloc: BUF_ALLOC,
            fwd_cnt: FWD_CNT,
        });

        // Write payload data.
        let data = vec![0xabu8; LEN as usize];
        packet.data_slice().write_all(&data).unwrap();
        rx_functions.push(VsockRxFunction::WriteData { bytes: data });

        let vsock_rw_input = VsockRwInput {
            pkt_max_data: MAX_PKT_BUF_SIZE,
            init_function: InitFunction::FromRx,
            descriptors,
            tx_functions: Vec::new(),
            rx_functions,
        };

        out_file
            .write_all(bincode::serialize(&vsock_rw_input).unwrap().as_slice())
            .unwrap();

        let written_input =
            bincode::deserialize::<VsockRwInput>(&std::fs::read(path).unwrap()).unwrap();
        assert_eq!(vsock_rw_input, written_input);
    }
}
