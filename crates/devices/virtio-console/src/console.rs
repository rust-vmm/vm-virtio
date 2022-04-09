use std::cmp;
use std::io::{Write};
use std::ops::Deref;
use std::sync::{Arc, Mutex};
use virtio_queue::{DescriptorChain};
use vm_memory::{Bytes, GuestMemory};

/// Console device resize feature.
pub const VIRTIO_CONSOLE_F_SIZE: u64 = 0;

/// Console device multiport feature.
pub const VIRTIO_CONSOLE_F_MULTIPORT: u64 = 1;

/// Console device emergency write feature.
pub const VIRTIO_CONSOLE_F_EMERG_WRITE: u64 = 2;


/// Console struct
pub struct Console {
    /// Data to send to the driver via receiveq
    input_buffer: Arc<Mutex<Vec<u8>>>,

    // /// Driver acked features
    // features: u64,
}

impl Console {
    /// Create new console object
    pub fn new() -> Self{
        Console {
            input_buffer: Arc::new(Mutex::new(Vec::new())),
            // features,
        }
    }

    // fn has_feature(&self, feature_pos: u64) -> bool {
    //     (self.features & (1u64 << feature_pos)) != 0
    // }

    /// Add data to the input buffer
    pub fn enqueue_data(&self, data: &mut Vec<u8>) {
        let mut input_buffer = self.input_buffer.lock().unwrap();
        input_buffer.append(data);
    }

    /// Check if input buffer is empty
    pub fn is_input_buffer_empty(&self) -> bool {
        let input_buffer = self.input_buffer.lock().unwrap();
        input_buffer.is_empty()
    }

    /// Process transmitq chain
    pub fn process_transmitq_chain<M, T>(&self, desc_chain: &mut DescriptorChain<M>, output: &mut T) -> usize
        where
            M: Deref,
            M::Target: GuestMemory,
            T: Write,
    {
        let mut len = 0;
        while let Some(desc) = desc_chain.next() {
            len = len + desc_chain.memory().write_to(
                desc.addr(),
                output,
                desc.len() as usize,
            ).unwrap();
            let _ = output.flush();
        }

        len
    }

    /// Process receiveq chain
    pub fn process_receiveq_chain<M>(&self, desc_chain: &mut DescriptorChain<M>) -> usize
        where
            M: Deref,
            M::Target: GuestMemory,
    {
        let mut sent_bytes: usize = 0;
        let mut input_buffer = self.input_buffer.lock().unwrap();

        if input_buffer.is_empty() {
            return 0;
        }

        while let Some(desc) = desc_chain.next() {
            let len_write = cmp::min(desc.len() as usize, input_buffer.len() as usize);
            let buffer_slice = input_buffer.drain(..len_write).collect::<Vec<u8>>();

            if let Err(err) = desc_chain.memory().write_slice(
                &buffer_slice[..],
                desc.addr()
            ) {
                println!("Failed to write slice: {:?}", err);
                break;
            }
            sent_bytes += len_write;

            if input_buffer.is_empty() {
                break;
            }
        }

        sent_bytes
    }
}
