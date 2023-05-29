use crate::FuzzingDescriptor;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug, PartialEq, Clone)]
pub struct BlkInput {
    pub descriptors: Vec<FuzzingDescriptor>,
    pub guestmem: Vec<(u64, Vec<u8>)>,
    pub features: u64,
    pub device_id: Option<[u8; 20]>,
}
