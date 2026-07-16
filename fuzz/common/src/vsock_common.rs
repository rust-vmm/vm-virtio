/// Shared constants used across vsock corpus-generation tests.
#[cfg(test)]
pub mod test_utils {
    pub const SRC_CID: u64 = 1;
    pub const DST_CID: u64 = 2;
    pub const SRC_PORT: u32 = 3;
    pub const DST_PORT: u32 = 4;
    pub const LEN: u32 = 16;
    pub const TYPE: u16 = 5;
    pub const OP: u16 = 6;
    pub const FLAGS: u32 = 7;
    pub const FLAG: u32 = 8;
    pub const BUF_ALLOC: u32 = 256;
    pub const FWD_CNT: u32 = 9;

    pub const MAX_PKT_BUF_SIZE: u32 = 64 * 1024;
    pub const DESC_LEN: u32 = 0x100;
    pub const HEADER_WRITE_ADDR: u64 = 0x100;
    pub const DATA_WRITE_ADDR: u64 = 0x1000;
}
