/* automatically generated by rust-bindgen 0.63.0 */

#[repr(C)]
#[derive(Default)]
pub struct __IncompleteArrayField<T>(::std::marker::PhantomData<T>, [T; 0]);
impl<T> __IncompleteArrayField<T> {
    #[inline]
    pub const fn new() -> Self {
        __IncompleteArrayField(::std::marker::PhantomData, [])
    }
    #[inline]
    pub fn as_ptr(&self) -> *const T {
        self as *const _ as *const T
    }
    #[inline]
    pub fn as_mut_ptr(&mut self) -> *mut T {
        self as *mut _ as *mut T
    }
    #[inline]
    pub unsafe fn as_slice(&self, len: usize) -> &[T] {
        ::std::slice::from_raw_parts(self.as_ptr(), len)
    }
    #[inline]
    pub unsafe fn as_mut_slice(&mut self, len: usize) -> &mut [T] {
        ::std::slice::from_raw_parts_mut(self.as_mut_ptr(), len)
    }
}
impl<T> ::std::fmt::Debug for __IncompleteArrayField<T> {
    fn fmt(&self, fmt: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
        fmt.write_str("__IncompleteArrayField")
    }
}
pub const VIRTIO_NET_F_CSUM: u32 = 0;
pub const VIRTIO_NET_F_GUEST_CSUM: u32 = 1;
pub const VIRTIO_NET_F_CTRL_GUEST_OFFLOADS: u32 = 2;
pub const VIRTIO_NET_F_MTU: u32 = 3;
pub const VIRTIO_NET_F_MAC: u32 = 5;
pub const VIRTIO_NET_F_GUEST_TSO4: u32 = 7;
pub const VIRTIO_NET_F_GUEST_TSO6: u32 = 8;
pub const VIRTIO_NET_F_GUEST_ECN: u32 = 9;
pub const VIRTIO_NET_F_GUEST_UFO: u32 = 10;
pub const VIRTIO_NET_F_HOST_TSO4: u32 = 11;
pub const VIRTIO_NET_F_HOST_TSO6: u32 = 12;
pub const VIRTIO_NET_F_HOST_ECN: u32 = 13;
pub const VIRTIO_NET_F_HOST_UFO: u32 = 14;
pub const VIRTIO_NET_F_MRG_RXBUF: u32 = 15;
pub const VIRTIO_NET_F_STATUS: u32 = 16;
pub const VIRTIO_NET_F_CTRL_VQ: u32 = 17;
pub const VIRTIO_NET_F_CTRL_RX: u32 = 18;
pub const VIRTIO_NET_F_CTRL_VLAN: u32 = 19;
pub const VIRTIO_NET_F_CTRL_RX_EXTRA: u32 = 20;
pub const VIRTIO_NET_F_GUEST_ANNOUNCE: u32 = 21;
pub const VIRTIO_NET_F_MQ: u32 = 22;
pub const VIRTIO_NET_F_CTRL_MAC_ADDR: u32 = 23;
pub const VIRTIO_NET_F_VQ_NOTF_COAL: u32 = 52;
pub const VIRTIO_NET_F_NOTF_COAL: u32 = 53;
pub const VIRTIO_NET_F_GUEST_USO4: u32 = 54;
pub const VIRTIO_NET_F_GUEST_USO6: u32 = 55;
pub const VIRTIO_NET_F_HOST_USO: u32 = 56;
pub const VIRTIO_NET_F_HASH_REPORT: u32 = 57;
pub const VIRTIO_NET_F_GUEST_HDRLEN: u32 = 59;
pub const VIRTIO_NET_F_RSS: u32 = 60;
pub const VIRTIO_NET_F_RSC_EXT: u32 = 61;
pub const VIRTIO_NET_F_STANDBY: u32 = 62;
pub const VIRTIO_NET_F_SPEED_DUPLEX: u32 = 63;
pub const VIRTIO_NET_F_GSO: u32 = 6;
pub const VIRTIO_NET_S_LINK_UP: u32 = 1;
pub const VIRTIO_NET_S_ANNOUNCE: u32 = 2;
pub const VIRTIO_NET_RSS_HASH_TYPE_IPv4: u32 = 1;
pub const VIRTIO_NET_RSS_HASH_TYPE_TCPv4: u32 = 2;
pub const VIRTIO_NET_RSS_HASH_TYPE_UDPv4: u32 = 4;
pub const VIRTIO_NET_RSS_HASH_TYPE_IPv6: u32 = 8;
pub const VIRTIO_NET_RSS_HASH_TYPE_TCPv6: u32 = 16;
pub const VIRTIO_NET_RSS_HASH_TYPE_UDPv6: u32 = 32;
pub const VIRTIO_NET_RSS_HASH_TYPE_IP_EX: u32 = 64;
pub const VIRTIO_NET_RSS_HASH_TYPE_TCP_EX: u32 = 128;
pub const VIRTIO_NET_RSS_HASH_TYPE_UDP_EX: u32 = 256;
pub const VIRTIO_NET_HDR_F_NEEDS_CSUM: u32 = 1;
pub const VIRTIO_NET_HDR_F_DATA_VALID: u32 = 2;
pub const VIRTIO_NET_HDR_F_RSC_INFO: u32 = 4;
pub const VIRTIO_NET_HDR_GSO_NONE: u32 = 0;
pub const VIRTIO_NET_HDR_GSO_TCPV4: u32 = 1;
pub const VIRTIO_NET_HDR_GSO_UDP: u32 = 3;
pub const VIRTIO_NET_HDR_GSO_TCPV6: u32 = 4;
pub const VIRTIO_NET_HDR_GSO_UDP_L4: u32 = 5;
pub const VIRTIO_NET_HDR_GSO_ECN: u32 = 128;
pub const VIRTIO_NET_HASH_REPORT_NONE: u32 = 0;
pub const VIRTIO_NET_HASH_REPORT_IPv4: u32 = 1;
pub const VIRTIO_NET_HASH_REPORT_TCPv4: u32 = 2;
pub const VIRTIO_NET_HASH_REPORT_UDPv4: u32 = 3;
pub const VIRTIO_NET_HASH_REPORT_IPv6: u32 = 4;
pub const VIRTIO_NET_HASH_REPORT_TCPv6: u32 = 5;
pub const VIRTIO_NET_HASH_REPORT_UDPv6: u32 = 6;
pub const VIRTIO_NET_HASH_REPORT_IPv6_EX: u32 = 7;
pub const VIRTIO_NET_HASH_REPORT_TCPv6_EX: u32 = 8;
pub const VIRTIO_NET_HASH_REPORT_UDPv6_EX: u32 = 9;
pub const VIRTIO_NET_OK: u32 = 0;
pub const VIRTIO_NET_ERR: u32 = 1;
pub const VIRTIO_NET_CTRL_RX: u32 = 0;
pub const VIRTIO_NET_CTRL_RX_PROMISC: u32 = 0;
pub const VIRTIO_NET_CTRL_RX_ALLMULTI: u32 = 1;
pub const VIRTIO_NET_CTRL_RX_ALLUNI: u32 = 2;
pub const VIRTIO_NET_CTRL_RX_NOMULTI: u32 = 3;
pub const VIRTIO_NET_CTRL_RX_NOUNI: u32 = 4;
pub const VIRTIO_NET_CTRL_RX_NOBCAST: u32 = 5;
pub const VIRTIO_NET_CTRL_MAC: u32 = 1;
pub const VIRTIO_NET_CTRL_MAC_TABLE_SET: u32 = 0;
pub const VIRTIO_NET_CTRL_MAC_ADDR_SET: u32 = 1;
pub const VIRTIO_NET_CTRL_VLAN: u32 = 2;
pub const VIRTIO_NET_CTRL_VLAN_ADD: u32 = 0;
pub const VIRTIO_NET_CTRL_VLAN_DEL: u32 = 1;
pub const VIRTIO_NET_CTRL_ANNOUNCE: u32 = 3;
pub const VIRTIO_NET_CTRL_ANNOUNCE_ACK: u32 = 0;
pub const VIRTIO_NET_CTRL_MQ: u32 = 4;
pub const VIRTIO_NET_CTRL_MQ_VQ_PAIRS_SET: u32 = 0;
pub const VIRTIO_NET_CTRL_MQ_VQ_PAIRS_MIN: u32 = 1;
pub const VIRTIO_NET_CTRL_MQ_VQ_PAIRS_MAX: u32 = 32768;
pub const VIRTIO_NET_CTRL_MQ_RSS_CONFIG: u32 = 1;
pub const VIRTIO_NET_CTRL_MQ_HASH_CONFIG: u32 = 2;
pub const VIRTIO_NET_CTRL_GUEST_OFFLOADS: u32 = 5;
pub const VIRTIO_NET_CTRL_GUEST_OFFLOADS_SET: u32 = 0;
pub const VIRTIO_NET_CTRL_NOTF_COAL: u32 = 6;
pub const VIRTIO_NET_CTRL_NOTF_COAL_TX_SET: u32 = 0;
pub const VIRTIO_NET_CTRL_NOTF_COAL_RX_SET: u32 = 1;
pub const VIRTIO_NET_CTRL_NOTF_COAL_VQ_SET: u32 = 2;
pub const VIRTIO_NET_CTRL_NOTF_COAL_VQ_GET: u32 = 3;
pub type __u8 = ::std::os::raw::c_uchar;
pub type __u16 = ::std::os::raw::c_ushort;
pub type __u32 = ::std::os::raw::c_uint;
pub type __le16 = __u16;
pub type __le32 = __u32;
pub type __virtio16 = __u16;
pub type __virtio32 = __u32;
#[repr(C, packed)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct virtio_net_config {
    pub mac: [__u8; 6usize],
    pub status: __virtio16,
    pub max_virtqueue_pairs: __virtio16,
    pub mtu: __virtio16,
    pub speed: __le32,
    pub duplex: __u8,
    pub rss_max_key_size: __u8,
    pub rss_max_indirection_table_length: __le16,
    pub supported_hash_types: __le32,
}
#[test]
fn bindgen_test_layout_virtio_net_config() {
    const UNINIT: ::std::mem::MaybeUninit<virtio_net_config> = ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
        ::std::mem::size_of::<virtio_net_config>(),
        24usize,
        concat!("Size of: ", stringify!(virtio_net_config))
    );
    assert_eq!(
        ::std::mem::align_of::<virtio_net_config>(),
        1usize,
        concat!("Alignment of ", stringify!(virtio_net_config))
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).mac) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_config),
            "::",
            stringify!(mac)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).status) as usize - ptr as usize },
        6usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_config),
            "::",
            stringify!(status)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).max_virtqueue_pairs) as usize - ptr as usize },
        8usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_config),
            "::",
            stringify!(max_virtqueue_pairs)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).mtu) as usize - ptr as usize },
        10usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_config),
            "::",
            stringify!(mtu)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).speed) as usize - ptr as usize },
        12usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_config),
            "::",
            stringify!(speed)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).duplex) as usize - ptr as usize },
        16usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_config),
            "::",
            stringify!(duplex)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).rss_max_key_size) as usize - ptr as usize },
        17usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_config),
            "::",
            stringify!(rss_max_key_size)
        )
    );
    assert_eq!(
        unsafe {
            ::std::ptr::addr_of!((*ptr).rss_max_indirection_table_length) as usize - ptr as usize
        },
        18usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_config),
            "::",
            stringify!(rss_max_indirection_table_length)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).supported_hash_types) as usize - ptr as usize },
        20usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_config),
            "::",
            stringify!(supported_hash_types)
        )
    );
}
#[repr(C)]
#[derive(Copy, Clone)]
pub struct virtio_net_hdr_v1 {
    pub flags: __u8,
    pub gso_type: __u8,
    pub hdr_len: __virtio16,
    pub gso_size: __virtio16,
    pub __bindgen_anon_1: virtio_net_hdr_v1__bindgen_ty_1,
    pub num_buffers: __virtio16,
}
#[repr(C)]
#[derive(Copy, Clone)]
pub union virtio_net_hdr_v1__bindgen_ty_1 {
    pub __bindgen_anon_1: virtio_net_hdr_v1__bindgen_ty_1__bindgen_ty_1,
    pub csum: virtio_net_hdr_v1__bindgen_ty_1__bindgen_ty_2,
    pub rsc: virtio_net_hdr_v1__bindgen_ty_1__bindgen_ty_3,
}
#[repr(C)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct virtio_net_hdr_v1__bindgen_ty_1__bindgen_ty_1 {
    pub csum_start: __virtio16,
    pub csum_offset: __virtio16,
}
#[test]
fn bindgen_test_layout_virtio_net_hdr_v1__bindgen_ty_1__bindgen_ty_1() {
    const UNINIT: ::std::mem::MaybeUninit<virtio_net_hdr_v1__bindgen_ty_1__bindgen_ty_1> =
        ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
        ::std::mem::size_of::<virtio_net_hdr_v1__bindgen_ty_1__bindgen_ty_1>(),
        4usize,
        concat!(
            "Size of: ",
            stringify!(virtio_net_hdr_v1__bindgen_ty_1__bindgen_ty_1)
        )
    );
    assert_eq!(
        ::std::mem::align_of::<virtio_net_hdr_v1__bindgen_ty_1__bindgen_ty_1>(),
        2usize,
        concat!(
            "Alignment of ",
            stringify!(virtio_net_hdr_v1__bindgen_ty_1__bindgen_ty_1)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).csum_start) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_hdr_v1__bindgen_ty_1__bindgen_ty_1),
            "::",
            stringify!(csum_start)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).csum_offset) as usize - ptr as usize },
        2usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_hdr_v1__bindgen_ty_1__bindgen_ty_1),
            "::",
            stringify!(csum_offset)
        )
    );
}
#[repr(C)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct virtio_net_hdr_v1__bindgen_ty_1__bindgen_ty_2 {
    pub start: __virtio16,
    pub offset: __virtio16,
}
#[test]
fn bindgen_test_layout_virtio_net_hdr_v1__bindgen_ty_1__bindgen_ty_2() {
    const UNINIT: ::std::mem::MaybeUninit<virtio_net_hdr_v1__bindgen_ty_1__bindgen_ty_2> =
        ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
        ::std::mem::size_of::<virtio_net_hdr_v1__bindgen_ty_1__bindgen_ty_2>(),
        4usize,
        concat!(
            "Size of: ",
            stringify!(virtio_net_hdr_v1__bindgen_ty_1__bindgen_ty_2)
        )
    );
    assert_eq!(
        ::std::mem::align_of::<virtio_net_hdr_v1__bindgen_ty_1__bindgen_ty_2>(),
        2usize,
        concat!(
            "Alignment of ",
            stringify!(virtio_net_hdr_v1__bindgen_ty_1__bindgen_ty_2)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).start) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_hdr_v1__bindgen_ty_1__bindgen_ty_2),
            "::",
            stringify!(start)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).offset) as usize - ptr as usize },
        2usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_hdr_v1__bindgen_ty_1__bindgen_ty_2),
            "::",
            stringify!(offset)
        )
    );
}
#[repr(C)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct virtio_net_hdr_v1__bindgen_ty_1__bindgen_ty_3 {
    pub segments: __le16,
    pub dup_acks: __le16,
}
#[test]
fn bindgen_test_layout_virtio_net_hdr_v1__bindgen_ty_1__bindgen_ty_3() {
    const UNINIT: ::std::mem::MaybeUninit<virtio_net_hdr_v1__bindgen_ty_1__bindgen_ty_3> =
        ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
        ::std::mem::size_of::<virtio_net_hdr_v1__bindgen_ty_1__bindgen_ty_3>(),
        4usize,
        concat!(
            "Size of: ",
            stringify!(virtio_net_hdr_v1__bindgen_ty_1__bindgen_ty_3)
        )
    );
    assert_eq!(
        ::std::mem::align_of::<virtio_net_hdr_v1__bindgen_ty_1__bindgen_ty_3>(),
        2usize,
        concat!(
            "Alignment of ",
            stringify!(virtio_net_hdr_v1__bindgen_ty_1__bindgen_ty_3)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).segments) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_hdr_v1__bindgen_ty_1__bindgen_ty_3),
            "::",
            stringify!(segments)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).dup_acks) as usize - ptr as usize },
        2usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_hdr_v1__bindgen_ty_1__bindgen_ty_3),
            "::",
            stringify!(dup_acks)
        )
    );
}
#[test]
fn bindgen_test_layout_virtio_net_hdr_v1__bindgen_ty_1() {
    const UNINIT: ::std::mem::MaybeUninit<virtio_net_hdr_v1__bindgen_ty_1> =
        ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
        ::std::mem::size_of::<virtio_net_hdr_v1__bindgen_ty_1>(),
        4usize,
        concat!("Size of: ", stringify!(virtio_net_hdr_v1__bindgen_ty_1))
    );
    assert_eq!(
        ::std::mem::align_of::<virtio_net_hdr_v1__bindgen_ty_1>(),
        2usize,
        concat!("Alignment of ", stringify!(virtio_net_hdr_v1__bindgen_ty_1))
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).csum) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_hdr_v1__bindgen_ty_1),
            "::",
            stringify!(csum)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).rsc) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_hdr_v1__bindgen_ty_1),
            "::",
            stringify!(rsc)
        )
    );
}
impl Default for virtio_net_hdr_v1__bindgen_ty_1 {
    fn default() -> Self {
        let mut s = ::std::mem::MaybeUninit::<Self>::uninit();
        unsafe {
            ::std::ptr::write_bytes(s.as_mut_ptr(), 0, 1);
            s.assume_init()
        }
    }
}
#[test]
fn bindgen_test_layout_virtio_net_hdr_v1() {
    const UNINIT: ::std::mem::MaybeUninit<virtio_net_hdr_v1> = ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
        ::std::mem::size_of::<virtio_net_hdr_v1>(),
        12usize,
        concat!("Size of: ", stringify!(virtio_net_hdr_v1))
    );
    assert_eq!(
        ::std::mem::align_of::<virtio_net_hdr_v1>(),
        2usize,
        concat!("Alignment of ", stringify!(virtio_net_hdr_v1))
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).flags) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_hdr_v1),
            "::",
            stringify!(flags)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).gso_type) as usize - ptr as usize },
        1usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_hdr_v1),
            "::",
            stringify!(gso_type)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).hdr_len) as usize - ptr as usize },
        2usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_hdr_v1),
            "::",
            stringify!(hdr_len)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).gso_size) as usize - ptr as usize },
        4usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_hdr_v1),
            "::",
            stringify!(gso_size)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).num_buffers) as usize - ptr as usize },
        10usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_hdr_v1),
            "::",
            stringify!(num_buffers)
        )
    );
}
impl Default for virtio_net_hdr_v1 {
    fn default() -> Self {
        let mut s = ::std::mem::MaybeUninit::<Self>::uninit();
        unsafe {
            ::std::ptr::write_bytes(s.as_mut_ptr(), 0, 1);
            s.assume_init()
        }
    }
}
#[repr(C)]
#[derive(Copy, Clone)]
pub struct virtio_net_hdr_v1_hash {
    pub hdr: virtio_net_hdr_v1,
    pub hash_value: __le32,
    pub hash_report: __le16,
    pub padding: __le16,
}
#[test]
fn bindgen_test_layout_virtio_net_hdr_v1_hash() {
    const UNINIT: ::std::mem::MaybeUninit<virtio_net_hdr_v1_hash> =
        ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
        ::std::mem::size_of::<virtio_net_hdr_v1_hash>(),
        20usize,
        concat!("Size of: ", stringify!(virtio_net_hdr_v1_hash))
    );
    assert_eq!(
        ::std::mem::align_of::<virtio_net_hdr_v1_hash>(),
        4usize,
        concat!("Alignment of ", stringify!(virtio_net_hdr_v1_hash))
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).hdr) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_hdr_v1_hash),
            "::",
            stringify!(hdr)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).hash_value) as usize - ptr as usize },
        12usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_hdr_v1_hash),
            "::",
            stringify!(hash_value)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).hash_report) as usize - ptr as usize },
        16usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_hdr_v1_hash),
            "::",
            stringify!(hash_report)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).padding) as usize - ptr as usize },
        18usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_hdr_v1_hash),
            "::",
            stringify!(padding)
        )
    );
}
impl Default for virtio_net_hdr_v1_hash {
    fn default() -> Self {
        let mut s = ::std::mem::MaybeUninit::<Self>::uninit();
        unsafe {
            ::std::ptr::write_bytes(s.as_mut_ptr(), 0, 1);
            s.assume_init()
        }
    }
}
#[repr(C)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct virtio_net_hdr {
    pub flags: __u8,
    pub gso_type: __u8,
    pub hdr_len: __virtio16,
    pub gso_size: __virtio16,
    pub csum_start: __virtio16,
    pub csum_offset: __virtio16,
}
#[test]
fn bindgen_test_layout_virtio_net_hdr() {
    const UNINIT: ::std::mem::MaybeUninit<virtio_net_hdr> = ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
        ::std::mem::size_of::<virtio_net_hdr>(),
        10usize,
        concat!("Size of: ", stringify!(virtio_net_hdr))
    );
    assert_eq!(
        ::std::mem::align_of::<virtio_net_hdr>(),
        2usize,
        concat!("Alignment of ", stringify!(virtio_net_hdr))
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).flags) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_hdr),
            "::",
            stringify!(flags)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).gso_type) as usize - ptr as usize },
        1usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_hdr),
            "::",
            stringify!(gso_type)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).hdr_len) as usize - ptr as usize },
        2usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_hdr),
            "::",
            stringify!(hdr_len)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).gso_size) as usize - ptr as usize },
        4usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_hdr),
            "::",
            stringify!(gso_size)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).csum_start) as usize - ptr as usize },
        6usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_hdr),
            "::",
            stringify!(csum_start)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).csum_offset) as usize - ptr as usize },
        8usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_hdr),
            "::",
            stringify!(csum_offset)
        )
    );
}
#[repr(C)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct virtio_net_hdr_mrg_rxbuf {
    pub hdr: virtio_net_hdr,
    pub num_buffers: __virtio16,
}
#[test]
fn bindgen_test_layout_virtio_net_hdr_mrg_rxbuf() {
    const UNINIT: ::std::mem::MaybeUninit<virtio_net_hdr_mrg_rxbuf> =
        ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
        ::std::mem::size_of::<virtio_net_hdr_mrg_rxbuf>(),
        12usize,
        concat!("Size of: ", stringify!(virtio_net_hdr_mrg_rxbuf))
    );
    assert_eq!(
        ::std::mem::align_of::<virtio_net_hdr_mrg_rxbuf>(),
        2usize,
        concat!("Alignment of ", stringify!(virtio_net_hdr_mrg_rxbuf))
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).hdr) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_hdr_mrg_rxbuf),
            "::",
            stringify!(hdr)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).num_buffers) as usize - ptr as usize },
        10usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_hdr_mrg_rxbuf),
            "::",
            stringify!(num_buffers)
        )
    );
}
#[repr(C, packed)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct virtio_net_ctrl_hdr {
    pub class: __u8,
    pub cmd: __u8,
}
#[test]
fn bindgen_test_layout_virtio_net_ctrl_hdr() {
    const UNINIT: ::std::mem::MaybeUninit<virtio_net_ctrl_hdr> = ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
        ::std::mem::size_of::<virtio_net_ctrl_hdr>(),
        2usize,
        concat!("Size of: ", stringify!(virtio_net_ctrl_hdr))
    );
    assert_eq!(
        ::std::mem::align_of::<virtio_net_ctrl_hdr>(),
        1usize,
        concat!("Alignment of ", stringify!(virtio_net_ctrl_hdr))
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).class) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_ctrl_hdr),
            "::",
            stringify!(class)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).cmd) as usize - ptr as usize },
        1usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_ctrl_hdr),
            "::",
            stringify!(cmd)
        )
    );
}
pub type virtio_net_ctrl_ack = __u8;
#[repr(C, packed)]
pub struct virtio_net_ctrl_mac {
    pub entries: __virtio32,
    pub macs: __IncompleteArrayField<[__u8; 6usize]>,
}
#[test]
fn bindgen_test_layout_virtio_net_ctrl_mac() {
    const UNINIT: ::std::mem::MaybeUninit<virtio_net_ctrl_mac> = ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
        ::std::mem::size_of::<virtio_net_ctrl_mac>(),
        4usize,
        concat!("Size of: ", stringify!(virtio_net_ctrl_mac))
    );
    assert_eq!(
        ::std::mem::align_of::<virtio_net_ctrl_mac>(),
        1usize,
        concat!("Alignment of ", stringify!(virtio_net_ctrl_mac))
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).entries) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_ctrl_mac),
            "::",
            stringify!(entries)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).macs) as usize - ptr as usize },
        4usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_ctrl_mac),
            "::",
            stringify!(macs)
        )
    );
}
impl Default for virtio_net_ctrl_mac {
    fn default() -> Self {
        let mut s = ::std::mem::MaybeUninit::<Self>::uninit();
        unsafe {
            ::std::ptr::write_bytes(s.as_mut_ptr(), 0, 1);
            s.assume_init()
        }
    }
}
#[repr(C)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct virtio_net_ctrl_mq {
    pub virtqueue_pairs: __virtio16,
}
#[test]
fn bindgen_test_layout_virtio_net_ctrl_mq() {
    const UNINIT: ::std::mem::MaybeUninit<virtio_net_ctrl_mq> = ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
        ::std::mem::size_of::<virtio_net_ctrl_mq>(),
        2usize,
        concat!("Size of: ", stringify!(virtio_net_ctrl_mq))
    );
    assert_eq!(
        ::std::mem::align_of::<virtio_net_ctrl_mq>(),
        2usize,
        concat!("Alignment of ", stringify!(virtio_net_ctrl_mq))
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).virtqueue_pairs) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_ctrl_mq),
            "::",
            stringify!(virtqueue_pairs)
        )
    );
}
#[repr(C)]
#[derive(Debug, Default)]
pub struct virtio_net_rss_config {
    pub hash_types: __le32,
    pub indirection_table_mask: __le16,
    pub unclassified_queue: __le16,
    pub indirection_table: [__le16; 1usize],
    pub max_tx_vq: __le16,
    pub hash_key_length: __u8,
    pub hash_key_data: __IncompleteArrayField<__u8>,
}
#[test]
fn bindgen_test_layout_virtio_net_rss_config() {
    const UNINIT: ::std::mem::MaybeUninit<virtio_net_rss_config> =
        ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
        ::std::mem::size_of::<virtio_net_rss_config>(),
        16usize,
        concat!("Size of: ", stringify!(virtio_net_rss_config))
    );
    assert_eq!(
        ::std::mem::align_of::<virtio_net_rss_config>(),
        4usize,
        concat!("Alignment of ", stringify!(virtio_net_rss_config))
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).hash_types) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_rss_config),
            "::",
            stringify!(hash_types)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).indirection_table_mask) as usize - ptr as usize },
        4usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_rss_config),
            "::",
            stringify!(indirection_table_mask)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).unclassified_queue) as usize - ptr as usize },
        6usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_rss_config),
            "::",
            stringify!(unclassified_queue)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).indirection_table) as usize - ptr as usize },
        8usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_rss_config),
            "::",
            stringify!(indirection_table)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).max_tx_vq) as usize - ptr as usize },
        10usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_rss_config),
            "::",
            stringify!(max_tx_vq)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).hash_key_length) as usize - ptr as usize },
        12usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_rss_config),
            "::",
            stringify!(hash_key_length)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).hash_key_data) as usize - ptr as usize },
        13usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_rss_config),
            "::",
            stringify!(hash_key_data)
        )
    );
}
#[repr(C)]
#[derive(Debug, Default)]
pub struct virtio_net_hash_config {
    pub hash_types: __le32,
    pub reserved: [__le16; 4usize],
    pub hash_key_length: __u8,
    pub hash_key_data: __IncompleteArrayField<__u8>,
}
#[test]
fn bindgen_test_layout_virtio_net_hash_config() {
    const UNINIT: ::std::mem::MaybeUninit<virtio_net_hash_config> =
        ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
        ::std::mem::size_of::<virtio_net_hash_config>(),
        16usize,
        concat!("Size of: ", stringify!(virtio_net_hash_config))
    );
    assert_eq!(
        ::std::mem::align_of::<virtio_net_hash_config>(),
        4usize,
        concat!("Alignment of ", stringify!(virtio_net_hash_config))
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).hash_types) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_hash_config),
            "::",
            stringify!(hash_types)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).reserved) as usize - ptr as usize },
        4usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_hash_config),
            "::",
            stringify!(reserved)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).hash_key_length) as usize - ptr as usize },
        12usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_hash_config),
            "::",
            stringify!(hash_key_length)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).hash_key_data) as usize - ptr as usize },
        13usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_hash_config),
            "::",
            stringify!(hash_key_data)
        )
    );
}
#[repr(C)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct virtio_net_ctrl_coal_tx {
    pub tx_max_packets: __le32,
    pub tx_usecs: __le32,
}
#[test]
fn bindgen_test_layout_virtio_net_ctrl_coal_tx() {
    const UNINIT: ::std::mem::MaybeUninit<virtio_net_ctrl_coal_tx> =
        ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
        ::std::mem::size_of::<virtio_net_ctrl_coal_tx>(),
        8usize,
        concat!("Size of: ", stringify!(virtio_net_ctrl_coal_tx))
    );
    assert_eq!(
        ::std::mem::align_of::<virtio_net_ctrl_coal_tx>(),
        4usize,
        concat!("Alignment of ", stringify!(virtio_net_ctrl_coal_tx))
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).tx_max_packets) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_ctrl_coal_tx),
            "::",
            stringify!(tx_max_packets)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).tx_usecs) as usize - ptr as usize },
        4usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_ctrl_coal_tx),
            "::",
            stringify!(tx_usecs)
        )
    );
}
#[repr(C)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct virtio_net_ctrl_coal_rx {
    pub rx_max_packets: __le32,
    pub rx_usecs: __le32,
}
#[test]
fn bindgen_test_layout_virtio_net_ctrl_coal_rx() {
    const UNINIT: ::std::mem::MaybeUninit<virtio_net_ctrl_coal_rx> =
        ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
        ::std::mem::size_of::<virtio_net_ctrl_coal_rx>(),
        8usize,
        concat!("Size of: ", stringify!(virtio_net_ctrl_coal_rx))
    );
    assert_eq!(
        ::std::mem::align_of::<virtio_net_ctrl_coal_rx>(),
        4usize,
        concat!("Alignment of ", stringify!(virtio_net_ctrl_coal_rx))
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).rx_max_packets) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_ctrl_coal_rx),
            "::",
            stringify!(rx_max_packets)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).rx_usecs) as usize - ptr as usize },
        4usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_ctrl_coal_rx),
            "::",
            stringify!(rx_usecs)
        )
    );
}
#[repr(C)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct virtio_net_ctrl_coal {
    pub max_packets: __le32,
    pub max_usecs: __le32,
}
#[test]
fn bindgen_test_layout_virtio_net_ctrl_coal() {
    const UNINIT: ::std::mem::MaybeUninit<virtio_net_ctrl_coal> = ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
        ::std::mem::size_of::<virtio_net_ctrl_coal>(),
        8usize,
        concat!("Size of: ", stringify!(virtio_net_ctrl_coal))
    );
    assert_eq!(
        ::std::mem::align_of::<virtio_net_ctrl_coal>(),
        4usize,
        concat!("Alignment of ", stringify!(virtio_net_ctrl_coal))
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).max_packets) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_ctrl_coal),
            "::",
            stringify!(max_packets)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).max_usecs) as usize - ptr as usize },
        4usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_ctrl_coal),
            "::",
            stringify!(max_usecs)
        )
    );
}
#[repr(C)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct virtio_net_ctrl_coal_vq {
    pub vqn: __le16,
    pub reserved: __le16,
    pub coal: virtio_net_ctrl_coal,
}
#[test]
fn bindgen_test_layout_virtio_net_ctrl_coal_vq() {
    const UNINIT: ::std::mem::MaybeUninit<virtio_net_ctrl_coal_vq> =
        ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
        ::std::mem::size_of::<virtio_net_ctrl_coal_vq>(),
        12usize,
        concat!("Size of: ", stringify!(virtio_net_ctrl_coal_vq))
    );
    assert_eq!(
        ::std::mem::align_of::<virtio_net_ctrl_coal_vq>(),
        4usize,
        concat!("Alignment of ", stringify!(virtio_net_ctrl_coal_vq))
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).vqn) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_ctrl_coal_vq),
            "::",
            stringify!(vqn)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).reserved) as usize - ptr as usize },
        2usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_ctrl_coal_vq),
            "::",
            stringify!(reserved)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).coal) as usize - ptr as usize },
        4usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_net_ctrl_coal_vq),
            "::",
            stringify!(coal)
        )
    );
}
