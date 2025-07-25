/* automatically generated by rust-bindgen 0.71.1 */

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
pub const VRING_DESC_F_NEXT: u32 = 1;
pub const VRING_DESC_F_WRITE: u32 = 2;
pub const VRING_DESC_F_INDIRECT: u32 = 4;
pub const VRING_PACKED_DESC_F_AVAIL: u32 = 7;
pub const VRING_PACKED_DESC_F_USED: u32 = 15;
pub const VRING_USED_F_NO_NOTIFY: u32 = 1;
pub const VRING_AVAIL_F_NO_INTERRUPT: u32 = 1;
pub const VRING_PACKED_EVENT_FLAG_ENABLE: u32 = 0;
pub const VRING_PACKED_EVENT_FLAG_DISABLE: u32 = 1;
pub const VRING_PACKED_EVENT_FLAG_DESC: u32 = 2;
pub const VRING_PACKED_EVENT_F_WRAP_CTR: u32 = 15;
pub const VIRTIO_RING_F_INDIRECT_DESC: u32 = 28;
pub const VIRTIO_RING_F_EVENT_IDX: u32 = 29;
pub const VRING_AVAIL_ALIGN_SIZE: u32 = 2;
pub const VRING_USED_ALIGN_SIZE: u32 = 4;
pub const VRING_DESC_ALIGN_SIZE: u32 = 16;
pub type __u16 = ::std::os::raw::c_ushort;
pub type __u32 = ::std::os::raw::c_uint;
pub type __u64 = ::std::os::raw::c_ulonglong;
pub type __le16 = __u16;
pub type __le32 = __u32;
pub type __le64 = __u64;
pub type __virtio16 = __u16;
pub type __virtio32 = __u32;
pub type __virtio64 = __u64;
#[doc = " struct vring_desc - Virtio ring descriptors,\n 16 bytes long. These can chain together via @next.\n\n @addr: buffer address (guest-physical)\n @len: buffer length\n @flags: descriptor flags\n @next: index of the next descriptor in the chain,\n        if the VRING_DESC_F_NEXT flag is set. We chain unused\n        descriptors via this, too."]
#[repr(C)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct vring_desc {
    pub addr: __virtio64,
    pub len: __virtio32,
    pub flags: __virtio16,
    pub next: __virtio16,
}
#[allow(clippy::unnecessary_operation, clippy::identity_op)]
const _: () = {
    ["Size of vring_desc"][::std::mem::size_of::<vring_desc>() - 16usize];
    ["Alignment of vring_desc"][::std::mem::align_of::<vring_desc>() - 8usize];
    ["Offset of field: vring_desc::addr"][::std::mem::offset_of!(vring_desc, addr) - 0usize];
    ["Offset of field: vring_desc::len"][::std::mem::offset_of!(vring_desc, len) - 8usize];
    ["Offset of field: vring_desc::flags"][::std::mem::offset_of!(vring_desc, flags) - 12usize];
    ["Offset of field: vring_desc::next"][::std::mem::offset_of!(vring_desc, next) - 14usize];
};
#[repr(C)]
#[derive(Debug, Default)]
pub struct vring_avail {
    pub flags: __virtio16,
    pub idx: __virtio16,
    pub ring: __IncompleteArrayField<__virtio16>,
}
#[allow(clippy::unnecessary_operation, clippy::identity_op)]
const _: () = {
    ["Size of vring_avail"][::std::mem::size_of::<vring_avail>() - 4usize];
    ["Alignment of vring_avail"][::std::mem::align_of::<vring_avail>() - 2usize];
    ["Offset of field: vring_avail::flags"][::std::mem::offset_of!(vring_avail, flags) - 0usize];
    ["Offset of field: vring_avail::idx"][::std::mem::offset_of!(vring_avail, idx) - 2usize];
    ["Offset of field: vring_avail::ring"][::std::mem::offset_of!(vring_avail, ring) - 4usize];
};
#[repr(C)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct vring_used_elem {
    pub id: __virtio32,
    pub len: __virtio32,
}
#[allow(clippy::unnecessary_operation, clippy::identity_op)]
const _: () = {
    ["Size of vring_used_elem"][::std::mem::size_of::<vring_used_elem>() - 8usize];
    ["Alignment of vring_used_elem"][::std::mem::align_of::<vring_used_elem>() - 4usize];
    ["Offset of field: vring_used_elem::id"][::std::mem::offset_of!(vring_used_elem, id) - 0usize];
    ["Offset of field: vring_used_elem::len"]
        [::std::mem::offset_of!(vring_used_elem, len) - 4usize];
};
pub type vring_used_elem_t = vring_used_elem;
#[repr(C)]
#[derive(Debug, Default)]
pub struct vring_used {
    pub flags: __virtio16,
    pub idx: __virtio16,
    pub ring: __IncompleteArrayField<vring_used_elem_t>,
}
#[allow(clippy::unnecessary_operation, clippy::identity_op)]
const _: () = {
    ["Size of vring_used"][::std::mem::size_of::<vring_used>() - 4usize];
    ["Alignment of vring_used"][::std::mem::align_of::<vring_used>() - 4usize];
    ["Offset of field: vring_used::flags"][::std::mem::offset_of!(vring_used, flags) - 0usize];
    ["Offset of field: vring_used::idx"][::std::mem::offset_of!(vring_used, idx) - 2usize];
    ["Offset of field: vring_used::ring"][::std::mem::offset_of!(vring_used, ring) - 4usize];
};
#[doc = " struct vring_desc - Virtio ring descriptors,\n 16 bytes long. These can chain together via @next.\n\n @addr: buffer address (guest-physical)\n @len: buffer length\n @flags: descriptor flags\n @next: index of the next descriptor in the chain,\n        if the VRING_DESC_F_NEXT flag is set. We chain unused\n        descriptors via this, too."]
pub type vring_desc_t = vring_desc;
pub type vring_avail_t = vring_avail;
pub type vring_used_t = vring_used;
#[repr(C)]
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct vring {
    pub num: ::std::os::raw::c_uint,
    pub desc: *mut vring_desc_t,
    pub avail: *mut vring_avail_t,
    pub used: *mut vring_used_t,
}
#[allow(clippy::unnecessary_operation, clippy::identity_op)]
const _: () = {
    ["Size of vring"][::std::mem::size_of::<vring>() - 16usize];
    ["Alignment of vring"][::std::mem::align_of::<vring>() - 4usize];
    ["Offset of field: vring::num"][::std::mem::offset_of!(vring, num) - 0usize];
    ["Offset of field: vring::desc"][::std::mem::offset_of!(vring, desc) - 4usize];
    ["Offset of field: vring::avail"][::std::mem::offset_of!(vring, avail) - 8usize];
    ["Offset of field: vring::used"][::std::mem::offset_of!(vring, used) - 12usize];
};
impl Default for vring {
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
pub struct vring_packed_desc_event {
    pub off_wrap: __le16,
    pub flags: __le16,
}
#[allow(clippy::unnecessary_operation, clippy::identity_op)]
const _: () = {
    ["Size of vring_packed_desc_event"][::std::mem::size_of::<vring_packed_desc_event>() - 4usize];
    ["Alignment of vring_packed_desc_event"]
        [::std::mem::align_of::<vring_packed_desc_event>() - 2usize];
    ["Offset of field: vring_packed_desc_event::off_wrap"]
        [::std::mem::offset_of!(vring_packed_desc_event, off_wrap) - 0usize];
    ["Offset of field: vring_packed_desc_event::flags"]
        [::std::mem::offset_of!(vring_packed_desc_event, flags) - 2usize];
};
#[repr(C)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct vring_packed_desc {
    pub addr: __le64,
    pub len: __le32,
    pub id: __le16,
    pub flags: __le16,
}
#[allow(clippy::unnecessary_operation, clippy::identity_op)]
const _: () = {
    ["Size of vring_packed_desc"][::std::mem::size_of::<vring_packed_desc>() - 16usize];
    ["Alignment of vring_packed_desc"][::std::mem::align_of::<vring_packed_desc>() - 8usize];
    ["Offset of field: vring_packed_desc::addr"]
        [::std::mem::offset_of!(vring_packed_desc, addr) - 0usize];
    ["Offset of field: vring_packed_desc::len"]
        [::std::mem::offset_of!(vring_packed_desc, len) - 8usize];
    ["Offset of field: vring_packed_desc::id"]
        [::std::mem::offset_of!(vring_packed_desc, id) - 12usize];
    ["Offset of field: vring_packed_desc::flags"]
        [::std::mem::offset_of!(vring_packed_desc, flags) - 14usize];
};
