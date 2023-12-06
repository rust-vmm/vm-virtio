/* automatically generated by rust-bindgen 0.63.0 */

pub type __u8 = ::std::os::raw::c_uchar;
pub type __u16 = ::std::os::raw::c_ushort;
pub type __u32 = ::std::os::raw::c_uint;
pub type __le16 = __u16;
pub type __le32 = __u32;
pub const virtio_input_config_select_VIRTIO_INPUT_CFG_UNSET: virtio_input_config_select = 0;
pub const virtio_input_config_select_VIRTIO_INPUT_CFG_ID_NAME: virtio_input_config_select = 1;
pub const virtio_input_config_select_VIRTIO_INPUT_CFG_ID_SERIAL: virtio_input_config_select = 2;
pub const virtio_input_config_select_VIRTIO_INPUT_CFG_ID_DEVIDS: virtio_input_config_select = 3;
pub const virtio_input_config_select_VIRTIO_INPUT_CFG_PROP_BITS: virtio_input_config_select = 16;
pub const virtio_input_config_select_VIRTIO_INPUT_CFG_EV_BITS: virtio_input_config_select = 17;
pub const virtio_input_config_select_VIRTIO_INPUT_CFG_ABS_INFO: virtio_input_config_select = 18;
pub type virtio_input_config_select = ::std::os::raw::c_uint;
#[repr(C)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct virtio_input_absinfo {
    pub min: __le32,
    pub max: __le32,
    pub fuzz: __le32,
    pub flat: __le32,
    pub res: __le32,
}
#[test]
fn bindgen_test_layout_virtio_input_absinfo() {
    const UNINIT: ::std::mem::MaybeUninit<virtio_input_absinfo> = ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
        ::std::mem::size_of::<virtio_input_absinfo>(),
        20usize,
        concat!("Size of: ", stringify!(virtio_input_absinfo))
    );
    assert_eq!(
        ::std::mem::align_of::<virtio_input_absinfo>(),
        4usize,
        concat!("Alignment of ", stringify!(virtio_input_absinfo))
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).min) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_input_absinfo),
            "::",
            stringify!(min)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).max) as usize - ptr as usize },
        4usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_input_absinfo),
            "::",
            stringify!(max)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).fuzz) as usize - ptr as usize },
        8usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_input_absinfo),
            "::",
            stringify!(fuzz)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).flat) as usize - ptr as usize },
        12usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_input_absinfo),
            "::",
            stringify!(flat)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).res) as usize - ptr as usize },
        16usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_input_absinfo),
            "::",
            stringify!(res)
        )
    );
}
#[repr(C)]
#[derive(Debug, Default, Copy, Clone, PartialEq)]
pub struct virtio_input_devids {
    pub bustype: __le16,
    pub vendor: __le16,
    pub product: __le16,
    pub version: __le16,
}
#[test]
fn bindgen_test_layout_virtio_input_devids() {
    const UNINIT: ::std::mem::MaybeUninit<virtio_input_devids> = ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
        ::std::mem::size_of::<virtio_input_devids>(),
        8usize,
        concat!("Size of: ", stringify!(virtio_input_devids))
    );
    assert_eq!(
        ::std::mem::align_of::<virtio_input_devids>(),
        2usize,
        concat!("Alignment of ", stringify!(virtio_input_devids))
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).bustype) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_input_devids),
            "::",
            stringify!(bustype)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).vendor) as usize - ptr as usize },
        2usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_input_devids),
            "::",
            stringify!(vendor)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).product) as usize - ptr as usize },
        4usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_input_devids),
            "::",
            stringify!(product)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).version) as usize - ptr as usize },
        6usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_input_devids),
            "::",
            stringify!(version)
        )
    );
}
#[repr(C)]
#[derive(Copy, Clone)]
pub struct virtio_input_config {
    pub select: __u8,
    pub subsel: __u8,
    pub size: __u8,
    pub reserved: [__u8; 5usize],
    pub u: virtio_input_config__bindgen_ty_1,
}
#[repr(C)]
#[derive(Copy, Clone)]
pub union virtio_input_config__bindgen_ty_1 {
    pub string: [::std::os::raw::c_char; 128usize],
    pub bitmap: [__u8; 128usize],
    pub abs: virtio_input_absinfo,
    pub ids: virtio_input_devids,
}
#[test]
fn bindgen_test_layout_virtio_input_config__bindgen_ty_1() {
    const UNINIT: ::std::mem::MaybeUninit<virtio_input_config__bindgen_ty_1> =
        ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
        ::std::mem::size_of::<virtio_input_config__bindgen_ty_1>(),
        128usize,
        concat!("Size of: ", stringify!(virtio_input_config__bindgen_ty_1))
    );
    assert_eq!(
        ::std::mem::align_of::<virtio_input_config__bindgen_ty_1>(),
        4usize,
        concat!(
            "Alignment of ",
            stringify!(virtio_input_config__bindgen_ty_1)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).string) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_input_config__bindgen_ty_1),
            "::",
            stringify!(string)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).bitmap) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_input_config__bindgen_ty_1),
            "::",
            stringify!(bitmap)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).abs) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_input_config__bindgen_ty_1),
            "::",
            stringify!(abs)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).ids) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_input_config__bindgen_ty_1),
            "::",
            stringify!(ids)
        )
    );
}
impl Default for virtio_input_config__bindgen_ty_1 {
    fn default() -> Self {
        let mut s = ::std::mem::MaybeUninit::<Self>::uninit();
        unsafe {
            ::std::ptr::write_bytes(s.as_mut_ptr(), 0, 1);
            s.assume_init()
        }
    }
}
#[test]
fn bindgen_test_layout_virtio_input_config() {
    const UNINIT: ::std::mem::MaybeUninit<virtio_input_config> = ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
        ::std::mem::size_of::<virtio_input_config>(),
        136usize,
        concat!("Size of: ", stringify!(virtio_input_config))
    );
    assert_eq!(
        ::std::mem::align_of::<virtio_input_config>(),
        4usize,
        concat!("Alignment of ", stringify!(virtio_input_config))
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).select) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_input_config),
            "::",
            stringify!(select)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).subsel) as usize - ptr as usize },
        1usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_input_config),
            "::",
            stringify!(subsel)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).size) as usize - ptr as usize },
        2usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_input_config),
            "::",
            stringify!(size)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).reserved) as usize - ptr as usize },
        3usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_input_config),
            "::",
            stringify!(reserved)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).u) as usize - ptr as usize },
        8usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_input_config),
            "::",
            stringify!(u)
        )
    );
}
impl Default for virtio_input_config {
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
pub struct virtio_input_event {
    pub type_: __le16,
    pub code: __le16,
    pub value: __le32,
}
#[test]
fn bindgen_test_layout_virtio_input_event() {
    const UNINIT: ::std::mem::MaybeUninit<virtio_input_event> = ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
        ::std::mem::size_of::<virtio_input_event>(),
        8usize,
        concat!("Size of: ", stringify!(virtio_input_event))
    );
    assert_eq!(
        ::std::mem::align_of::<virtio_input_event>(),
        4usize,
        concat!("Alignment of ", stringify!(virtio_input_event))
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).type_) as usize - ptr as usize },
        0usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_input_event),
            "::",
            stringify!(type_)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).code) as usize - ptr as usize },
        2usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_input_event),
            "::",
            stringify!(code)
        )
    );
    assert_eq!(
        unsafe { ::std::ptr::addr_of!((*ptr).value) as usize - ptr as usize },
        4usize,
        concat!(
            "Offset of field: ",
            stringify!(virtio_input_event),
            "::",
            stringify!(value)
        )
    );
}
