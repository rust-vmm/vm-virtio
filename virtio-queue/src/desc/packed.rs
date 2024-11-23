//! packed descriptor
use virtio_bindings::bindings::virtio_ring::{
    VRING_DESC_F_INDIRECT, VRING_DESC_F_NEXT, VRING_DESC_F_WRITE,
};
use vm_memory::{ByteValued, GuestAddress, Le16, Le32, Le64};

/// A virtio packed descriptor constraints with C representation.
#[repr(C)]
#[derive(Default, Clone, Copy, Debug)]
pub struct Descriptor {
    /// Guest physical address of device specific data.
    addr: Le64,
    /// Length of device specific data.
    len: Le32,
    /// Index of descriptor in the descriptor table.
    id: Le16,
    /// Includes next, write, and indirect bits.
    flags: Le16,
}

#[allow(clippy::len_without_is_empty)]
impl Descriptor {
    /// Return the guest physical address of the descriptor buffer.
    pub fn addr(&self) -> GuestAddress {
        GuestAddress(self.addr.into())
    }

    /// Return the length of the descriptor buffer.
    pub fn len(&self) -> u32 {
        self.len.into()
    }

    /// Return the flags for this descriptor, including next, write and indirect bits.
    pub fn flags(&self) -> u16 {
        self.flags.into()
    }

    /// Return the index of the descriptor in the descriptor table.
    pub fn id(&self) -> u16 {
        self.id.into()
    }

    /// Check whether this descriptor refers to a buffer containing an indirect descriptor table.
    pub fn refers_to_indirect_table(&self) -> bool {
        self.flags() & VRING_DESC_F_INDIRECT as u16 != 0
    }

    /// Check whether the `VIRTQ_DESC_F_NEXT` is set for the descriptor.
    pub fn has_next(&self) -> bool {
        self.flags() & VRING_DESC_F_NEXT as u16 != 0
    }

    /// Check if the driver designated this as a write only descriptor.
    ///
    /// If this is false, this descriptor is read only.
    /// Write only means the the emulated device can write and the driver can read.
    pub fn is_write_only(&self) -> bool {
        self.flags() & VRING_DESC_F_WRITE as u16 != 0
    }
}

impl Descriptor {
    /// Create a new descriptor.
    ///
    /// # Arguments
    /// * `addr` - the guest physical address of the descriptor buffer.
    /// * `len` - the length of the descriptor buffer.
    /// * `flags` - the `flags` for the descriptor.
    /// * `next` - the `next` field of the descriptor.
    pub fn new(addr: u64, len: u32, id: u16, flags: u16) -> Self {
        Descriptor {
            addr: addr.into(),
            len: len.into(),
            id: id.into(),
            flags: flags.into(),
        }
    }

    /// Set the guest physical address of the descriptor buffer.
    pub fn set_addr(&mut self, addr: u64) {
        self.addr = addr.into();
    }

    /// Set the length of the descriptor buffer.
    pub fn set_len(&mut self, len: u32) {
        self.len = len.into();
    }

    /// Set the flags for this descriptor.
    pub fn set_flags(&mut self, flags: u16) {
        self.flags = flags.into();
    }

    /// Set the value stored in the `next` field of the descriptor.
    pub fn set_id(&mut self, id: u16) {
        self.id = id.into();
    }
}

// SAFETY: This is safe because `Descriptor` contains only wrappers over POD types and
// all accesses through safe `vm-memory` API will validate any garbage that could be
// included in there.
unsafe impl ByteValued for Descriptor {}

/// A packed descriptor event constraints with C representation.
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct PackedDescEvent {
    off_wrap: Le16,
    flags: Le16,
}

impl PackedDescEvent {
    /// Create a new `VirtqUsedElem` instance.
    ///
    /// # Arguments
    /// * `id` - the index of the used descriptor chain.
    /// * `len` - the total length of the descriptor chain which was used (written to).
    #[allow(unused)]
    pub(crate) fn new(off_wrap: u16, flags: u16) -> Self {
        PackedDescEvent {
            off_wrap: off_wrap.into(),
            flags: flags.into(),
        }
    }
}

// SAFETY: This is safe because `PackedDescEvent` contains only wrappers over POD types and
// all accesses through safe `vm-memory` API will validate any garbage that could be
// included in there.
unsafe impl ByteValued for PackedDescEvent {}

#[cfg(test)]
mod tests {
    use super::*;
    use memoffset::offset_of;
    use std::mem::{align_of, size_of};

    #[test]
    fn test_descriptor_offset() {
        assert_eq!(size_of::<Descriptor>(), 16);
        assert_eq!(offset_of!(Descriptor, addr), 0);
        assert_eq!(offset_of!(Descriptor, len), 8);
        assert_eq!(offset_of!(Descriptor, id), 12);
        assert_eq!(offset_of!(Descriptor, flags), 14);
        assert!(align_of::<Descriptor>() <= 16);
    }

    #[test]
    fn test_descriptor_getter_setter() {
        let mut desc = Descriptor::new(0, 0, 0, 0);

        desc.set_addr(0x1000);
        assert_eq!(desc.addr(), GuestAddress(0x1000));
        desc.set_len(0x2000);
        assert_eq!(desc.len(), 0x2000);
        desc.set_flags(VRING_DESC_F_NEXT as u16);
        assert_eq!(desc.flags(), VRING_DESC_F_NEXT as u16);
        assert!(desc.has_next());
        assert!(!desc.is_write_only());
        assert!(!desc.refers_to_indirect_table());
        desc.set_flags(VRING_DESC_F_WRITE as u16);
        assert_eq!(desc.flags(), VRING_DESC_F_WRITE as u16);
        assert!(!desc.has_next());
        assert!(desc.is_write_only());
        assert!(!desc.refers_to_indirect_table());
        desc.set_flags(VRING_DESC_F_INDIRECT as u16);
        assert_eq!(desc.flags(), VRING_DESC_F_INDIRECT as u16);
        assert!(!desc.is_write_only());
        assert!(desc.refers_to_indirect_table());
        desc.set_id(1);
        assert_eq!(desc.id(), 1);
    }

    #[test]
    fn test_descriptor_copy() {
        let e1 = Descriptor::new(1, 2, 0, 3);
        let mut e2 = Descriptor::default();

        e2.as_mut_slice().copy_from_slice(e1.as_slice());
        assert_eq!(e1.addr(), e2.addr());
        assert_eq!(e1.len(), e2.len());
        assert_eq!(e1.id(), e2.id());
        assert_eq!(e1.flags(), e2.flags());
    }

    #[test]
    fn test_packed_desc_event_offset() {
        assert_eq!(offset_of!(PackedDescEvent, off_wrap), 0);
        assert_eq!(offset_of!(PackedDescEvent, flags), 2);
        assert_eq!(size_of::<PackedDescEvent>(), 4);
    }

    #[test]
    fn test_packed_desc_event_copy() {
        let e1 = PackedDescEvent::new(1, 2);
        let mut e2 = PackedDescEvent::new(0, 0);

        e2.as_mut_slice().copy_from_slice(e1.as_slice());
        assert_eq!(e1.off_wrap, e2.off_wrap);
        assert_eq!(e1.flags, e2.flags);
    }
}
