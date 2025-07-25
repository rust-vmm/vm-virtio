// SPDX-License-Identifier: Apache-2.0 AND BSD-3-Clause
use std::mem::ManuallyDrop;
use std::num::Wrapping;

use vm_memory::{AtomicAccess, GuestMemoryError, GuestMemoryRegion, MemoryRegionAddress};

use std::io::{Read, Write};
use std::mem::MaybeUninit;
use std::num::NonZero;
use vm_memory::ByteValued;

use super::*;

pub struct StubRegion {
    buffer: *mut u8,
    region_len: usize,
    region_start: GuestAddress,
}

impl StubRegion {
    pub fn new(buf_ptr: *mut u8, buf_len: usize, start_offset: u64) -> Self {
        // Allocate the buffer and leak it to get a stable pointer.
        Self {
            buffer: buf_ptr,
            region_len: buf_len,
            region_start: GuestAddress(start_offset),
        }
    }

    fn to_region_addr(&self, addr: GuestAddress) -> Option<MemoryRegionAddress> {
        let offset = addr
            .raw_value()
            .checked_sub(self.region_start.raw_value())?;
        if offset < self.region_len as u64 {
            Some(MemoryRegionAddress(offset))
        } else {
            None
        }
    }

    fn checked_offset(
        &self,
        addr: MemoryRegionAddress,
        count: usize,
    ) -> Option<MemoryRegionAddress> {
        let end = addr.0.checked_add(count as u64)?;
        if end <= self.region_len as u64 {
            Some(MemoryRegionAddress(end))
        } else {
            None
        }
    }
}

impl GuestMemoryRegion for StubRegion {
    type B = ();

    fn len(&self) -> <GuestAddress as vm_memory::AddressValue>::V {
        self.region_len.try_into().unwrap()
    }

    fn start_addr(&self) -> GuestAddress {
        self.region_start
    }

    fn bitmap(&self) -> &Self::B {
        // For Kani, we do not need a bitmap, so we return an empty tuple.
        &()
    }
}

impl Bytes<MemoryRegionAddress> for StubRegion {
    type E = GuestMemoryError;

    fn write(&self, buf: &[u8], addr: MemoryRegionAddress) -> Result<usize, Self::E> {
        let offset = addr.0 as usize;
        let end = offset
            .checked_add(buf.len())
            .ok_or(GuestMemoryError::InvalidGuestAddress(GuestAddress(addr.0)))?;
        if end > self.region_len as usize {
            return Err(GuestMemoryError::InvalidGuestAddress(GuestAddress(addr.0)));
        }
        unsafe {
            std::ptr::copy_nonoverlapping(buf.as_ptr(), self.buffer.add(offset), buf.len());
        }
        Ok(buf.len())
    }

    fn read(&self, buf: &mut [u8], addr: MemoryRegionAddress) -> Result<usize, Self::E> {
        let offset = addr.0 as usize;
        let end = offset
            .checked_add(buf.len())
            .ok_or(GuestMemoryError::InvalidGuestAddress(GuestAddress(addr.0)))?;
        if end > self.region_len as usize {
            return Err(GuestMemoryError::InvalidGuestAddress(GuestAddress(addr.0)));
        }
        unsafe {
            std::ptr::copy_nonoverlapping(self.buffer.add(offset), buf.as_mut_ptr(), buf.len());
        }
        Ok(buf.len())
    }

    fn write_slice(&self, buf: &[u8], addr: MemoryRegionAddress) -> Result<(), Self::E> {
        self.write(buf, addr).map(|_| ())
    }

    fn read_slice(&self, buf: &mut [u8], addr: MemoryRegionAddress) -> Result<(), Self::E> {
        self.read(buf, addr).map(|_| ())
    }

    fn read_from<F: Read>(
        &self,
        addr: MemoryRegionAddress,
        src: &mut F,
        count: usize,
    ) -> Result<usize, Self::E> {
        let mut temp = vec![0u8; count];
        src.read_exact(&mut temp)
            .map_err(|_| GuestMemoryError::PartialBuffer {
                expected: count,
                completed: 0,
            })?;
        self.write(&temp, addr)
    }

    fn read_exact_from<F: Read>(
        &self,
        addr: MemoryRegionAddress,
        src: &mut F,
        count: usize,
    ) -> Result<(), Self::E> {
        let mut temp = vec![0u8; count];
        src.read_exact(&mut temp)
            .map_err(|_| GuestMemoryError::PartialBuffer {
                expected: count,
                completed: 0,
            })?;
        self.write_slice(&temp, addr)
    }

    fn read_obj<T: ByteValued>(&self, addr: MemoryRegionAddress) -> Result<T, Self::E> {
        let size = std::mem::size_of::<T>();
        let offset = addr.0 as usize;
        let end = offset
            .checked_add(size)
            .ok_or(GuestMemoryError::InvalidGuestAddress(GuestAddress(addr.0)))?;
        if end > self.region_len as usize {
            return Err(GuestMemoryError::InvalidGuestAddress(GuestAddress(addr.0)));
        }
        let mut result: T = unsafe { MaybeUninit::<T>::zeroed().assume_init() };
        unsafe {
            std::ptr::copy_nonoverlapping(
                self.buffer.add(offset),
                (&mut result as *mut T) as *mut u8,
                size,
            );
        }
        Ok(result)
    }

    fn write_to<F: Write>(
        &self,
        addr: MemoryRegionAddress,
        dst: &mut F,
        count: usize,
    ) -> Result<usize, Self::E> {
        let offset = addr.0 as usize;
        let end = offset
            .checked_add(count)
            .ok_or(GuestMemoryError::InvalidGuestAddress(GuestAddress(addr.0)))?;
        if end > self.region_len as usize {
            return Err(GuestMemoryError::InvalidGuestAddress(GuestAddress(addr.0)));
        }
        unsafe {
            let slice = std::slice::from_raw_parts(self.buffer.add(offset), count);
            dst.write_all(slice)
                .map_err(|_| GuestMemoryError::PartialBuffer {
                    expected: count,
                    completed: 0,
                })?;
        }
        Ok(count)
    }

    fn write_obj<T: ByteValued>(&self, val: T, addr: MemoryRegionAddress) -> Result<(), Self::E> {
        let size = std::mem::size_of::<T>();
        let offset = addr.0 as usize;
        let end = offset
            .checked_add(size)
            .ok_or(GuestMemoryError::InvalidGuestAddress(GuestAddress(addr.0)))?;
        if end > self.region_len as usize {
            return Err(GuestMemoryError::InvalidGuestAddress(GuestAddress(addr.0)));
        }
        let bytes = val.as_slice();
        unsafe {
            std::ptr::copy_nonoverlapping(bytes.as_ptr(), self.buffer.add(offset), size);
        }
        Ok(())
    }

    fn write_all_to<F: Write>(
        &self,
        addr: MemoryRegionAddress,
        dst: &mut F,
        count: usize,
    ) -> Result<(), Self::E> {
        self.write_to(addr, dst, count).map(|_| ())
    }

    fn store<T: AtomicAccess>(
        &self,
        val: T,
        addr: MemoryRegionAddress,
        _order: Ordering,
    ) -> Result<(), Self::E> {
        let size = std::mem::size_of::<T>();
        let offset = addr.0 as usize;
        let end = offset
            .checked_add(size)
            .ok_or(GuestMemoryError::InvalidGuestAddress(GuestAddress(addr.0)))?;
        if end > self.region_len as usize {
            return Err(GuestMemoryError::InvalidGuestAddress(GuestAddress(addr.0)));
        }
        let bytes = val.as_slice();
        unsafe {
            std::ptr::copy_nonoverlapping(bytes.as_ptr(), self.buffer.add(offset), size);
        }
        Ok(())
    }

    fn load<T: AtomicAccess>(
        &self,
        addr: MemoryRegionAddress,
        _order: Ordering,
    ) -> Result<T, Self::E> {
        let size = std::mem::size_of::<T>();
        let offset = addr.0 as usize;
        let end = offset
            .checked_add(size)
            .ok_or(GuestMemoryError::InvalidGuestAddress(GuestAddress(addr.0)))?;
        if end > self.region_len as usize {
            return Err(GuestMemoryError::InvalidGuestAddress(GuestAddress(addr.0)));
        }
        unsafe {
            let slice = std::slice::from_raw_parts(self.buffer.add(offset), size);
            T::from_slice(slice)
                .ok_or_else(|| GuestMemoryError::InvalidGuestAddress(GuestAddress(addr.0)))
                .copied()
        }
    }
}

/// A made-for-kani version of `vm_memory::GuestMemoryMmap`. Unlike the real
/// `GuestMemoryMmap`, which manages a list of regions and then does a binary
/// search to determine which region a specific read or write request goes to,
/// this only uses a single region. Eliminating this binary search significantly
/// speeds up all queue proofs, because it eliminates the only loop contained herein,
/// meaning we can use `kani::unwind(0)` instead of `kani::unwind(2)`. Functionally,
/// it works identically to `GuestMemoryMmap` with only a single contained region.
pub struct SingleRegionGuestMemory {
    the_region: StubRegion,
}

impl GuestMemory for SingleRegionGuestMemory {
    type R = StubRegion;

    fn num_regions(&self) -> usize {
        1
    }

    fn find_region(&self, addr: GuestAddress) -> Option<&Self::R> {
        self.the_region
            .to_region_addr(addr)
            .map(|_| &self.the_region)
    }

    fn iter(&self) -> impl Iterator<Item = &Self::R> {
        std::iter::once(&self.the_region)
    }

    fn try_access<F>(
        &self,
        count: usize,
        addr: GuestAddress,
        mut f: F,
    ) -> vm_memory::guest_memory::Result<usize>
    where
        F: FnMut(
            usize,
            usize,
            MemoryRegionAddress,
            &Self::R,
        ) -> vm_memory::guest_memory::Result<usize>,
    {
        // We only have a single region, meaning a lot of the complications of the default
        // try_access implementation for dealing with reads/writes across multiple
        // regions does not apply.
        let region_addr = self
            .the_region
            .to_region_addr(addr)
            .ok_or(vm_memory::guest_memory::Error::InvalidGuestAddress(addr))?;
        self.the_region
            .checked_offset(region_addr, count)
            .ok_or(vm_memory::guest_memory::Error::InvalidGuestAddress(addr))?;
        f(0, count, region_addr, &self.the_region)
    }
}

impl kani::Arbitrary for SingleRegionGuestMemory {
    fn any() -> Self {
        guest_memory(
            ManuallyDrop::new(kani::vec::exact_vec::<u8, GUEST_MEMORY_SIZE>()).as_mut_ptr(),
            GUEST_MEMORY_SIZE,
            GUEST_MEMORY_BASE,
        )
    }
}
pub struct ProofContext {
    pub queue: Queue,
    pub memory: SingleRegionGuestMemory,
}

/// We start the first guest memory region at an offset so that harnesses using
/// Queue::any() will be exposed to queue segments both before and after valid guest memory.
/// This is conforming to MockSplitQueue::new() that uses `0` as starting address of the
/// virtqueue. Also, QUEUE_END is the size only if GUEST_MEMORY_BASE is `0`
const GUEST_MEMORY_BASE: u64 = 0;

// We size our guest memory to fit a properly aligned queue, plus some wiggles bytes
// to make sure we not only test queues where all segments are consecutively aligned.
// We need to give at least 16 bytes of buffer space for the descriptor table to be
// able to change its address, as it is 16-byte aligned.
const GUEST_MEMORY_SIZE: usize = QUEUE_END as usize + 30;

fn guest_memory(memory: *mut u8, size: usize, start: u64) -> SingleRegionGuestMemory {
    // // Ideally, we'd want to do
    // // let region = unsafe {MmapRegionBuilder::new(GUEST_MEMORY_SIZE)
    // //    .with_raw_mmap_pointer(bytes.as_mut_ptr())
    // //    .build()
    // //    .unwrap()};
    // // However, .build() calls to .build_raw(), which contains a call to libc::sysconf.
    // // Since kani 0.34.0, stubbing out foreign functions is supported, but due to the rust
    // // standard library using a special version of the libc crate, it runs into some problems
    // // [1] Even if we work around those problems, we run into performance problems [2].
    // // Therefore, for now we stick to this ugly transmute hack (which only works because
    // // the kani compiler will never re-order fields, so we can treat repr(Rust) as repr(C)).
    // //
    // // [1]: https://github.com/model-checking/kani/issues/2673
    // // [2]: https://github.com/model-checking/kani/issues/2538
    // let region_stub = MmapRegionStub {
    //     addr: memory,
    //     size: size,
    //     start: start,
    //     _bitmap: Default::default(),
    //     _file_offset: None,
    //     _prot: 0,
    //     _flags: libc::MAP_ANONYMOUS | libc::MAP_PRIVATE,
    //     _owned: false,
    //     _hugetlbfs: None,
    // };

    //let region: MmapRegion<()> = unsafe { std::mem::transmute(region_stub) };

    let guest_region = StubRegion::new(memory, size, start);

    // Use a single memory region for guests of size < 2GB
    SingleRegionGuestMemory {
        the_region: guest_region,
    }
}

const MAX_QUEUE_SIZE: u16 = 4;

// Constants describing the in-memory layout of a queue of size MAX_QUEUE_SIZE starting
// at the beginning of guest memory. These are based on Section 2.7 of the VirtIO 1.2
// specification.
const QUEUE_BASE_ADDRESS: u64 = GUEST_MEMORY_BASE;

/// descriptor table has 16 bytes per entry, avail ring starts right after
const MAX_START_AVAIL_RING_BASE_ADDRESS: u64 = QUEUE_BASE_ADDRESS + MAX_QUEUE_SIZE as u64 * 16;

/// Used ring starts after avail ring (which has size 6 + 2 * MAX_QUEUE_SIZE),
/// and needs 2 bytes of padding
const MAX_START_USED_RING_BASE_ADDRESS: u64 =
    MAX_START_AVAIL_RING_BASE_ADDRESS + 6 + 2 * MAX_QUEUE_SIZE as u64 + 2;

/// The address of the first byte after the queue. Since our queue starts at guest physical
/// address 0, this is also the size of the memory area occupied by the queue.
/// Note that the used ring structure has size 6 + 8 * MAX_QUEUE_SIZE
const QUEUE_END: u64 = MAX_START_USED_RING_BASE_ADDRESS + 6 + 8 * MAX_QUEUE_SIZE as u64;

impl kani::Arbitrary for ProofContext {
    fn any() -> Self {
        // descriptor table has 16 bytes per entry, avail ring starts right after
        let desc_tbl_queue_size = kani::any::<u16>();
        // Alignment of the descriptor table is 16 bytes as per the VirtIO spec.
        // See https://docs.oasis-open.org/virtio/virtio/v1.0/cs04/virtio-v1.0-cs04.pdf
        kani::assume(
            desc_tbl_queue_size <= 16 * MAX_QUEUE_SIZE && (desc_tbl_queue_size & 0xF == 0),
        );
        let avail_ring_base_address: u64 = QUEUE_BASE_ADDRESS + desc_tbl_queue_size as u64;

        // Used ring starts after avail ring (which has max size 6 + 2 * MAX_QUEUE_SIZE),
        // and needs 2 bytes of padding
        let avail_ring_queue_size = kani::any::<u16>();
        // Alignment of the available ring is 2 bytes as per the VirtIO spec.
        // See https://docs.oasis-open.org/virtio/virtio/v1.0/cs04/virtio-v1.0-cs04.pdf
        kani::assume(
            avail_ring_queue_size <= 6 + 2 * MAX_QUEUE_SIZE + 2
                && (avail_ring_queue_size & 0x1 == 0),
        );
        let used_ring_base_address: u64 = avail_ring_base_address + avail_ring_queue_size as u64;

        // The address of the first byte after the queue. Since our queue starts at guest physical
        // address 0, this is also the size of the memory area occupied by the queue.
        // Note that the used ring structure has max size 6 + 8 * MAX_QUEUE_SIZE
        let used_ring_queue_size = kani::any::<u16>();
        // Alignment of the used ring is 4 bytes as per the VirtIO spec.
        // See https://docs.oasis-open.org/virtio/virtio/v1.0/cs04/virtio-v1.0-cs04.pdf
        kani::assume(
            avail_ring_queue_size <= 6 + 8 * MAX_QUEUE_SIZE && (used_ring_queue_size & 0x3 == 0),
        );

        // The size of the queue data structures should fill the available space
        kani::assume(QUEUE_END == used_ring_base_address + used_ring_queue_size as u64);

        let mem = SingleRegionGuestMemory::any();

        let mut queue = Queue::new(MAX_QUEUE_SIZE).unwrap();

        queue.ready = true;

        queue.set_desc_table_address(
            Some(QUEUE_BASE_ADDRESS as u32),
            Some((QUEUE_BASE_ADDRESS >> 32) as u32),
        );

        queue.set_avail_ring_address(
            Some(avail_ring_base_address as u32),
            Some((avail_ring_base_address >> 32) as u32),
        );

        queue.set_used_ring_address(
            Some(used_ring_base_address as u32),
            Some((used_ring_base_address >> 32) as u32),
        );

        queue.set_next_avail(kani::any());
        queue.set_next_used(kani::any());
        queue.set_event_idx(kani::any());
        queue.num_added = Wrapping(kani::any());

        kani::assume(queue.is_valid(&mem));

        ProofContext { queue, memory: mem }
    }
}

#[kani::proof]
// There are no loops anywhere, but kani really enjoys getting stuck in std::ptr::drop_in_place.
// This is a compiler intrinsic that has a "dummy" implementation in stdlib that just
// recursively calls itself. Kani will generally unwind this recursion infinitely.
#[kani::unwind(0)]
fn verify_spec_2_7_7_2() {
    // Section 2.7.7.2 deals with device-to-driver notification suppression.
    // It describes a mechanism by which the driver can tell the device that it does not
    // want notifications (IRQs) about the device finishing processing individual buffers
    // (descriptor chain heads) from the avail ring until a specific number of descriptors
    // has been processed. This is done by the driver
    // defining a "used_event" index, which tells the device "please do not notify me until
    // used.ring[used_event] has been written to by you".
    let ProofContext {
        mut queue,
        memory: mem,
    } = kani::any();

    let num_added_old = queue.num_added.0;
    let needs_notification = queue.needs_notification(&mem);

    // event_idx_enabled equivalent to VIRTIO_F_EVENT_IDX negotiated
    if !queue.event_idx_enabled {
        // The specification here says
        // After the device writes a descriptor index into the used ring:
        // – If flags is 1, the device SHOULD NOT send a notification.
        // – If flags is 0, the device MUST send a notification
        // flags is the first field in the avail_ring_address, which we completely ignore. We
        // always send a notification, and as there only is a SHOULD NOT, that is okay
        assert!(needs_notification.unwrap());
    } else {
        // next_used - 1 is where the previous descriptor was placed
        if Wrapping(queue.used_event(&mem, Ordering::Relaxed).unwrap())
            == std::num::Wrapping(queue.next_used - Wrapping(1))
            && num_added_old > 0
        {
            // If the idx field in the used ring (which determined where that descriptor index
            // was placed) was equal to used_event, the device MUST send a
            // notification.
            assert!(needs_notification.unwrap());

            kani::cover!();
        }

        // The other case is handled by a "SHOULD NOT send a notification" in the spec.
        // So we do not care
    }

    #[kani::proof]
    #[kani::unwind(0)]
    fn verify_add_used() {
        let ProofContext { mut queue, memory } = kani::any();
        let used_idx = queue.next_used;
        kani::assume(used_idx.0 < queue.size());
        let used_desc_table_index = kani::any();
        if queue
            .add_used(&memory, used_desc_table_index, kani::any())
            .is_ok()
        {
            assert_eq!(queue.next_used, used_idx + Wrapping(1));
        } else {
            assert_eq!(queue.next_used, used_idx);

            // Ideally, here we would want to actually read the relevant values from memory and
            // assert they are unchanged. However, kani will run out of memory if we try to do so,
            // so we instead verify the following "proxy property": If an error happened, then
            // it happened at the very beginning of add_used, meaning no memory accesses were
            // done. This is relying on implementation details of add_used, namely that
            // the check for out-of-bounds descriptor index happens at the very beginning of the
            // function.
            assert!(used_desc_table_index >= queue.size());
        }
    }

    #[kani::proof]
    #[kani::unwind(0)]
    fn verify_used_ring_avail_event() {
        let ProofContext {
            mut queue,
            memory: _,
        } = kani::any();
        let x = kani::any();
        queue.set_next_used(x);
        assert_eq!(x, queue.next_used.0);
    }

    #[kani::proof]
    #[kani::unwind(0)]
    // Driver writes to the avail_ring idx field
    fn verify_enable_notification() {
        let ProofContext { mut queue, memory } = kani::any();

        // The enable_notification method sets notification to true and returns
        //   - true, if there are pending entries in the `idx` field of the
        //     avail ring
        //   - false, if there are no pending entries in the `idx` field of the
        // avail ring The check for pending entries is done by comparing the
        // current `avail_idx` with the `next_avail` field of the queue. If they
        // are different, there are pending entries, otherwise there are no
        // pending entries. The equality check is a consequence of the
        // monotonicity property of `idx` (2.7.6.1) that it cannot be decreased
        // by the driver.
        if queue.enable_notification(&memory).unwrap() {
            assert_ne!(
                queue.avail_idx(&memory, Ordering::Relaxed).unwrap(),
                queue.next_avail
            );
        } else {
            assert_eq!(
                queue.avail_idx(&memory, Ordering::Relaxed).unwrap(),
                queue.next_avail
            );
        }
    }
}
