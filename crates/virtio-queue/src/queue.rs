// Copyright 2022 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// Copyright (C) 2020-2021 Alibaba Cloud. All rights reserved.
// Copyright © 2019 Intel Corporation.
// Portions Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// SPDX-License-Identifier: Apache-2.0 AND BSD-3-Clause

use std::mem::size_of;
use std::num::Wrapping;
use std::ops::Deref;
use std::sync::atomic::{fence, Ordering};

use vm_memory::{Address, Bytes, GuestAddress, GuestMemory};

use crate::defs::{
    DEFAULT_AVAIL_RING_ADDR, DEFAULT_DESC_TABLE_ADDR, DEFAULT_USED_RING_ADDR,
    VIRTQ_AVAIL_ELEMENT_SIZE, VIRTQ_AVAIL_RING_HEADER_SIZE, VIRTQ_AVAIL_RING_META_SIZE,
    VIRTQ_USED_ELEMENT_SIZE, VIRTQ_USED_RING_HEADER_SIZE, VIRTQ_USED_RING_META_SIZE,
};
use crate::{
    error, Descriptor, DescriptorChain, Error, QueueGuard, QueueOwnedT, QueueState, QueueT,
    VirtqUsedElem,
};
use virtio_bindings::bindings::virtio_ring::VRING_USED_F_NO_NOTIFY;

/// The maximum queue size as defined in the Virtio Spec.
pub const MAX_QUEUE_SIZE: u16 = 32768;

/// Struct to maintain information and manipulate a virtio queue.
///
/// # Example
///
/// ```rust
/// use virtio_queue::{Queue, QueueOwnedT, QueueT};
/// use vm_memory::{Bytes, GuestAddress, GuestAddressSpace, GuestMemoryMmap};
///
/// let m = GuestMemoryMmap::<()>::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap();
/// let mut queue = Queue::new(1024).unwrap();
///
/// // First, the driver sets up the queue; this set up is done via writes on the bus (PCI, MMIO).
/// queue.set_size(8);
/// queue.set_desc_table_address(Some(0x1000), None);
/// queue.set_avail_ring_address(Some(0x2000), None);
/// queue.set_used_ring_address(Some(0x3000), None);
/// queue.set_event_idx(true);
/// queue.set_ready(true);
/// // The user should check if the queue is valid before starting to use it.
/// assert!(queue.is_valid(&m));
///
/// // Here the driver would add entries in the available ring and then update the `idx` field of
/// // the available ring (address = 0x2000 + 2).
/// m.write_obj(3, GuestAddress(0x2002));
///
/// loop {
///     queue.disable_notification(&m).unwrap();
///
///     // Consume entries from the available ring.
///     while let Some(chain) = queue.iter(&m).unwrap().next() {
///         // Process the descriptor chain, and then add an entry in the used ring and optionally
///         // notify the driver.
///         queue.add_used(&m, chain.head_index(), 0x100).unwrap();
///
///         if queue.needs_notification(&m).unwrap() {
///             // Here we would notify the driver it has new entries in the used ring to consume.
///         }
///     }
///     if !queue.enable_notification(&m).unwrap() {
///         break;
///     }
/// }
///
/// // We can reset the queue at some point.
/// queue.reset();
/// // The queue should not be ready after reset.
/// assert!(!queue.ready());
/// ```
#[derive(Debug, Default, PartialEq, Eq)]
pub struct Queue {
    /// The maximum size in elements offered by the device.
    max_size: u16,

    /// Tail position of the available ring.
    next_avail: Wrapping<u16>,

    /// Head position of the used ring.
    next_used: Wrapping<u16>,

    /// VIRTIO_F_RING_EVENT_IDX negotiated.
    event_idx_enabled: bool,

    /// The number of descriptor chains placed in the used ring via `add_used`
    /// since the last time `needs_notification` was called on the associated queue.
    num_added: Wrapping<u16>,

    /// The queue size in elements the driver selected.
    size: u16,

    /// Indicates if the queue is finished with configuration.
    ready: bool,

    /// Guest physical address of the descriptor table.
    desc_table: GuestAddress,

    /// Guest physical address of the available ring.
    avail_ring: GuestAddress,

    /// Guest physical address of the used ring.
    used_ring: GuestAddress,
}

impl Queue {
    /// Equivalent of [`QueueT::set_size`] returning an error in case of invalid size.
    ///
    /// This should not be directly used, as the preferred method is part of the [`QueueT`]
    /// interface. This is a convenience function for implementing save/restore capabilities.
    pub fn try_set_size(&mut self, size: u16) -> Result<(), Error> {
        if size > self.max_size() || size == 0 || (size & (size - 1)) != 0 {
            return Err(Error::InvalidSize);
        }
        self.size = size;
        Ok(())
    }

    /// Tries to set the descriptor table address. In case of an invalid value, the address is
    /// not updated.
    ///
    /// This should not be directly used, as the preferred method is
    /// [`QueueT::set_desc_table_address`]. This is a convenience function for implementing
    /// save/restore capabilities.
    pub fn try_set_desc_table_address(&mut self, desc_table: GuestAddress) -> Result<(), Error> {
        if desc_table.mask(0xf) != 0 {
            return Err(Error::InvalidDescTableAlign);
        }
        self.desc_table = desc_table;

        Ok(())
    }

    /// Tries to update the available ring address. In case of an invalid value, the address is
    /// not updated.
    ///
    /// This should not be directly used, as the preferred method is
    /// [`QueueT::set_avail_ring_address`]. This is a convenience function for implementing
    /// save/restore capabilities.
    pub fn try_set_avail_ring_address(&mut self, avail_ring: GuestAddress) -> Result<(), Error> {
        if avail_ring.mask(0x1) != 0 {
            return Err(Error::InvalidAvailRingAlign);
        }
        self.avail_ring = avail_ring;
        Ok(())
    }

    /// Tries to update the used ring address. In cae of an invalid value, the address is not
    /// updated.
    ///
    /// This should not be directly used, as the preferred method is
    /// [`QueueT::set_used_ring_address`]. This is a convenience function for implementing
    /// save/restore capabilities.
    pub fn try_set_used_ring_address(&mut self, used_ring: GuestAddress) -> Result<(), Error> {
        if used_ring.mask(0x3) != 0 {
            return Err(Error::InvalidUsedRingAlign);
        }
        self.used_ring = used_ring;
        Ok(())
    }

    /// Returns the state of the `Queue`.
    ///
    /// This is useful for implementing save/restore capabilities.
    /// The state does not have support for serialization, but this can be
    /// added by VMMs locally through the use of a
    /// [remote type](https://serde.rs/remote-derive.html).
    ///
    /// Alternatively, a version aware and serializable/deserializable QueueState
    /// is available in the `virtio-queue-ser` crate.
    pub fn state(&self) -> QueueState {
        QueueState {
            max_size: self.max_size,
            next_avail: self.next_avail(),
            next_used: self.next_used(),
            event_idx_enabled: self.event_idx_enabled,
            size: self.size,
            ready: self.ready,
            desc_table: self.desc_table(),
            avail_ring: self.avail_ring(),
            used_ring: self.used_ring(),
        }
    }

    // Helper method that writes `val` to the `avail_event` field of the used ring, using
    // the provided ordering.
    fn set_avail_event<M: GuestMemory>(
        &self,
        mem: &M,
        val: u16,
        order: Ordering,
    ) -> Result<(), Error> {
        // This can not overflow an u64 since it is working with relatively small numbers compared
        // to u64::MAX.
        let avail_event_offset =
            VIRTQ_USED_RING_HEADER_SIZE + VIRTQ_USED_ELEMENT_SIZE * u64::from(self.size);
        let addr = self
            .used_ring
            .checked_add(avail_event_offset)
            .ok_or(Error::AddressOverflow)?;

        mem.store(u16::to_le(val), addr, order)
            .map_err(Error::GuestMemory)
    }

    // Set the value of the `flags` field of the used ring, applying the specified ordering.
    fn set_used_flags<M: GuestMemory>(
        &mut self,
        mem: &M,
        val: u16,
        order: Ordering,
    ) -> Result<(), Error> {
        mem.store(u16::to_le(val), self.used_ring, order)
            .map_err(Error::GuestMemory)
    }

    // Write the appropriate values to enable or disable notifications from the driver.
    //
    // Every access in this method uses `Relaxed` ordering because a fence is added by the caller
    // when appropriate.
    fn set_notification<M: GuestMemory>(&mut self, mem: &M, enable: bool) -> Result<(), Error> {
        if enable {
            if self.event_idx_enabled {
                // We call `set_avail_event` using the `next_avail` value, instead of reading
                // and using the current `avail_idx` to avoid missing notifications. More
                // details in `enable_notification`.
                self.set_avail_event(mem, self.next_avail.0, Ordering::Relaxed)
            } else {
                self.set_used_flags(mem, 0, Ordering::Relaxed)
            }
        } else if !self.event_idx_enabled {
            self.set_used_flags(mem, VRING_USED_F_NO_NOTIFY as u16, Ordering::Relaxed)
        } else {
            // Notifications are effectively disabled by default after triggering once when
            // `VIRTIO_F_EVENT_IDX` is negotiated, so we don't do anything in that case.
            Ok(())
        }
    }

    // Return the value present in the used_event field of the avail ring.
    //
    // If the VIRTIO_F_EVENT_IDX feature bit is not negotiated, the flags field in the available
    // ring offers a crude mechanism for the driver to inform the device that it doesn’t want
    // interrupts when buffers are used. Otherwise virtq_avail.used_event is a more performant
    // alternative where the driver specifies how far the device can progress before interrupting.
    //
    // Neither of these interrupt suppression methods are reliable, as they are not synchronized
    // with the device, but they serve as useful optimizations. So we only ensure access to the
    // virtq_avail.used_event is atomic, but do not need to synchronize with other memory accesses.
    fn used_event<M: GuestMemory>(&self, mem: &M, order: Ordering) -> Result<Wrapping<u16>, Error> {
        // This can not overflow an u64 since it is working with relatively small numbers compared
        // to u64::MAX.
        let used_event_offset =
            VIRTQ_AVAIL_RING_HEADER_SIZE + u64::from(self.size) * VIRTQ_AVAIL_ELEMENT_SIZE;
        let used_event_addr = self
            .avail_ring
            .checked_add(used_event_offset)
            .ok_or(Error::AddressOverflow)?;

        mem.load(used_event_addr, order)
            .map(u16::from_le)
            .map(Wrapping)
            .map_err(Error::GuestMemory)
    }
}

impl<'a> QueueGuard<'a> for Queue {
    type G = &'a mut Self;
}

impl QueueT for Queue {
    fn new(max_size: u16) -> Result<Self, Error> {
        // We need to check that the max size is a power of 2 because we're setting this as the
        // queue size, and the valid queue sizes are a power of 2 as per the specification.
        if max_size == 0 || max_size > MAX_QUEUE_SIZE || (max_size & (max_size - 1)) != 0 {
            return Err(Error::InvalidMaxSize);
        }
        Ok(Queue {
            max_size,
            size: max_size,
            ready: false,
            desc_table: GuestAddress(DEFAULT_DESC_TABLE_ADDR),
            avail_ring: GuestAddress(DEFAULT_AVAIL_RING_ADDR),
            used_ring: GuestAddress(DEFAULT_USED_RING_ADDR),
            next_avail: Wrapping(0),
            next_used: Wrapping(0),
            event_idx_enabled: false,
            num_added: Wrapping(0),
        })
    }

    fn is_valid<M: GuestMemory>(&self, mem: &M) -> bool {
        let queue_size = self.size as u64;
        let desc_table = self.desc_table;
        // The multiplication can not overflow an u64 since we are multiplying an u16 with a
        // small number.
        let desc_table_size = size_of::<Descriptor>() as u64 * queue_size;
        let avail_ring = self.avail_ring;
        // The operations below can not overflow an u64 since they're working with relatively small
        // numbers compared to u64::MAX.
        let avail_ring_size = VIRTQ_AVAIL_RING_META_SIZE + VIRTQ_AVAIL_ELEMENT_SIZE * queue_size;
        let used_ring = self.used_ring;
        let used_ring_size = VIRTQ_USED_RING_META_SIZE + VIRTQ_USED_ELEMENT_SIZE * queue_size;

        if !self.ready {
            error!("attempt to use virtio queue that is not marked ready");
            false
        } else if desc_table
            .checked_add(desc_table_size)
            .map_or(true, |v| !mem.address_in_range(v))
        {
            error!(
                "virtio queue descriptor table goes out of bounds: start:0x{:08x} size:0x{:08x}",
                desc_table.raw_value(),
                desc_table_size
            );
            false
        } else if avail_ring
            .checked_add(avail_ring_size)
            .map_or(true, |v| !mem.address_in_range(v))
        {
            error!(
                "virtio queue available ring goes out of bounds: start:0x{:08x} size:0x{:08x}",
                avail_ring.raw_value(),
                avail_ring_size
            );
            false
        } else if used_ring
            .checked_add(used_ring_size)
            .map_or(true, |v| !mem.address_in_range(v))
        {
            error!(
                "virtio queue used ring goes out of bounds: start:0x{:08x} size:0x{:08x}",
                used_ring.raw_value(),
                used_ring_size
            );
            false
        } else {
            true
        }
    }

    fn reset(&mut self) {
        self.ready = false;
        self.size = self.max_size;
        self.desc_table = GuestAddress(DEFAULT_DESC_TABLE_ADDR);
        self.avail_ring = GuestAddress(DEFAULT_AVAIL_RING_ADDR);
        self.used_ring = GuestAddress(DEFAULT_USED_RING_ADDR);
        self.next_avail = Wrapping(0);
        self.next_used = Wrapping(0);
        self.num_added = Wrapping(0);
        self.event_idx_enabled = false;
    }

    fn lock(&mut self) -> <Self as QueueGuard>::G {
        self
    }

    fn max_size(&self) -> u16 {
        self.max_size
    }

    fn size(&self) -> u16 {
        self.size
    }

    fn set_size(&mut self, size: u16) {
        if self.try_set_size(size).is_err() {
            error!("virtio queue with invalid size: {}", size);
        }
    }

    fn ready(&self) -> bool {
        self.ready
    }

    fn set_ready(&mut self, ready: bool) {
        self.ready = ready;
    }

    fn set_desc_table_address(&mut self, low: Option<u32>, high: Option<u32>) {
        let low = low.unwrap_or(self.desc_table.0 as u32) as u64;
        let high = high.unwrap_or((self.desc_table.0 >> 32) as u32) as u64;

        let desc_table = GuestAddress((high << 32) | low);
        if self.try_set_desc_table_address(desc_table).is_err() {
            error!("virtio queue descriptor table breaks alignment constraints");
        }
    }

    fn set_avail_ring_address(&mut self, low: Option<u32>, high: Option<u32>) {
        let low = low.unwrap_or(self.avail_ring.0 as u32) as u64;
        let high = high.unwrap_or((self.avail_ring.0 >> 32) as u32) as u64;

        let avail_ring = GuestAddress((high << 32) | low);
        if self.try_set_avail_ring_address(avail_ring).is_err() {
            error!("virtio queue available ring breaks alignment constraints");
        }
    }

    fn set_used_ring_address(&mut self, low: Option<u32>, high: Option<u32>) {
        let low = low.unwrap_or(self.used_ring.0 as u32) as u64;
        let high = high.unwrap_or((self.used_ring.0 >> 32) as u32) as u64;

        let used_ring = GuestAddress((high << 32) | low);
        if self.try_set_used_ring_address(used_ring).is_err() {
            error!("virtio queue used ring breaks alignment constraints");
        }
    }

    fn set_event_idx(&mut self, enabled: bool) {
        self.event_idx_enabled = enabled;
    }

    fn avail_idx<M>(&self, mem: &M, order: Ordering) -> Result<Wrapping<u16>, Error>
    where
        M: GuestMemory + ?Sized,
    {
        let addr = self
            .avail_ring
            .checked_add(2)
            .ok_or(Error::AddressOverflow)?;

        mem.load(addr, order)
            .map(u16::from_le)
            .map(Wrapping)
            .map_err(Error::GuestMemory)
    }

    fn used_idx<M: GuestMemory>(&self, mem: &M, order: Ordering) -> Result<Wrapping<u16>, Error> {
        let addr = self
            .used_ring
            .checked_add(2)
            .ok_or(Error::AddressOverflow)?;

        mem.load(addr, order)
            .map(u16::from_le)
            .map(Wrapping)
            .map_err(Error::GuestMemory)
    }

    fn add_used<M: GuestMemory>(
        &mut self,
        mem: &M,
        head_index: u16,
        len: u32,
    ) -> Result<(), Error> {
        if head_index >= self.size {
            error!(
                "attempted to add out of bounds descriptor to used ring: {}",
                head_index
            );
            return Err(Error::InvalidDescriptorIndex);
        }

        let next_used_index = u64::from(self.next_used.0 % self.size);
        // This can not overflow an u64 since it is working with relatively small numbers compared
        // to u64::MAX.
        let offset = VIRTQ_USED_RING_HEADER_SIZE + next_used_index * VIRTQ_USED_ELEMENT_SIZE;
        let addr = self
            .used_ring
            .checked_add(offset)
            .ok_or(Error::AddressOverflow)?;
        mem.write_obj(VirtqUsedElem::new(head_index.into(), len), addr)
            .map_err(Error::GuestMemory)?;

        self.next_used += Wrapping(1);
        self.num_added += Wrapping(1);

        mem.store(
            u16::to_le(self.next_used.0),
            self.used_ring
                .checked_add(2)
                .ok_or(Error::AddressOverflow)?,
            Ordering::Release,
        )
        .map_err(Error::GuestMemory)
    }

    // TODO: Turn this into a doc comment/example.
    // With the current implementation, a common way of consuming entries from the available ring
    // while also leveraging notification suppression is to use a loop, for example:
    //
    // loop {
    //     // We have to explicitly disable notifications if `VIRTIO_F_EVENT_IDX` has not been
    //     // negotiated.
    //     self.disable_notification()?;
    //
    //     for chain in self.iter()? {
    //         // Do something with each chain ...
    //         // Let's assume we process all available chains here.
    //     }
    //
    //     // If `enable_notification` returns `true`, the driver has added more entries to the
    //     // available ring.
    //     if !self.enable_notification()? {
    //         break;
    //     }
    // }
    fn enable_notification<M: GuestMemory>(&mut self, mem: &M) -> Result<bool, Error> {
        self.set_notification(mem, true)?;
        // Ensures the following read is not reordered before any previous write operation.
        fence(Ordering::SeqCst);

        // We double check here to avoid the situation where the available ring has been updated
        // just before we re-enabled notifications, and it's possible to miss one. We compare the
        // current `avail_idx` value to `self.next_avail` because it's where we stopped processing
        // entries. There are situations where we intentionally avoid processing everything in the
        // available ring (which will cause this method to return `true`), but in that case we'll
        // probably not re-enable notifications as we already know there are pending entries.
        self.avail_idx(mem, Ordering::Relaxed)
            .map(|idx| idx != self.next_avail)
    }

    fn disable_notification<M: GuestMemory>(&mut self, mem: &M) -> Result<(), Error> {
        self.set_notification(mem, false)
    }

    fn needs_notification<M: GuestMemory>(&mut self, mem: &M) -> Result<bool, Error> {
        let used_idx = self.next_used;

        // Complete all the writes in add_used() before reading the event.
        fence(Ordering::SeqCst);

        // The VRING_AVAIL_F_NO_INTERRUPT flag isn't supported yet.

        // When the `EVENT_IDX` feature is negotiated, the driver writes into `used_event`
        // a value that's used by the device to determine whether a notification must
        // be submitted after adding a descriptor chain to the used ring. According to the
        // standard, the notification must be sent when `next_used == used_event + 1`, but
        // various device model implementations rely on an inequality instead, most likely
        // to also support use cases where a bunch of descriptor chains are added to the used
        // ring first, and only afterwards the `needs_notification` logic is called. For example,
        // the approach based on `num_added` below is taken from the Linux Kernel implementation
        // (i.e. https://elixir.bootlin.com/linux/v5.15.35/source/drivers/virtio/virtio_ring.c#L661)

        // The `old` variable below is used to determine the value of `next_used` from when
        // `needs_notification` was called last (each `needs_notification` call resets `num_added`
        // to zero, while each `add_used` called increments it by one). Then, the logic below
        // uses wrapped arithmetic to see whether `used_event` can be found between `old` and
        // `next_used` in the circular sequence space of the used ring.
        if self.event_idx_enabled {
            let used_event = self.used_event(mem, Ordering::Relaxed)?;
            let old = used_idx - self.num_added;
            self.num_added = Wrapping(0);

            return Ok(used_idx - used_event - Wrapping(1) < used_idx - old);
        }

        Ok(true)
    }

    fn next_avail(&self) -> u16 {
        self.next_avail.0
    }

    fn set_next_avail(&mut self, next_avail: u16) {
        self.next_avail = Wrapping(next_avail);
    }

    fn next_used(&self) -> u16 {
        self.next_used.0
    }

    fn set_next_used(&mut self, next_used: u16) {
        self.next_used = Wrapping(next_used);
    }

    fn desc_table(&self) -> u64 {
        self.desc_table.0
    }

    fn avail_ring(&self) -> u64 {
        self.avail_ring.0
    }

    fn used_ring(&self) -> u64 {
        self.used_ring.0
    }

    fn event_idx_enabled(&self) -> bool {
        self.event_idx_enabled
    }

    fn pop_descriptor_chain<M>(&mut self, mem: M) -> Option<DescriptorChain<M>>
    where
        M: Clone + Deref,
        M::Target: GuestMemory,
    {
        // Default, iter-based impl. Will be subsequently improved.
        match self.iter(mem) {
            Ok(mut iter) => iter.next(),
            Err(e) => {
                error!("Iterator error {}", e);
                None
            }
        }
    }
}

impl QueueOwnedT for Queue {
    fn iter<M>(&mut self, mem: M) -> Result<AvailIter<'_, M>, Error>
    where
        M: Deref,
        M::Target: GuestMemory,
    {
        // We're checking here that a reset did not happen without re-initializing the queue.
        // TODO: In the future we might want to also check that the other parameters in the
        // queue are valid.
        if !self.ready || self.avail_ring == GuestAddress(0) {
            return Err(Error::QueueNotReady);
        }

        self.avail_idx(mem.deref(), Ordering::Acquire)
            .map(move |idx| AvailIter::new(mem, idx, self))?
    }

    fn go_to_previous_position(&mut self) {
        self.next_avail -= Wrapping(1);
    }
}

/// Consuming iterator over all available descriptor chain heads in the queue.
///
/// # Example
///
/// ```rust
/// # use virtio_bindings::bindings::virtio_ring::{VRING_DESC_F_NEXT, VRING_DESC_F_WRITE};
/// # use virtio_queue::mock::MockSplitQueue;
/// use virtio_queue::{Descriptor, Queue, QueueOwnedT};
/// use vm_memory::{GuestAddress, GuestMemoryMmap};
///
/// # fn populate_queue(m: &GuestMemoryMmap) -> Queue {
/// #    let vq = MockSplitQueue::new(m, 16);
/// #    let mut q: Queue = vq.create_queue().unwrap();
/// #
/// #    // The chains are (0, 1), (2, 3, 4) and (5, 6).
/// #    let mut descs = Vec::new();
/// #    for i in 0..7 {
/// #        let flags = match i {
/// #            1 | 6 => 0,
/// #            2 | 5 => VRING_DESC_F_NEXT | VRING_DESC_F_WRITE,
/// #            4 => VRING_DESC_F_WRITE,
/// #            _ => VRING_DESC_F_NEXT,
/// #        };
/// #
/// #        descs.push(Descriptor::new((0x1000 * (i + 1)) as u64, 0x1000, flags as u16, i + 1));
/// #    }
/// #
/// #    vq.add_desc_chains(&descs, 0).unwrap();
/// #    q
/// # }
/// let m = &GuestMemoryMmap::<()>::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap();
/// // Populate the queue with descriptor chains and update the available ring accordingly.
/// let mut queue = populate_queue(m);
/// let mut i = queue.iter(m).unwrap();
///
/// {
///     let mut c = i.next().unwrap();
///     let _first_head_index = c.head_index();
///     // We should have two descriptors in the first chain.
///     let _desc1 = c.next().unwrap();
///     let _desc2 = c.next().unwrap();
/// }
///
/// {
///     let c = i.next().unwrap();
///     let _second_head_index = c.head_index();
///
///     let mut iter = c.writable();
///     // We should have two writable descriptors in the second chain.
///     let _desc1 = iter.next().unwrap();
///     let _desc2 = iter.next().unwrap();
/// }
///
/// {
///     let c = i.next().unwrap();
///     let _third_head_index = c.head_index();
///
///     let mut iter = c.readable();
///     // We should have one readable descriptor in the third chain.
///     let _desc1 = iter.next().unwrap();
/// }
/// // Let's go back one position in the available ring.
/// i.go_to_previous_position();
/// // We should be able to access again the third descriptor chain.
/// let c = i.next().unwrap();
/// let _third_head_index = c.head_index();
/// ```
#[derive(Debug)]
pub struct AvailIter<'b, M> {
    mem: M,
    desc_table: GuestAddress,
    avail_ring: GuestAddress,
    queue_size: u16,
    last_index: Wrapping<u16>,
    next_avail: &'b mut Wrapping<u16>,
}

impl<'b, M> AvailIter<'b, M>
where
    M: Deref,
    M::Target: GuestMemory,
{
    /// Create a new instance of `AvailInter`.
    ///
    /// # Arguments
    /// * `mem` - the `GuestMemory` object that can be used to access the queue buffers.
    /// * `idx` - the index of the available ring entry where the driver would put the next
    ///           available descriptor chain.
    /// * `queue` - the `Queue` object from which the needed data to create the `AvailIter` can
    ///             be retrieved.
    pub(crate) fn new(mem: M, idx: Wrapping<u16>, queue: &'b mut Queue) -> Result<Self, Error> {
        // The number of descriptor chain heads to process should always
        // be smaller or equal to the queue size, as the driver should
        // never ask the VMM to process a available ring entry more than
        // once. Checking and reporting such incorrect driver behavior
        // can prevent potential hanging and Denial-of-Service from
        // happening on the VMM side.
        if (idx - queue.next_avail).0 > queue.size {
            return Err(Error::InvalidAvailRingIndex);
        }

        Ok(AvailIter {
            mem,
            desc_table: queue.desc_table,
            avail_ring: queue.avail_ring,
            queue_size: queue.size,
            last_index: idx,
            next_avail: &mut queue.next_avail,
        })
    }

    /// Goes back one position in the available descriptor chain offered by the driver.
    ///
    /// Rust does not support bidirectional iterators. This is the only way to revert the effect
    /// of an iterator increment on the queue.
    ///
    /// Note: this method assumes there's only one thread manipulating the queue, so it should only
    /// be invoked in single-threaded context.
    pub fn go_to_previous_position(&mut self) {
        *self.next_avail -= Wrapping(1);
    }
}

impl<'b, M> Iterator for AvailIter<'b, M>
where
    M: Clone + Deref,
    M::Target: GuestMemory,
{
    type Item = DescriptorChain<M>;

    fn next(&mut self) -> Option<Self::Item> {
        if *self.next_avail == self.last_index {
            return None;
        }

        // These two operations can not overflow an u64 since they're working with relatively small
        // numbers compared to u64::MAX.
        let elem_off =
            u64::from(self.next_avail.0.checked_rem(self.queue_size)?) * VIRTQ_AVAIL_ELEMENT_SIZE;
        let offset = VIRTQ_AVAIL_RING_HEADER_SIZE + elem_off;

        let addr = self.avail_ring.checked_add(offset)?;
        let head_index: u16 = self
            .mem
            .load(addr, Ordering::Acquire)
            .map(u16::from_le)
            .map_err(|_| error!("Failed to read from memory {:x}", addr.raw_value()))
            .ok()?;

        *self.next_avail += Wrapping(1);

        Some(DescriptorChain::new(
            self.mem.clone(),
            self.desc_table,
            self.queue_size,
            head_index,
        ))
    }
}

#[cfg(any(test, feature = "test-utils"))]
// It is convenient for tests to implement `PartialEq`, but it is not a
// proper implementation as `GuestMemory` errors cannot implement `PartialEq`.
impl PartialEq for Error {
    fn eq(&self, other: &Self) -> bool {
        format!("{}", &self) == format!("{}", other)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::defs::{DEFAULT_AVAIL_RING_ADDR, DEFAULT_DESC_TABLE_ADDR, DEFAULT_USED_RING_ADDR};
    use crate::mock::MockSplitQueue;
    use crate::Descriptor;
    use virtio_bindings::bindings::virtio_ring::{
        VRING_DESC_F_NEXT, VRING_DESC_F_WRITE, VRING_USED_F_NO_NOTIFY,
    };

    use vm_memory::{Address, Bytes, GuestAddress, GuestMemoryMmap};

    #[test]
    fn test_queue_is_valid() {
        let m = &GuestMemoryMmap::<()>::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap();
        let vq = MockSplitQueue::new(m, 16);
        let mut q: Queue = vq.create_queue().unwrap();

        // q is currently valid
        assert!(q.is_valid(m));

        // shouldn't be valid when not marked as ready
        q.set_ready(false);
        assert!(!q.ready());
        assert!(!q.is_valid(m));
        q.set_ready(true);

        // shouldn't be allowed to set a size > max_size
        q.set_size(q.max_size() << 1);
        assert_eq!(q.size, q.max_size());

        // or set the size to 0
        q.set_size(0);
        assert_eq!(q.size, q.max_size());

        // or set a size which is not a power of 2
        q.set_size(11);
        assert_eq!(q.size, q.max_size());

        // but should be allowed to set a size if 0 < size <= max_size and size is a power of two
        q.set_size(4);
        assert_eq!(q.size, 4);
        q.size = q.max_size();

        // shouldn't be allowed to set an address that breaks the alignment constraint
        q.set_desc_table_address(Some(0xf), None);
        assert_eq!(q.desc_table.0, vq.desc_table_addr().0);
        // should be allowed to set an aligned out of bounds address
        q.set_desc_table_address(Some(0xffff_fff0), None);
        assert_eq!(q.desc_table.0, 0xffff_fff0);
        // but shouldn't be valid
        assert!(!q.is_valid(m));
        // but should be allowed to set a valid description table address
        q.set_desc_table_address(Some(0x10), None);
        assert_eq!(q.desc_table.0, 0x10);
        assert!(q.is_valid(m));
        let addr = vq.desc_table_addr().0;
        q.set_desc_table_address(Some(addr as u32), Some((addr >> 32) as u32));

        // shouldn't be allowed to set an address that breaks the alignment constraint
        q.set_avail_ring_address(Some(0x1), None);
        assert_eq!(q.avail_ring.0, vq.avail_addr().0);
        // should be allowed to set an aligned out of bounds address
        q.set_avail_ring_address(Some(0xffff_fffe), None);
        assert_eq!(q.avail_ring.0, 0xffff_fffe);
        // but shouldn't be valid
        assert!(!q.is_valid(m));
        // but should be allowed to set a valid available ring address
        q.set_avail_ring_address(Some(0x2), None);
        assert_eq!(q.avail_ring.0, 0x2);
        assert!(q.is_valid(m));
        let addr = vq.avail_addr().0;
        q.set_avail_ring_address(Some(addr as u32), Some((addr >> 32) as u32));

        // shouldn't be allowed to set an address that breaks the alignment constraint
        q.set_used_ring_address(Some(0x3), None);
        assert_eq!(q.used_ring.0, vq.used_addr().0);
        // should be allowed to set an aligned out of bounds address
        q.set_used_ring_address(Some(0xffff_fffc), None);
        assert_eq!(q.used_ring.0, 0xffff_fffc);
        // but shouldn't be valid
        assert!(!q.is_valid(m));
        // but should be allowed to set a valid used ring address
        q.set_used_ring_address(Some(0x4), None);
        assert_eq!(q.used_ring.0, 0x4);
        let addr = vq.used_addr().0;
        q.set_used_ring_address(Some(addr as u32), Some((addr >> 32) as u32));
        assert!(q.is_valid(m));
    }

    #[test]
    fn test_add_used() {
        let mem = &GuestMemoryMmap::<()>::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap();
        let vq = MockSplitQueue::new(mem, 16);
        let mut q: Queue = vq.create_queue().unwrap();

        assert_eq!(q.used_idx(mem, Ordering::Acquire).unwrap(), Wrapping(0));
        assert_eq!(u16::from_le(vq.used().idx().load()), 0);

        // index too large
        assert!(q.add_used(mem, 16, 0x1000).is_err());
        assert_eq!(u16::from_le(vq.used().idx().load()), 0);

        // should be ok
        q.add_used(mem, 1, 0x1000).unwrap();
        assert_eq!(q.next_used, Wrapping(1));
        assert_eq!(q.used_idx(mem, Ordering::Acquire).unwrap(), Wrapping(1));
        assert_eq!(u16::from_le(vq.used().idx().load()), 1);

        let x = vq.used().ring().ref_at(0).unwrap().load();
        assert_eq!(x.id(), 1);
        assert_eq!(x.len(), 0x1000);
    }

    #[test]
    fn test_reset_queue() {
        let m = &GuestMemoryMmap::<()>::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap();
        let vq = MockSplitQueue::new(m, 16);
        let mut q: Queue = vq.create_queue().unwrap();

        q.set_size(8);
        // The address set by `MockSplitQueue` for the descriptor table is DEFAULT_DESC_TABLE_ADDR,
        // so let's change it for testing the reset.
        q.set_desc_table_address(Some(0x5000), None);
        // Same for `event_idx_enabled`, `next_avail` `next_used` and `signalled_used`.
        q.set_event_idx(true);
        q.set_next_avail(2);
        q.set_next_used(4);
        q.num_added = Wrapping(15);
        assert_eq!(q.size, 8);
        // `create_queue` also marks the queue as ready.
        assert!(q.ready);
        assert_ne!(q.desc_table, GuestAddress(DEFAULT_DESC_TABLE_ADDR));
        assert_ne!(q.avail_ring, GuestAddress(DEFAULT_AVAIL_RING_ADDR));
        assert_ne!(q.used_ring, GuestAddress(DEFAULT_USED_RING_ADDR));
        assert_ne!(q.next_avail, Wrapping(0));
        assert_ne!(q.next_used, Wrapping(0));
        assert_ne!(q.num_added, Wrapping(0));
        assert!(q.event_idx_enabled);

        q.reset();
        assert_eq!(q.size, 16);
        assert!(!q.ready);
        assert_eq!(q.desc_table, GuestAddress(DEFAULT_DESC_TABLE_ADDR));
        assert_eq!(q.avail_ring, GuestAddress(DEFAULT_AVAIL_RING_ADDR));
        assert_eq!(q.used_ring, GuestAddress(DEFAULT_USED_RING_ADDR));
        assert_eq!(q.next_avail, Wrapping(0));
        assert_eq!(q.next_used, Wrapping(0));
        assert_eq!(q.num_added, Wrapping(0));
        assert!(!q.event_idx_enabled);
    }

    #[test]
    fn test_needs_notification() {
        let mem = &GuestMemoryMmap::<()>::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap();
        let qsize = 16;
        let vq = MockSplitQueue::new(mem, qsize);
        let mut q: Queue = vq.create_queue().unwrap();
        let avail_addr = vq.avail_addr();

        // It should always return true when EVENT_IDX isn't enabled.
        for i in 0..qsize {
            q.next_used = Wrapping(i);
            assert!(q.needs_notification(mem).unwrap());
        }

        mem.write_obj::<u16>(
            u16::to_le(4),
            avail_addr.unchecked_add(4 + qsize as u64 * 2),
        )
        .unwrap();
        q.set_event_idx(true);

        // Incrementing up to this value causes an `u16` to wrap back to 0.
        let wrap = u32::from(u16::MAX) + 1;

        for i in 0..wrap + 12 {
            q.next_used = Wrapping(i as u16);
            // Let's test wrapping around the maximum index value as well.
            // `num_added` needs to be at least `1` to represent the fact that new descriptor
            // chains have be added to the used ring since the last time `needs_notification`
            // returned.
            q.num_added = Wrapping(1);
            let expected = i == 5 || i == (5 + wrap);
            assert_eq!((q.needs_notification(mem).unwrap(), i), (expected, i));
        }

        mem.write_obj::<u16>(
            u16::to_le(8),
            avail_addr.unchecked_add(4 + qsize as u64 * 2),
        )
        .unwrap();

        // Returns `false` because the current `used_event` value is behind both `next_used` and
        // the value of `next_used` at the time when `needs_notification` last returned (which is
        // computed based on `num_added` as described in the comments for `needs_notification`.
        assert!(!q.needs_notification(mem).unwrap());

        mem.write_obj::<u16>(
            u16::to_le(15),
            avail_addr.unchecked_add(4 + qsize as u64 * 2),
        )
        .unwrap();

        q.num_added = Wrapping(1);
        assert!(!q.needs_notification(mem).unwrap());

        q.next_used = Wrapping(15);
        q.num_added = Wrapping(1);
        assert!(!q.needs_notification(mem).unwrap());

        q.next_used = Wrapping(16);
        q.num_added = Wrapping(1);
        assert!(q.needs_notification(mem).unwrap());

        // Calling `needs_notification` again immediately returns `false`.
        assert!(!q.needs_notification(mem).unwrap());

        mem.write_obj::<u16>(
            u16::to_le(u16::MAX - 3),
            avail_addr.unchecked_add(4 + qsize as u64 * 2),
        )
        .unwrap();
        q.next_used = Wrapping(u16::MAX - 2);
        q.num_added = Wrapping(1);
        // Returns `true` because, when looking at circular sequence of indices of the used ring,
        // the value we wrote in the `used_event` appears between the "old" value of `next_used`
        // (i.e. `next_used` - `num_added`) and the current `next_used`, thus suggesting that we
        // need to notify the driver.
        assert!(q.needs_notification(mem).unwrap());
    }

    #[test]
    fn test_enable_disable_notification() {
        let mem = &GuestMemoryMmap::<()>::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap();
        let vq = MockSplitQueue::new(mem, 16);

        let mut q: Queue = vq.create_queue().unwrap();
        let used_addr = vq.used_addr();

        assert!(!q.event_idx_enabled);

        q.enable_notification(mem).unwrap();
        let v = mem.read_obj::<u16>(used_addr).map(u16::from_le).unwrap();
        assert_eq!(v, 0);

        q.disable_notification(mem).unwrap();
        let v = mem.read_obj::<u16>(used_addr).map(u16::from_le).unwrap();
        assert_eq!(v, VRING_USED_F_NO_NOTIFY as u16);

        q.enable_notification(mem).unwrap();
        let v = mem.read_obj::<u16>(used_addr).map(u16::from_le).unwrap();
        assert_eq!(v, 0);

        q.set_event_idx(true);
        let avail_addr = vq.avail_addr();
        mem.write_obj::<u16>(u16::to_le(2), avail_addr.unchecked_add(2))
            .unwrap();

        assert!(q.enable_notification(mem).unwrap());
        q.next_avail = Wrapping(2);
        assert!(!q.enable_notification(mem).unwrap());

        mem.write_obj::<u16>(u16::to_le(8), avail_addr.unchecked_add(2))
            .unwrap();

        assert!(q.enable_notification(mem).unwrap());
        q.next_avail = Wrapping(8);
        assert!(!q.enable_notification(mem).unwrap());
    }

    #[test]
    fn test_consume_chains_with_notif() {
        let mem = &GuestMemoryMmap::<()>::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap();
        let vq = MockSplitQueue::new(mem, 16);

        let mut q: Queue = vq.create_queue().unwrap();

        // q is currently valid.
        assert!(q.is_valid(mem));

        // The chains are (0, 1), (2, 3, 4), (5, 6), (7, 8), (9, 10, 11, 12).
        let mut descs = Vec::new();
        for i in 0..13 {
            let flags = match i {
                1 | 4 | 6 | 8 | 12 => 0,
                _ => VRING_DESC_F_NEXT,
            };

            descs.push(Descriptor::new(
                (0x1000 * (i + 1)) as u64,
                0x1000,
                flags as u16,
                i + 1,
            ));
        }

        vq.add_desc_chains(&descs, 0).unwrap();
        // Update the index of the chain that can be consumed to not be the last one.
        // This enables us to consume chains in multiple iterations as opposed to consuming
        // all the driver written chains at once.
        vq.avail().idx().store(u16::to_le(2));
        // No descriptor chains are consumed at this point.
        assert_eq!(q.next_avail(), 0);

        let mut i = 0;

        loop {
            i += 1;
            q.disable_notification(mem).unwrap();

            while let Some(chain) = q.iter(mem).unwrap().next() {
                // Process the descriptor chain, and then add entries to the
                // used ring.
                let head_index = chain.head_index();
                let mut desc_len = 0;
                chain.for_each(|d| {
                    if d.flags() as u32 & VRING_DESC_F_WRITE == VRING_DESC_F_WRITE {
                        desc_len += d.len();
                    }
                });
                q.add_used(mem, head_index, desc_len).unwrap();
            }
            if !q.enable_notification(mem).unwrap() {
                break;
            }
        }
        // The chains should be consumed in a single loop iteration because there's nothing updating
        // the `idx` field of the available ring in the meantime.
        assert_eq!(i, 1);
        // The next chain that can be consumed should have index 2.
        assert_eq!(q.next_avail(), 2);
        assert_eq!(q.next_used(), 2);
        // Let the device know it can consume one more chain.
        vq.avail().idx().store(u16::to_le(3));
        i = 0;

        loop {
            i += 1;
            q.disable_notification(mem).unwrap();

            while let Some(chain) = q.iter(mem).unwrap().next() {
                // Process the descriptor chain, and then add entries to the
                // used ring.
                let head_index = chain.head_index();
                let mut desc_len = 0;
                chain.for_each(|d| {
                    if d.flags() as u32 & VRING_DESC_F_WRITE == VRING_DESC_F_WRITE {
                        desc_len += d.len();
                    }
                });
                q.add_used(mem, head_index, desc_len).unwrap();
            }

            // For the simplicity of the test we are updating here the `idx` value of the available
            // ring. Ideally this should be done on a separate thread.
            // Because of this update, the loop should be iterated again to consume the new
            // available descriptor chains.
            vq.avail().idx().store(u16::to_le(4));
            if !q.enable_notification(mem).unwrap() {
                break;
            }
        }
        assert_eq!(i, 2);
        // The next chain that can be consumed should have index 4.
        assert_eq!(q.next_avail(), 4);
        assert_eq!(q.next_used(), 4);

        // Set an `idx` that is bigger than the number of entries added in the ring.
        // This is an allowed scenario, but the indexes of the chain will have unexpected values.
        vq.avail().idx().store(u16::to_le(7));
        loop {
            q.disable_notification(mem).unwrap();

            while let Some(chain) = q.iter(mem).unwrap().next() {
                // Process the descriptor chain, and then add entries to the
                // used ring.
                let head_index = chain.head_index();
                let mut desc_len = 0;
                chain.for_each(|d| {
                    if d.flags() as u32 & VRING_DESC_F_WRITE == VRING_DESC_F_WRITE {
                        desc_len += d.len();
                    }
                });
                q.add_used(mem, head_index, desc_len).unwrap();
            }
            if !q.enable_notification(mem).unwrap() {
                break;
            }
        }
        assert_eq!(q.next_avail(), 7);
        assert_eq!(q.next_used(), 7);
    }

    #[test]
    fn test_invalid_avail_idx() {
        // This is a negative test for the following MUST from the spec: `A driver MUST NOT
        // decrement the available idx on a virtqueue (ie. there is no way to “unexpose” buffers).`.
        // We validate that for this misconfiguration, the device does not panic.
        let mem = &GuestMemoryMmap::<()>::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap();
        let vq = MockSplitQueue::new(mem, 16);

        let mut q: Queue = vq.create_queue().unwrap();

        // q is currently valid.
        assert!(q.is_valid(mem));

        // The chains are (0, 1), (2, 3, 4), (5, 6).
        let mut descs = Vec::new();
        for i in 0..7 {
            let flags = match i {
                1 | 4 | 6 => 0,
                _ => VRING_DESC_F_NEXT,
            };

            descs.push(Descriptor::new(
                (0x1000 * (i + 1)) as u64,
                0x1000,
                flags as u16,
                i + 1,
            ));
        }

        vq.add_desc_chains(&descs, 0).unwrap();
        // Let the device know it can consume chains with the index < 2.
        vq.avail().idx().store(u16::to_le(3));
        // No descriptor chains are consumed at this point.
        assert_eq!(q.next_avail(), 0);
        assert_eq!(q.next_used(), 0);

        loop {
            q.disable_notification(mem).unwrap();

            while let Some(chain) = q.iter(mem).unwrap().next() {
                // Process the descriptor chain, and then add entries to the
                // used ring.
                let head_index = chain.head_index();
                let mut desc_len = 0;
                chain.for_each(|d| {
                    if d.flags() as u32 & VRING_DESC_F_WRITE == VRING_DESC_F_WRITE {
                        desc_len += d.len();
                    }
                });
                q.add_used(mem, head_index, desc_len).unwrap();
            }
            if !q.enable_notification(mem).unwrap() {
                break;
            }
        }
        // The next chain that can be consumed should have index 3.
        assert_eq!(q.next_avail(), 3);
        assert_eq!(q.avail_idx(mem, Ordering::Acquire).unwrap(), Wrapping(3));
        assert_eq!(q.next_used(), 3);
        assert_eq!(q.used_idx(mem, Ordering::Acquire).unwrap(), Wrapping(3));
        assert!(q.lock().ready());

        // Decrement `idx` which should be forbidden. We don't enforce this thing, but we should
        // test that we don't panic in case the driver decrements it.
        vq.avail().idx().store(u16::to_le(1));
        // Invalid available ring index
        assert!(q.iter(mem).is_err());
    }

    #[test]
    fn test_iterator_and_avail_idx() {
        // This test ensures constructing a descriptor chain iterator succeeds
        // with valid available ring indexes while produces an error with invalid
        // indexes.
        let queue_size = 2;
        let mem = &GuestMemoryMmap::<()>::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap();
        let vq = MockSplitQueue::new(mem, queue_size);

        let mut q: Queue = vq.create_queue().unwrap();

        // q is currently valid.
        assert!(q.is_valid(mem));

        // Create descriptors to fill up the queue
        let mut descs = Vec::new();
        for i in 0..queue_size {
            descs.push(Descriptor::new(
                (0x1000 * (i + 1)) as u64,
                0x1000,
                0_u16,
                i + 1,
            ));
        }
        vq.add_desc_chains(&descs, 0).unwrap();

        // Set the 'next_available' index to 'u16:MAX' to test the wrapping scenarios
        q.set_next_avail(u16::MAX);

        // When the number of chains exposed by the driver is equal to or less than the queue
        // size, the available ring index is valid and constructs an iterator successfully.
        let avail_idx = Wrapping(q.next_avail()) + Wrapping(queue_size);
        vq.avail().idx().store(u16::to_le(avail_idx.0));
        assert!(q.iter(mem).is_ok());
        let avail_idx = Wrapping(q.next_avail()) + Wrapping(queue_size - 1);
        vq.avail().idx().store(u16::to_le(avail_idx.0));
        assert!(q.iter(mem).is_ok());

        // When the number of chains exposed by the driver is larger than the queue size, the
        // available ring index is invalid and produces an error from constructing an iterator.
        let avail_idx = Wrapping(q.next_avail()) + Wrapping(queue_size + 1);
        vq.avail().idx().store(u16::to_le(avail_idx.0));
        assert!(q.iter(mem).is_err());
    }

    #[test]
    fn test_descriptor_and_iterator() {
        let m = &GuestMemoryMmap::<()>::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap();
        let vq = MockSplitQueue::new(m, 16);

        let mut q: Queue = vq.create_queue().unwrap();

        // q is currently valid
        assert!(q.is_valid(m));

        // the chains are (0, 1), (2, 3, 4) and (5, 6)
        let mut descs = Vec::new();
        for j in 0..7 {
            let flags = match j {
                1 | 6 => 0,
                2 | 5 => VRING_DESC_F_NEXT | VRING_DESC_F_WRITE,
                4 => VRING_DESC_F_WRITE,
                _ => VRING_DESC_F_NEXT,
            };

            descs.push(Descriptor::new(
                (0x1000 * (j + 1)) as u64,
                0x1000,
                flags as u16,
                j + 1,
            ));
        }

        vq.add_desc_chains(&descs, 0).unwrap();

        let mut i = q.iter(m).unwrap();

        {
            let c = i.next().unwrap();
            assert_eq!(c.head_index(), 0);

            let mut iter = c;
            assert!(iter.next().is_some());
            assert!(iter.next().is_some());
            assert!(iter.next().is_none());
            assert!(iter.next().is_none());
        }

        {
            let c = i.next().unwrap();
            assert_eq!(c.head_index(), 2);

            let mut iter = c.writable();
            assert!(iter.next().is_some());
            assert!(iter.next().is_some());
            assert!(iter.next().is_none());
            assert!(iter.next().is_none());
        }

        {
            let c = i.next().unwrap();
            assert_eq!(c.head_index(), 5);

            let mut iter = c.readable();
            assert!(iter.next().is_some());
            assert!(iter.next().is_none());
            assert!(iter.next().is_none());
        }
    }

    #[test]
    fn test_iterator() {
        let m = &GuestMemoryMmap::<()>::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap();
        let vq = MockSplitQueue::new(m, 16);

        let mut q: Queue = vq.create_queue().unwrap();

        q.size = q.max_size;
        q.desc_table = vq.desc_table_addr();
        q.avail_ring = vq.avail_addr();
        q.used_ring = vq.used_addr();
        assert!(q.is_valid(m));

        {
            // an invalid queue should return an iterator with no next
            q.ready = false;
            assert!(q.iter(m).is_err());
        }

        q.ready = true;

        // now let's create two simple descriptor chains
        // the chains are (0, 1) and (2, 3, 4)
        {
            let mut descs = Vec::new();
            for j in 0..5u16 {
                let flags = match j {
                    1 | 4 => 0,
                    _ => VRING_DESC_F_NEXT,
                };

                descs.push(Descriptor::new(
                    (0x1000 * (j + 1)) as u64,
                    0x1000,
                    flags as u16,
                    j + 1,
                ));
            }
            vq.add_desc_chains(&descs, 0).unwrap();

            let mut i = q.iter(m).unwrap();

            {
                let mut c = i.next().unwrap();
                assert_eq!(c.head_index(), 0);

                c.next().unwrap();
                assert!(c.next().is_some());
                assert!(c.next().is_none());
                assert_eq!(c.head_index(), 0);
            }

            {
                let mut c = i.next().unwrap();
                assert_eq!(c.head_index(), 2);

                c.next().unwrap();
                c.next().unwrap();
                c.next().unwrap();
                assert!(c.next().is_none());
                assert_eq!(c.head_index(), 2);
            }

            // also test go_to_previous_position() works as expected
            {
                assert!(i.next().is_none());
                i.go_to_previous_position();
                let mut c = q.iter(m).unwrap().next().unwrap();
                c.next().unwrap();
                c.next().unwrap();
                c.next().unwrap();
                assert!(c.next().is_none());
            }
        }

        // Test that iterating some broken descriptor chain does not exceed
        // 2^32 bytes in total (VIRTIO spec version 1.2, 2.7.5.2:
        // Drivers MUST NOT add a descriptor chain longer than 2^32 bytes in
        // total)
        {
            let descs = vec![
                Descriptor::new(0x1000, 0xffff_ffff, VRING_DESC_F_NEXT as u16, 1),
                Descriptor::new(0x1000, 0x1234_5678, 0, 2),
            ];
            vq.add_desc_chains(&descs, 0).unwrap();
            let mut yielded_bytes_by_iteration = 0_u32;
            for d in q.iter(m).unwrap().next().unwrap() {
                yielded_bytes_by_iteration = yielded_bytes_by_iteration
                    .checked_add(d.len())
                    .expect("iterator should not yield more than 2^32 bytes");
            }
        }

        // Same as above, but test with a descriptor which is self-referential
        {
            let descs = vec![Descriptor::new(
                0x1000,
                0xffff_ffff,
                VRING_DESC_F_NEXT as u16,
                0,
            )];
            vq.add_desc_chains(&descs, 0).unwrap();
            let mut yielded_bytes_by_iteration = 0_u32;
            for d in q.iter(m).unwrap().next().unwrap() {
                yielded_bytes_by_iteration = yielded_bytes_by_iteration
                    .checked_add(d.len())
                    .expect("iterator should not yield more than 2^32 bytes");
            }
        }
    }

    #[test]
    fn test_regression_iterator_division() {
        // This is a regression test that tests that the iterator does not try to divide
        // by 0 when the queue size is 0
        let m = &GuestMemoryMmap::<()>::from_ranges(&[(GuestAddress(0), 0x10000)]).unwrap();
        let vq = MockSplitQueue::new(m, 1);
        // This input was generated by the fuzzer, both for the QueueS and the Descriptor
        let descriptors: Vec<Descriptor> = vec![Descriptor::new(
            14178673876262995140,
            3301229764,
            50372,
            50372,
        )];
        vq.build_desc_chain(&descriptors).unwrap();

        let mut q = Queue {
            max_size: 38,
            next_avail: Wrapping(0),
            next_used: Wrapping(0),
            event_idx_enabled: false,
            num_added: Wrapping(0),
            size: 0,
            ready: false,
            desc_table: GuestAddress(12837708984796196),
            avail_ring: GuestAddress(0),
            used_ring: GuestAddress(9943947977301164032),
        };

        assert!(q.pop_descriptor_chain(m).is_none());
    }

    #[test]
    fn test_setters_error_cases() {
        assert_eq!(Queue::new(15).unwrap_err(), Error::InvalidMaxSize);
        let mut q = Queue::new(16).unwrap();

        let expected_val = q.desc_table.0;
        assert_eq!(
            q.try_set_desc_table_address(GuestAddress(0xf)).unwrap_err(),
            Error::InvalidDescTableAlign
        );
        assert_eq!(q.desc_table(), expected_val);

        let expected_val = q.avail_ring.0;
        assert_eq!(
            q.try_set_avail_ring_address(GuestAddress(0x1)).unwrap_err(),
            Error::InvalidAvailRingAlign
        );
        assert_eq!(q.avail_ring(), expected_val);

        let expected_val = q.used_ring.0;
        assert_eq!(
            q.try_set_used_ring_address(GuestAddress(0x3)).unwrap_err(),
            Error::InvalidUsedRingAlign
        );
        assert_eq!(q.used_ring(), expected_val);

        let expected_val = q.size;
        assert_eq!(q.try_set_size(15).unwrap_err(), Error::InvalidSize);
        assert_eq!(q.size(), expected_val)
    }

    #[test]
    // This is a regression test for a fuzzing finding. If the driver requests a reset of the
    // device, but then does not re-initializes the queue then a subsequent call to process
    // a request should yield no descriptors to process. Before this fix we were processing
    // descriptors that were added to the queue before, and we were ending up processing 255
    // descriptors per chain.
    fn test_regression_timeout_after_reset() {
        // The input below was generated by libfuzzer and adapted for this test.
        let m = &GuestMemoryMmap::<()>::from_ranges(&[(GuestAddress(0x0), 0x10000)]).unwrap();
        let vq = MockSplitQueue::new(m, 1024);

        // This input below was generated by the fuzzer.
        let descriptors: Vec<Descriptor> = vec![
            Descriptor::new(21508325467, 0, 1, 4),
            Descriptor::new(2097152, 4096, 3, 0),
            Descriptor::new(18374686479672737792, 4294967295, 65535, 29),
            Descriptor::new(76842670169653248, 1114115, 0, 0),
            Descriptor::new(16, 983040, 126, 3),
            Descriptor::new(897648164864, 0, 0, 0),
            Descriptor::new(111669149722, 0, 0, 0),
        ];
        vq.build_multiple_desc_chains(&descriptors).unwrap();

        let mut q: Queue = vq.create_queue().unwrap();

        // Setting the queue to ready should not allow consuming descriptors after reset.
        q.reset();
        q.set_ready(true);
        let mut counter = 0;
        while let Some(mut desc_chain) = q.pop_descriptor_chain(m) {
            // this empty loop is here to check that there are no side effects
            // in terms of memory & execution time.
            while desc_chain.next().is_some() {
                counter += 1;
            }
        }
        assert_eq!(counter, 0);

        // Setting the avail_addr to valid should not allow consuming descriptors after reset.
        q.reset();
        q.set_avail_ring_address(Some(0x1000), None);
        assert_eq!(q.avail_ring, GuestAddress(0x1000));
        counter = 0;
        while let Some(mut desc_chain) = q.pop_descriptor_chain(m) {
            // this empty loop is here to check that there are no side effects
            // in terms of memory & execution time.
            while desc_chain.next().is_some() {
                counter += 1;
            }
        }
        assert_eq!(counter, 0);
    }
}
