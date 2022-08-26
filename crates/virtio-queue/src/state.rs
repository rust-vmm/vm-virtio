use crate::{Error, Queue, QueueT};
use vm_memory::GuestAddress;

/// Representation of the `Queue` state.
///
/// The `QueueState` represents the pure state of the `queue` without tracking any implementation
/// details of the queue. The goal with this design is to minimize the changes required to the
/// state, and thus the required transitions between states when upgrading or downgrading.
///
/// In practice this means that the `QueueState` consists solely of POD (Plain Old Data).
///
/// As this structure has all the fields public it is consider to be untrusted. A validated
/// queue can be created from the state by calling the associated `try_from` function.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct QueueState {
    /// The maximum size in elements offered by the device.
    pub max_size: u16,
    /// Tail position of the available ring.
    pub next_avail: u16,
    /// Head position of the used ring.
    pub next_used: u16,
    /// VIRTIO_F_RING_EVENT_IDX negotiated.
    pub event_idx_enabled: bool,
    /// The queue size in elements the driver selected.
    pub size: u16,
    /// Indicates if the queue is finished with configuration.
    pub ready: bool,
    /// Guest physical address of the descriptor table.
    pub desc_table: u64,
    /// Guest physical address of the available ring.
    pub avail_ring: u64,
    /// Guest physical address of the used ring.
    pub used_ring: u64,
}

impl TryFrom<QueueState> for Queue {
    type Error = Error;

    fn try_from(q_state: QueueState) -> Result<Self, Self::Error> {
        let mut q = Queue::new(q_state.max_size)?;

        q.set_next_avail(q_state.next_avail);
        q.set_next_used(q_state.next_used);
        q.set_event_idx(q_state.event_idx_enabled);
        q.try_set_size(q_state.size)?;
        q.set_ready(q_state.ready);
        q.try_set_desc_table_address(GuestAddress(q_state.desc_table))?;
        q.try_set_avail_ring_address(GuestAddress(q_state.avail_ring))?;
        q.try_set_used_ring_address(GuestAddress(q_state.used_ring))?;

        Ok(q)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn create_valid_queue_state() -> QueueState {
        let queue = Queue::new(16).unwrap();
        queue.state()
    }

    #[test]
    fn test_empty_queue_state() {
        let max_size = 16;
        let queue = Queue::new(max_size).unwrap();

        // Saving the state of a queue on which we didn't do any operation is ok.
        // Same for restore.
        let queue_state = queue.state();
        let restored_q = Queue::try_from(queue_state).unwrap();
        assert_eq!(queue, restored_q);
    }

    #[test]
    fn test_invalid_queue_state() {
        // Let's generate a state that we know is valid so we can just alter one field at a time.
        let mut q_state = create_valid_queue_state();

        // Test invalid max_size.
        // Size too small.
        q_state.max_size = 0;
        assert!(Queue::try_from(q_state).is_err());
        // Size too big.
        q_state.max_size = u16::MAX;
        assert!(Queue::try_from(q_state).is_err());
        // Size not a power of 2.
        q_state.max_size = 15;
        assert!(Queue::try_from(q_state).is_err());

        // Test invalid size.
        let mut q_state = create_valid_queue_state();
        // Size too small.
        q_state.size = 0;
        assert!(Queue::try_from(q_state).is_err());
        // Size too big.
        q_state.size = u16::MAX;
        assert!(Queue::try_from(q_state).is_err());
        // Size not a power of 2.
        q_state.size = 15;
        assert!(Queue::try_from(q_state).is_err());

        // Test invalid desc_table.
        let mut q_state = create_valid_queue_state();
        q_state.desc_table = 0xf;
        assert!(Queue::try_from(q_state).is_err());

        // Test invalid avail_ring.
        let mut q_state = create_valid_queue_state();
        q_state.avail_ring = 0x1;
        assert!(Queue::try_from(q_state).is_err());

        // Test invalid used_ring.
        let mut q_state = create_valid_queue_state();
        q_state.used_ring = 0x3;
        assert!(Queue::try_from(q_state).is_err());
    }
}
