// Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

use criterion::{black_box, BatchSize, Criterion};
use virtio_queue::{Queue, QueueOwnedT, QueueT};
use vm_memory::{GuestAddress, GuestMemory, GuestMemoryMmap};

use virtio_queue::mock::MockSplitQueue;

pub fn benchmark_queue(c: &mut Criterion) {
    fn walk_queue<M: GuestMemory>(q: &mut Queue, mem: &M) -> (usize, usize) {
        let mut num_chains = 0;
        let mut num_descriptors = 0;

        q.iter(mem).unwrap().for_each(|chain| {
            num_chains += 1;
            chain.for_each(|_| num_descriptors += 1);
        });

        (num_chains, num_descriptors)
    }

    fn bench_queue<S, R>(c: &mut Criterion, bench_name: &str, setup: S, mut routine: R)
    where
        S: FnMut() -> Queue + Clone,
        R: FnMut(Queue),
    {
        c.bench_function(bench_name, move |b| {
            b.iter_batched(
                setup.clone(),
                |q| routine(black_box(q)),
                BatchSize::SmallInput,
            )
        });
    }

    let mem = GuestMemoryMmap::<()>::from_ranges(&[(GuestAddress(0x0), 0x1_0000_0000)]).unwrap();

    let queue_with_chains = |num_chains, len, indirect| {
        let mut mq = MockSplitQueue::new(&mem, 256);
        for _ in 0..num_chains {
            if indirect {
                mq.add_indirect_chain(len).unwrap();
            } else {
                mq.add_chain(len).unwrap();
            }
        }
        mq.create_queue().unwrap()
    };

    let empty_queue = || {
        let mq = MockSplitQueue::new(&mem, 256);
        mq.create_queue().unwrap()
    };

    for indirect in [false, true].iter().copied() {
        bench_queue(
            c,
            &format!("single chain (indirect={})", indirect),
            || queue_with_chains(1, 128, indirect),
            |mut q| {
                let (num_chains, num_descriptors) = walk_queue(&mut q, &mem);
                assert_eq!(num_chains, 1);
                assert_eq!(num_descriptors, 128);
            },
        );

        bench_queue(
            c,
            &format!("multiple chains (indirect={})", indirect),
            || queue_with_chains(128, 1, indirect),
            |mut q| {
                let (num_chains, num_descriptors) = walk_queue(&mut q, &mem);
                assert_eq!(num_chains, 128);
                assert_eq!(num_descriptors, 128);
            },
        );
    }

    bench_queue(c, "add used", empty_queue, |mut q| {
        for _ in 0..128 {
            q.add_used(&mem, 123, 0x1000).unwrap();
        }
    });
}
