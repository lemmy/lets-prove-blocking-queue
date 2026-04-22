//! Bounded blocking FIFO queue: a `Mutex<VecDeque<T>>` plus two
//! `Condvar`s, one for "not full" (waited on by producers) and one for
//! "not empty" (waited on by consumers).
//!
//! This file is the actual program. It is plain `std`-only Rust — the
//! same code any Rust programmer would write for a textbook bounded
//! buffer.
//!
//! Two adjacent crates re-use this source file without duplicating it:
//!
//!   * `../verus/blocking_queue.rs` pulls this file in via
//!     `#[path = "../src/lib.rs"] mod blocking_queue;` and pairs it
//!     with a Verus-checked proof that the protocol implemented below
//!     is deadlock-free. The `#[cfg_attr(verus_keep_ghost,
//!     verifier::external)]` annotations on `BlockingQueue` and its
//!     methods tell Verus to parse the implementation but skip
//!     verifying it directly (Verus has no model for
//!     `std::sync::{Mutex, Condvar}`); the proof verifies an abstract
//!     state machine that this code refines.
//!   * `../loom/` is a separate Cargo crate that depends on this one
//!     by path and is built under `RUSTFLAGS="--cfg loom"`. Under that
//!     cfg the `pub use` block below swaps `std::sync::{Arc, Mutex,
//!     Condvar}` and `std::thread` for loom's instrumented mocks, so
//!     loom's C11 scheduler can permute every legal interleaving of
//!     the producers and consumers exercising the queue.
//!
//! The link from this implementation to the Verus proof is the four
//! labelled comments inside `put` / `get`:
//!
//!     // === abstract transition: put_block ===
//!     // === abstract transition: put_succeed ===
//!     // === abstract transition: get_block ===
//!     // === abstract transition: get_succeed ===
//!
//! Each one names one transition of the abstract state machine in
//! `../verus/blocking_queue.rs`.

use std::collections::VecDeque;

// `Mutex`, `Condvar`, `Arc`, and `thread` are swapped between the
// standard library and loom's instrumented mocks based on the `loom`
// cfg flag.
//
//   * Plain `cargo` / `cargo test`               -> std primitives.
//   * `RUSTFLAGS="--cfg loom" cargo test ...`    -> loom primitives, so
//     the C11 scheduler in `loom::model(..)` can permute every possible
//     interleaving of the producers and consumers exercising the queue.
//
// `BlockingQueue<T>` itself uses `Mutex<VecDeque<T>>` and two `Condvar`s,
// so swapping these three types is enough to make the implementation
// loom-instrumented.
#[cfg(not(loom))]
pub use std::sync::{Arc, Condvar, Mutex};
#[cfg(not(loom))]
pub use std::thread;

#[cfg(loom)]
pub use loom::sync::{Arc, Condvar, Mutex};
#[cfg(loom)]
pub use loom::thread;

#[cfg(not(loom))]
use std::time::Duration;

/// Bounded blocking FIFO queue: a `Mutex<VecDeque<T>>` plus two
/// `Condvar`s, one for "not full" (waited on by producers) and one for
/// "not empty" (waited on by consumers).
#[cfg_attr(verus_keep_ghost, verifier::external)]
pub struct BlockingQueue<T> {
    capacity: usize,
    state: Mutex<VecDeque<T>>,
    not_full: Condvar,
    not_empty: Condvar,
}

#[cfg_attr(verus_keep_ghost, verifier::external)]
impl<T> BlockingQueue<T> {
    /// Create a queue holding at most `capacity` items.
    ///
    /// # Panics
    ///
    /// Panics if `capacity` is zero — a zero-capacity blocking queue
    /// would deadlock by construction (producer waits for non-full,
    /// which never happens).
    pub fn new(capacity: usize) -> Self {
        assert!(capacity > 0, "capacity must be > 0");
        Self {
            capacity,
            state: Mutex::new(VecDeque::with_capacity(capacity)),
            not_full: Condvar::new(),
            not_empty: Condvar::new(),
        }
    }

    /// Insert `item`, blocking until space is available.
    pub fn put(&self, item: T) {
        let mut buf = self.state.lock().unwrap();
        // Loop on the predicate to defend against spurious wake-ups
        // and the lost-wakeup race after `notify_one`.
        while buf.len() == self.capacity {
            // === abstract transition: put_block ===
            buf = self.not_full.wait(buf).unwrap();
        }
        // === abstract transition: put_succeed ===
        buf.push_back(item);
        self.not_empty.notify_one();
    }

    /// Remove and return the next item, blocking until one is available.
    pub fn get(&self) -> T {
        let mut buf = self.state.lock().unwrap();
        while buf.is_empty() {
            // === abstract transition: get_block ===
            buf = self.not_empty.wait(buf).unwrap();
        }
        // === abstract transition: get_succeed ===
        let item = buf.pop_front().expect("queue was non-empty");
        self.not_full.notify_one();
        item
    }

    /// Current number of buffered items (for tests / diagnostics).
    pub fn len(&self) -> usize {
        self.state.lock().unwrap().len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn capacity(&self) -> usize {
        self.capacity
    }
}

// ---------------------------------------------------------------------------
// Demo helper used by `src/main.rs` (`cargo run`).
//
// Gated on `cfg(not(loom))`: under `--cfg loom` only the loom test
// harness in `../loom/tests/loom.rs` should run, not the std-thread
// demo, which would not fit inside `loom::model`'s thread budget.
// ---------------------------------------------------------------------------

#[cfg(not(loom))]
const CAPACITY: usize = 3;
#[cfg(not(loom))]
const PRODUCERS: usize = 2;
#[cfg(not(loom))]
const CONSUMERS: usize = 2;
#[cfg(not(loom))]
const ITEMS_PER_PRODUCER: usize = 5;

#[cfg(not(loom))]
#[cfg_attr(verus_keep_ghost, verifier::external)]
pub fn run_demo() {
    let queue: Arc<BlockingQueue<(usize, usize)>> = Arc::new(BlockingQueue::new(CAPACITY));
    let mut handles = Vec::new();

    for p in 0..PRODUCERS {
        let queue = Arc::clone(&queue);
        handles.push(thread::spawn(move || {
            for i in 0..ITEMS_PER_PRODUCER {
                println!("producer {p} putting {i}");
                queue.put((p, i));
                thread::sleep(Duration::from_millis(20));
            }
        }));
    }

    let total = PRODUCERS * ITEMS_PER_PRODUCER;
    let per_consumer = total / CONSUMERS;
    for c in 0..CONSUMERS {
        let queue = Arc::clone(&queue);
        handles.push(thread::spawn(move || {
            for _ in 0..per_consumer {
                let (p, i) = queue.get();
                println!("consumer {c} got ({p}, {i})");
                thread::sleep(Duration::from_millis(35));
            }
        }));
    }

    for h in handles {
        h.join().unwrap();
    }
    println!("done; queue len = {}", queue.len());
}

// ---------------------------------------------------------------------------
// Tests.
//
// Standard `cargo test` integration tests. Gated on `cfg(not(loom))`
// because the stress test (4×4 threads, 1000 items) dwarfs loom's
// thread/interleaving budget. The loom-instrumented tests live in
// `../loom/tests/loom.rs` and use much smaller models.
// ---------------------------------------------------------------------------

#[cfg(all(test, not(loom)))]
mod tests {
    use super::*;

    #[test]
    fn single_threaded_round_trip() {
        let q = BlockingQueue::new(2);
        q.put(1);
        q.put(2);
        assert_eq!(q.get(), 1);
        assert_eq!(q.get(), 2);
        assert!(q.is_empty());
    }

    #[test]
    fn producer_blocks_until_consumer_makes_room() {
        let q = Arc::new(BlockingQueue::new(1));
        q.put(10);

        let q2 = Arc::clone(&q);
        let producer = thread::spawn(move || {
            q2.put(20);
        });

        thread::sleep(Duration::from_millis(50));
        assert_eq!(q.get(), 10);
        producer.join().unwrap();
        assert_eq!(q.get(), 20);
    }

    #[test]
    fn many_producers_many_consumers_drain_cleanly() {
        const PRODUCERS: usize = 4;
        const CONSUMERS: usize = 4;
        const PER_PRODUCER: usize = 250;

        let q: Arc<BlockingQueue<usize>> = Arc::new(BlockingQueue::new(8));
        let mut handles = Vec::new();

        for p in 0..PRODUCERS {
            let q = Arc::clone(&q);
            handles.push(thread::spawn(move || {
                for i in 0..PER_PRODUCER {
                    q.put(p * PER_PRODUCER + i);
                }
            }));
        }

        let total = PRODUCERS * PER_PRODUCER;
        let per_consumer = total / CONSUMERS;
        let mut consumer_handles = Vec::new();
        for _ in 0..CONSUMERS {
            let q = Arc::clone(&q);
            consumer_handles.push(thread::spawn(move || {
                let mut taken = Vec::with_capacity(per_consumer);
                for _ in 0..per_consumer {
                    taken.push(q.get());
                }
                taken
            }));
        }

        for h in handles {
            h.join().unwrap();
        }
        let mut all = Vec::with_capacity(total);
        for h in consumer_handles {
            all.extend(h.join().unwrap());
        }
        all.sort_unstable();
        let expected: Vec<usize> = (0..total).collect();
        assert_eq!(all, expected);
        assert!(q.is_empty());
    }
}
