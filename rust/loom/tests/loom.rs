//! Loom-instrumented tests for `blocking_queue::BlockingQueue<T>`.
//!
//! These complement the Verus proof in `../verus/blocking_queue.rs` by
//! exhaustively exploring concrete thread interleavings of small models
//! with loom's C11 scheduler. The Verus proof shows that the abstract
//! protocol is deadlock-free for any number of producers, consumers,
//! and capacity; the loom tests ratify that the concrete `Mutex`+`Condvar`
//! realisation in `../src/lib.rs` actually behaves like that abstract
//! protocol on the executions loom can enumerate (deadlock-free, every
//! put eventually pairs with a get, FIFO from a single producer, and so
//! on).
//!
//! Run with:
//!     RUSTFLAGS="--cfg loom" cargo test --release
//!
//! (from this folder; the `--release` flag is recommended because loom
//! enumerates a lot of interleavings).
//!
//! Models are kept tiny because loom's interleaving budget grows
//! super-exponentially with the number of threads (loom's `MAX_THREADS`
//! is small, and the test harness counts each `loom::thread::spawn`
//! plus the closure thread itself).

#![cfg(loom)]

use blocking_queue::{Arc, BlockingQueue, thread};

/// One producer + main consumer, capacity 1, single item.
///
/// Smallest non-trivial interleaving: producer may run before, during,
/// or after the consumer's `lock` / `wait` / `notify`. Loom enumerates
/// every legal scheduling and asserts no panic / no deadlock.
#[test]
fn one_producer_one_consumer_cap1_one_item() {
    loom::model(|| {
        let q: Arc<BlockingQueue<u32>> = Arc::new(BlockingQueue::new(1));
        let q2 = Arc::clone(&q);

        let p = thread::spawn(move || {
            q2.put(42);
        });

        assert_eq!(q.get(), 42);
        p.join().unwrap();
    });
}

/// One producer pushes two items through a capacity-1 queue.
///
/// Forces the producer to block on `not_full` at least once and be
/// woken by the consumer's `notify_one`. Catches lost-wakeup-style
/// bugs: if `put` notified the wrong condvar (or none), the producer
/// would block forever and loom would report a deadlock.
#[test]
fn one_producer_one_consumer_cap1_two_items() {
    loom::model(|| {
        let q: Arc<BlockingQueue<u32>> = Arc::new(BlockingQueue::new(1));
        let q2 = Arc::clone(&q);

        let p = thread::spawn(move || {
            q2.put(1);
            q2.put(2);
        });

        // The order is fixed because there is only one producer.
        assert_eq!(q.get(), 1);
        assert_eq!(q.get(), 2);
        p.join().unwrap();
    });
}

/// Two producers + main consumer, capacity 1.
///
/// Three threads total (main + 2 spawned), within loom's budget.
/// Both producers race for the single buffer slot; the consumer drains
/// both items. Asserts the multiset of items received matches what was
/// produced — exposes any bug where a `notify_one` woke the wrong
/// waiter and a producer was lost.
#[test]
fn two_producers_one_consumer_cap1() {
    loom::model(|| {
        let q: Arc<BlockingQueue<u32>> = Arc::new(BlockingQueue::new(1));
        let q1 = Arc::clone(&q);
        let q2 = Arc::clone(&q);

        let h1 = thread::spawn(move || q1.put(1));
        let h2 = thread::spawn(move || q2.put(2));

        let a = q.get();
        let b = q.get();

        h1.join().unwrap();
        h2.join().unwrap();

        let mut got = [a, b];
        got.sort();
        assert_eq!(got, [1, 2]);
    });
}

/// One producer + one consumer in spawned threads + main does nothing.
/// Capacity 2, three items.
///
/// Exercises the case where the producer may briefly fill the buffer
/// (capacity reached) and then block in `put`, requiring the consumer's
/// `notify_one` on `not_full` to make progress.
#[test]
fn one_producer_one_consumer_cap2_three_items() {
    loom::model(|| {
        let q: Arc<BlockingQueue<u32>> = Arc::new(BlockingQueue::new(2));
        let qp = Arc::clone(&q);
        let qc = Arc::clone(&q);

        let p = thread::spawn(move || {
            qp.put(1);
            qp.put(2);
            qp.put(3);
        });

        let c = thread::spawn(move || {
            let a = qc.get();
            let b = qc.get();
            let c = qc.get();
            (a, b, c)
        });

        p.join().unwrap();
        let (a, b, c) = c.join().unwrap();
        // Single producer => FIFO order is preserved on the consumer side.
        assert_eq!((a, b, c), (1, 2, 3));
    });
}
