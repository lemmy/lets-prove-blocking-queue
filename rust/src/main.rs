//! Demo binary: spins up two producers and two consumers around a
//! capacity-3 `BlockingQueue<(usize, usize)>` and prints what each
//! thread does. The actual demo loop lives in `blocking_queue::run_demo`
//! so it can stay close to the implementation it exercises.

#[cfg(not(loom))]
fn main() {
    blocking_queue::run_demo();
}

// Stub `main` so the bin still compiles under `--cfg loom`. Loom tests
// live in `../loom/tests/loom.rs` and never invoke this binary.
#[cfg(loom)]
fn main() {}
