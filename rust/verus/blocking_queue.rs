//! Verus-checked proof that the bounded blocking queue in
//! [`../src/lib.rs`](../src/lib.rs) implements a deadlock-free protocol.
//!
//! Run with:
//!
//!     verus blocking_queue.rs
//!
//! There is no `Cargo.toml` in this folder: Verus is invoked directly
//! on this source file. The implementation it refers to is pulled in
//! via `#[path]` so the proof and the code it verifies are processed
//! together. Every item in `../src/lib.rs` is annotated
//! `#[cfg_attr(verus_keep_ghost, verifier::external)]`, so Verus parses
//! the implementation but does not try to verify the standard-library
//! code directly — it has no model for `std::sync::{Mutex, Condvar}`.
//!
//! What is verified is the abstract state machine in the `proof`
//! module below. Its four transitions correspond, one for one, to the
//! four critical sections of `put` and `get` in `../src/lib.rs`,
//! marked there with
//!
//!     // === abstract transition: put_block ===
//!     // === abstract transition: put_succeed ===
//!     // === abstract transition: get_block ===
//!     // === abstract transition: get_succeed ===
//!
//! comments. The safety property proved is the same one stated in the
//! repository's top-level README and proved in the TLA+ entry at
//! `../../tlaplus/BlockingQueue.tla`:
//!
//!     no_deadlock(s, n_p, n_c) ==
//!            (∃ t < n_p. t ∉ s.wait_p)
//!         ∨  (∃ t < n_c. t ∉ s.wait_c)
//!
//! i.e. `(P ∪ C) ≠ W`: at every reachable state at least one producer
//! or consumer is runnable.

// Pull the implementation in side-by-side with the proof. Verus
// follows the `#[path]` like rustc and parses `../src/lib.rs`; the
// `#[cfg_attr(verus_keep_ghost, verifier::external)]` annotations on
// the items inside that file ensure the implementation is treated as
// an external (un-verified) reference.
#[path = "../src/lib.rs"]
#[allow(dead_code)]
mod blocking_queue;

// Verus invokes rustc on this file as a binary crate, so it requires a
// `main` symbol. The actual program's `main` lives in `../src/main.rs`
// (used by `cargo run`); here we just provide a no-op stub so Verus
// can compile-and-verify the file standalone.
#[cfg_attr(verus_keep_ghost, verifier::external)]
fn main() {}

// ===========================================================================
// Verus proof of deadlock freedom.
// ===========================================================================
//
// The proof follows the recipe of the TLA+ proof in
// `../../tlaplus/BlockingQueue.tla`:
//
//   1. Define an abstract state machine whose transitions correspond, one
//      for one, to the four critical sections a producer or consumer can
//      execute while it holds the queue's mutex (a successful or blocking
//      `put`/`get`) — see `../src/lib.rs`.
//   2. State the safety invariant `NoDeadlock`: the union of waiting
//      producers and consumers never equals the entire population of
//      threads.
//   3. Strengthen it with two "meat" clauses (empty buffer => some
//      producer is runnable, full buffer => some consumer is runnable)
//      so that the conjunction is inductive.
//   4. Discharge the three obligations machine-checked by Verus:
//        Init  ==> IInv
//        IInv /\ Step ==> IInv'
//        IInv  ==> NoDeadlock
//
// The whole module is gated on `#[cfg(verus_keep_ghost)]`, the cfg that
// Verus sets when running. Plain `cargo` / `rustc` does not see it, so
// this file remains compilable by stock rustc as well (modulo the
// `verifier::external` attribute, which is itself behind that cfg).

#[cfg(verus_keep_ghost)]
mod proof {

use vstd::prelude::*;
use vstd::set::*;

verus! {

broadcast use group_set_axioms;

// ---------------------------------------------------------------------------
// Abstract state.
//
// `buffer_len` is the number of items currently in the bounded buffer.
// `wait_p` and `wait_c` are the sets of producer / consumer thread ids that
// have called `Condvar::wait` and have not yet been woken.
//
// Producers are identified by the naturals `0 .. n_p`, consumers by
// `0 .. n_c`. The two id spaces are kept disjoint by being stored in two
// separate fields, exactly as `wait_p` and `wait_c` are kept disjoint in the
// TLA+ spec.
// ---------------------------------------------------------------------------

pub struct State {
    pub buffer_len: nat,
    pub wait_p: Set<nat>,
    pub wait_c: Set<nat>,
}

pub open spec fn producers(n_p: nat) -> Set<nat> {
    Set::new(|i: nat| i < n_p)
}

pub open spec fn consumers(n_c: nat) -> Set<nat> {
    Set::new(|i: nat| i < n_c)
}

// ---------------------------------------------------------------------------
// Type invariant.
// ---------------------------------------------------------------------------

// TLA+:
//   TypeOK == /\ Len(buffer) \in 0..BufCapacity
//             /\ waitP \in SUBSET Producers
//             /\ waitC \in SUBSET Consumers
pub open spec fn type_ok(s: State, n_p: nat, n_c: nat, cap: nat) -> bool {
    &&& s.buffer_len <= cap                       // Len(buffer) \in 0..BufCapacity
    &&& s.wait_p.subset_of(producers(n_p))        // waitP \in SUBSET Producers
    &&& s.wait_c.subset_of(consumers(n_c))        // waitC \in SUBSET Consumers
}

// ---------------------------------------------------------------------------
// The deadlock-freedom safety property.
//
// In the TLA+ spec this is `(waitC \cup waitP) # (Producers \cup Consumers)`,
// equivalently: at least one producer or one consumer is not currently
// waiting.
// ---------------------------------------------------------------------------

// TLA+:
//   NoDeadlock == (waitC \cup waitP) # (Producers \cup Consumers)
// Equivalently (and how it is encoded here):
//   (Producers \ waitP) # {} \/ (Consumers \ waitC) # {}
pub open spec fn no_deadlock(s: State, n_p: nat, n_c: nat) -> bool {
    ||| (exists|t: nat| t < n_p && !s.wait_p.contains(t))   // (Producers \ waitP) # {}
    ||| (exists|t: nat| t < n_c && !s.wait_c.contains(t))   // (Consumers \ waitC) # {}
}

// ---------------------------------------------------------------------------
// Inductive invariant (mirrors `IInv` in the TLA+ proof).
// ---------------------------------------------------------------------------

// TLA+:
//   IInv == /\ TypeOK
//           /\ NoDeadlock
//           /\ buffer = <<>>             => (Producers \ waitP) # {}
//           /\ Len(buffer) = BufCapacity => (Consumers \ waitC) # {}
pub open spec fn inv(s: State, n_p: nat, n_c: nat, cap: nat) -> bool {
    &&& type_ok(s, n_p, n_c, cap)                                                       // TypeOK
    &&& no_deadlock(s, n_p, n_c)                                                        // NoDeadlock
    &&& (s.buffer_len == 0 ==> exists|t: nat| t < n_p && !s.wait_p.contains(t))         // buffer = <<>>             => (Producers \ waitP) # {}
    &&& (s.buffer_len == cap ==> exists|t: nat| t < n_c && !s.wait_c.contains(t))       // Len(buffer) = BufCapacity => (Consumers \ waitC) # {}
}

// ---------------------------------------------------------------------------
// Transitions.
//
// Every `put`/`get` runs under the mutex, so each call performs exactly one
// of these state changes atomically. A successful `put` (resp. `get`) may
// also wake at most one waiter on the opposite condition variable; that
// corresponds to the `Notify` operator in the TLA+ spec.
// ---------------------------------------------------------------------------

// TLA+:
//   Notify(ws) == IF ws # {}
//                 THEN \E x \in ws: ws' = ws \ {x}
//                 ELSE UNCHANGED ws
pub open spec fn notify(ws_old: Set<nat>, ws_new: Set<nat>) -> bool {
    if ws_old =~= Set::<nat>::empty() {
        ws_new =~= ws_old                                                       // ELSE UNCHANGED ws
    } else {
        exists|x: nat| ws_old.contains(x) && ws_new =~= ws_old.remove(x)        // THEN \E x \in ws: ws' = ws \ {x}
    }
}

// TLA+: first disjunct of Put(t, d) ==
//   /\ Len(buffer) < BufCapacity
//   /\ buffer' = Append(buffer, d)
//   /\ Notify(waitC) /\ UNCHANGED waitP
pub open spec fn put_succeed(s: State, s2: State, _t: nat, cap: nat) -> bool {
    &&& s.buffer_len < cap                          // Len(buffer) < BufCapacity
    &&& s2.buffer_len == s.buffer_len + 1           // buffer' = Append(buffer, d)   (data abstracted away)
    &&& notify(s.wait_c, s2.wait_c)                 // Notify(waitC)
    &&& s2.wait_p =~= s.wait_p                      // UNCHANGED waitP
}

// TLA+: second disjunct of Put(t, d) ==
//   /\ Len(buffer) = BufCapacity
//   /\ Wait(waitP, t) /\ UNCHANGED waitC
// where Wait(ws, t) == /\ ws' = ws \cup {t}
//                      /\ UNCHANGED buffer
pub open spec fn put_block(s: State, s2: State, t: nat, cap: nat) -> bool {
    &&& s.buffer_len == cap                         // Len(buffer) = BufCapacity
    &&& s2.buffer_len == s.buffer_len               // UNCHANGED buffer  (from Wait)
    &&& s2.wait_p =~= s.wait_p.insert(t)            // waitP' = waitP \cup {t}
    &&& s2.wait_c =~= s.wait_c                      // UNCHANGED waitC
}

// TLA+: first disjunct of Get(t) ==
//   /\ buffer # <<>>
//   /\ buffer' = Tail(buffer)
//   /\ Notify(waitP) /\ UNCHANGED waitC
pub open spec fn get_succeed(s: State, s2: State, _t: nat) -> bool {
    &&& s.buffer_len > 0                            // buffer # <<>>
    &&& s2.buffer_len + 1 == s.buffer_len           // buffer' = Tail(buffer)
    &&& notify(s.wait_p, s2.wait_p)                 // Notify(waitP)
    &&& s2.wait_c =~= s.wait_c                      // UNCHANGED waitC
}

// TLA+: second disjunct of Get(t) ==
//   /\ buffer = <<>>
//   /\ Wait(waitC, t) /\ UNCHANGED waitP
pub open spec fn get_block(s: State, s2: State, t: nat) -> bool {
    &&& s.buffer_len == 0                           // buffer = <<>>
    &&& s2.buffer_len == s.buffer_len               // UNCHANGED buffer  (from Wait)
    &&& s2.wait_c =~= s.wait_c.insert(t)            // waitC' = waitC \cup {t}
    &&& s2.wait_p =~= s.wait_p                      // UNCHANGED waitP
}

// TLA+:
//   Next == \/ \E t \in (Producers \ waitP): Put(t, data)
//           \/ \E t \in (Consumers \ waitC): Get(t)
pub open spec fn step(s: State, s2: State, n_p: nat, n_c: nat, cap: nat) -> bool {
    // \E t \in (Producers \ waitP): Put(t, data)
    ||| exists|t: nat| #![auto]
            t < n_p && !s.wait_p.contains(t)
                && (put_succeed(s, s2, t, cap) || put_block(s, s2, t, cap))
    // \E t \in (Consumers \ waitC): Get(t)
    ||| exists|t: nat| #![auto]
            t < n_c && !s.wait_c.contains(t)
                && (get_succeed(s, s2, t) || get_block(s, s2, t))
}

// TLA+:
//   Init == buffer = <<>> /\ waitC = {} /\ waitP = {}
pub open spec fn init(s: State) -> bool {
    &&& s.buffer_len == 0                       // buffer = <<>>
    &&& s.wait_p =~= Set::<nat>::empty()        // waitP = {}
    &&& s.wait_c =~= Set::<nat>::empty()        // waitC = {}
}

// ---------------------------------------------------------------------------
// Proof obligations.
// ---------------------------------------------------------------------------

// TLA+ obligation <1>1 of THEOREM DeadlockFreedom:
//   Init => IInv
proof fn init_implies_inv(s: State, n_p: nat, n_c: nat, cap: nat)
    requires
        n_p > 0,
        n_c > 0,
        cap > 0,
        init(s),
    ensures
        inv(s, n_p, n_c, cap),
{
    // Producer 0 is non-waiting; that witnesses both NoDeadlock and the
    // "buffer empty ==> some producer runnable" clause.
    assert(0nat < n_p);
    assert(!s.wait_p.contains(0nat));
    assert(exists|t: nat| t < n_p && !s.wait_p.contains(t)) by {
        assert(0nat < n_p && !s.wait_p.contains(0nat));
    }
    // The "buffer == cap" clause is vacuous since buffer_len == 0 < cap.
}

// TLA+ obligation <1>2 of THEOREM DeadlockFreedom:
//   IInv /\ [Next]_vars => IInv'
// Verus discharges the stuttering case s2 = s automatically by the
// per-transition lemmas; the exists-disjunction below mirrors the
// TLA+ case-split  Next == \E t ...: Put(t, _) \/ \E t ...: Get(t).
proof fn inv_inductive(s: State, s2: State, n_p: nat, n_c: nat, cap: nat)
    requires
        n_p > 0,
        n_c > 0,
        cap > 0,
        inv(s, n_p, n_c, cap),
        step(s, s2, n_p, n_c, cap),
    ensures
        inv(s2, n_p, n_c, cap),
{
    // Case-split on which transition fired.
    if exists|t: nat| #![auto]
        t < n_p && !s.wait_p.contains(t)
            && (put_succeed(s, s2, t, cap) || put_block(s, s2, t, cap))
    {
        let t = choose|t: nat| #![auto]
            t < n_p && !s.wait_p.contains(t)
                && (put_succeed(s, s2, t, cap) || put_block(s, s2, t, cap));
        if put_succeed(s, s2, t, cap) {
            put_succeed_preserves(s, s2, t, n_p, n_c, cap);
        } else {
            put_block_preserves(s, s2, t, n_p, n_c, cap);
        }
    } else {
        let t = choose|t: nat| #![auto]
            t < n_c && !s.wait_c.contains(t)
                && (get_succeed(s, s2, t) || get_block(s, s2, t));
        assert(t < n_c && !s.wait_c.contains(t)
            && (get_succeed(s, s2, t) || get_block(s, s2, t)));
        if get_succeed(s, s2, t) {
            get_succeed_preserves(s, s2, t, n_p, n_c, cap);
        } else {
            get_block_preserves(s, s2, t, n_p, n_c, cap);
        }
    }
}

// TLA+ obligation <1>3 of THEOREM DeadlockFreedom:
//   IInv => NoDeadlock
// Immediate -- NoDeadlock is a conjunct of IInv (BY DEF IInv).
proof fn inv_implies_no_deadlock(s: State, n_p: nat, n_c: nat, cap: nat)
    requires
        inv(s, n_p, n_c, cap),
    ensures
        no_deadlock(s, n_p, n_c),
{}

// ---------------------------------------------------------------------------
// One inductive lemma per transition.
// ---------------------------------------------------------------------------

proof fn put_succeed_preserves(
    s: State,
    s2: State,
    t: nat,
    n_p: nat,
    n_c: nat,
    cap: nat,
)
    requires
        n_p > 0,
        n_c > 0,
        cap > 0,
        inv(s, n_p, n_c, cap),
        t < n_p,
        !s.wait_p.contains(t),
        put_succeed(s, s2, t, cap),
    ensures
        inv(s2, n_p, n_c, cap),
{
    // wait_p is unchanged, so subset_of and "t is a non-waiting producer in s'"
    // both still hold; t witnesses NoDeadlock'.
    assert(s2.wait_p =~= s.wait_p);
    assert(!s2.wait_p.contains(t));
    assert(exists|t: nat| t < n_p && !s2.wait_p.contains(t)) by {
        assert(t < n_p && !s2.wait_p.contains(t));
    }

    // wait_c either unchanged or shrank by one element, so it stays a subset
    // of consumers(n_c).
    assert(s2.wait_c.subset_of(consumers(n_c))) by {
        if s.wait_c =~= Set::<nat>::empty() {
            assert(s2.wait_c =~= s.wait_c);
        } else {
            let x = choose|x: nat|
                s.wait_c.contains(x) && s2.wait_c =~= s.wait_c.remove(x);
            assert(s.wait_c.contains(x) && s2.wait_c =~= s.wait_c.remove(x));
            assert forall|y: nat| s2.wait_c.contains(y) implies #[trigger] consumers(n_c).contains(y) by {
                assert(s.wait_c.contains(y));
            };
        }
    }

    // Buffer grew by 1, so the "empty" clause is vacuous. Establish the
    // "full" clause if buffer_len' == cap.
    if s2.buffer_len == cap {
        // Some consumer must be non-waiting in s'.
        if s.wait_c =~= Set::<nat>::empty() {
            assert(0nat < n_c);
            assert(!s2.wait_c.contains(0nat));
            assert(exists|c: nat| c < n_c && !s2.wait_c.contains(c)) by {
                assert(0nat < n_c && !s2.wait_c.contains(0nat));
            }
        } else {
            let x = choose|x: nat|
                s.wait_c.contains(x) && s2.wait_c =~= s.wait_c.remove(x);
            assert(s.wait_c.contains(x) && s2.wait_c =~= s.wait_c.remove(x));
            // x was a consumer (wait_c was a subset of consumers).
            assert(consumers(n_c).contains(x));
            assert(x < n_c);
            assert(!s2.wait_c.contains(x));
            assert(exists|c: nat| c < n_c && !s2.wait_c.contains(c)) by {
                assert(x < n_c && !s2.wait_c.contains(x));
            }
        }
    }
}

proof fn put_block_preserves(
    s: State,
    s2: State,
    t: nat,
    n_p: nat,
    n_c: nat,
    cap: nat,
)
    requires
        n_p > 0,
        n_c > 0,
        cap > 0,
        inv(s, n_p, n_c, cap),
        t < n_p,
        !s.wait_p.contains(t),
        put_block(s, s2, t, cap),
    ensures
        inv(s2, n_p, n_c, cap),
{
    // s.buffer_len == cap, so by IInv there is a non-waiting consumer; that
    // consumer is still non-waiting in s' (wait_c unchanged) and witnesses
    // both NoDeadlock' and the "buffer == cap" clause.
    assert(s.buffer_len == cap);
    let c = choose|c: nat| c < n_c && !s.wait_c.contains(c);
    assert(c < n_c && !s.wait_c.contains(c));
    assert(s2.wait_c =~= s.wait_c);
    assert(!s2.wait_c.contains(c));
    assert(exists|c: nat| c < n_c && !s2.wait_c.contains(c)) by {
        assert(c < n_c && !s2.wait_c.contains(c));
    }
    // wait_p grows by t; t is a producer, so the subset relation is kept.
    assert(s2.wait_p.subset_of(producers(n_p))) by {
        assert(producers(n_p).contains(t));
        assert forall|y: nat| s2.wait_p.contains(y) implies #[trigger] producers(n_p).contains(y) by {
            if y == t {
            } else {
                assert(s.wait_p.contains(y));
            }
        };
    }
    // Buffer is unchanged, so the "empty" clause is vacuous (cap > 0).
}

proof fn get_succeed_preserves(
    s: State,
    s2: State,
    t: nat,
    n_p: nat,
    n_c: nat,
    cap: nat,
)
    requires
        n_p > 0,
        n_c > 0,
        cap > 0,
        inv(s, n_p, n_c, cap),
        t < n_c,
        !s.wait_c.contains(t),
        get_succeed(s, s2, t),
    ensures
        inv(s2, n_p, n_c, cap),
{
    // Symmetric to put_succeed.
    assert(s2.wait_c =~= s.wait_c);
    assert(!s2.wait_c.contains(t));
    assert(exists|c: nat| c < n_c && !s2.wait_c.contains(c)) by {
        assert(t < n_c && !s2.wait_c.contains(t));
    }
    assert(s2.wait_p.subset_of(producers(n_p))) by {
        if s.wait_p =~= Set::<nat>::empty() {
            assert(s2.wait_p =~= s.wait_p);
        } else {
            let x = choose|x: nat|
                s.wait_p.contains(x) && s2.wait_p =~= s.wait_p.remove(x);
            assert(s.wait_p.contains(x) && s2.wait_p =~= s.wait_p.remove(x));
            assert forall|y: nat| s2.wait_p.contains(y) implies #[trigger] producers(n_p).contains(y) by {
                assert(s.wait_p.contains(y));
            };
        }
    }
    if s2.buffer_len == 0 {
        if s.wait_p =~= Set::<nat>::empty() {
            assert(0nat < n_p);
            assert(!s2.wait_p.contains(0nat));
            assert(exists|p: nat| p < n_p && !s2.wait_p.contains(p)) by {
                assert(0nat < n_p && !s2.wait_p.contains(0nat));
            }
        } else {
            let x = choose|x: nat|
                s.wait_p.contains(x) && s2.wait_p =~= s.wait_p.remove(x);
            assert(s.wait_p.contains(x) && s2.wait_p =~= s.wait_p.remove(x));
            assert(producers(n_p).contains(x));
            assert(x < n_p);
            assert(!s2.wait_p.contains(x));
            assert(exists|p: nat| p < n_p && !s2.wait_p.contains(p)) by {
                assert(x < n_p && !s2.wait_p.contains(x));
            }
        }
    }
}

proof fn get_block_preserves(
    s: State,
    s2: State,
    t: nat,
    n_p: nat,
    n_c: nat,
    cap: nat,
)
    requires
        n_p > 0,
        n_c > 0,
        cap > 0,
        inv(s, n_p, n_c, cap),
        t < n_c,
        !s.wait_c.contains(t),
        get_block(s, s2, t),
    ensures
        inv(s2, n_p, n_c, cap),
{
    // Symmetric to put_block.
    assert(s.buffer_len == 0);
    let p = choose|p: nat| p < n_p && !s.wait_p.contains(p);
    assert(p < n_p && !s.wait_p.contains(p));
    assert(s2.wait_p =~= s.wait_p);
    assert(!s2.wait_p.contains(p));
    assert(exists|p: nat| p < n_p && !s2.wait_p.contains(p)) by {
        assert(p < n_p && !s2.wait_p.contains(p));
    }
    assert(s2.wait_c.subset_of(consumers(n_c))) by {
        assert(consumers(n_c).contains(t));
        assert forall|y: nat| s2.wait_c.contains(y) implies #[trigger] consumers(n_c).contains(y) by {
            if y == t {
            } else {
                assert(s.wait_c.contains(y));
            }
        };
    }
}

// ---------------------------------------------------------------------------
// Top-level theorem.
//
// `deadlock_freedom` packages the three obligations above into a standard
// induction principle: from `init` plus closure under `step`, every state
// satisfies `no_deadlock`. The hypothesis `inv(s, ..)` is the inductive
// invariant established by `init_implies_inv` and `inv_inductive`.
// ---------------------------------------------------------------------------

// TLA+:
//   THEOREM DeadlockFreedom == Spec => []IInv
// (here stated point-wise: any state s satisfying IInv satisfies NoDeadlock;
//  the temporal closure under [Next]_vars is provided by `inv_inductive`,
//  and `init_implies_inv` discharges the base case Init => IInv.)
pub proof fn deadlock_freedom(s: State, n_p: nat, n_c: nat, cap: nat)
    requires
        n_p > 0,
        n_c > 0,
        cap > 0,
        inv(s, n_p, n_c, cap),
    ensures
        no_deadlock(s, n_p, n_c),
{
    inv_implies_no_deadlock(s, n_p, n_c, cap);
}

} // verus!

} // mod proof
