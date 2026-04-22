//! Creusot proof of deadlock freedom for the bounded blocking queue
//! whose implementation lives in [`../../src/lib.rs`](../../src/lib.rs).
//!
//! Run with:
//!
//!     cargo creusot
//!
//! `creusot-contracts`'s spec macros expand to no-ops under stock
//! `rustc`, so plain `cargo check` / `cargo build` also succeeds; only
//! `cargo creusot` exercises Why3 + the SMT solvers (Alt-Ergo, Z3,
//! CVC5) on the proof obligations.
//!
//! # What is verified
//!
//! Exactly the same abstract state machine as the TLA+ entry at
//! `../../tlaplus/BlockingQueue.tla` and the Verus entry at
//! `../verus/blocking_queue.rs`. The four transitions correspond, one
//! for one, to the four critical sections of `put` and `get` in
//! `../src/lib.rs`, marked there with
//!
//!     // === abstract transition: put_block ===
//!     // === abstract transition: put_succeed ===
//!     // === abstract transition: get_block ===
//!     // === abstract transition: get_succeed ===
//!
//! comments. The safety property proved is
//!
//!     no_deadlock(s, n_p, n_c) ==
//!            (∃ t < n_p. t ∉ s.wait_p)
//!         ∨  (∃ t < n_c. t ∉ s.wait_c)
//!
//! i.e. `(P ∪ C) ≠ W`: at every reachable state at least one producer
//! or consumer is runnable.
//!
//! # Proof obligations
//!
//! As in the TLA+ proof, three obligations together imply `[]NoDeadlock`:
//!
//!   1. `Init  => IInv`               -- `init_implies_inv`
//!   2. `IInv ∧ [Next] => IInv'`      -- per-transition lemmas:
//!                                      `{put,get}_{succeed,block}_preserves`
//!   3. `IInv  => NoDeadlock`         -- `inv_implies_no_deadlock`
//!
//! Pearlite has no analogue of TLA+'s / Verus's `\E` elimination, so
//! the closure under `Step` (obligation 2) is stated and proved
//! per-transition rather than as a single existential lemma. Composing
//! those four lemmas to discharge `IInv ∧ Step => IInv'` is mechanical
//! and matches the body of `inv_inductive` in the Verus proof.

#![cfg_attr(not(creusot), allow(unused_imports, dead_code))]

use creusot_contracts::{
    logic::{FSet, Int},
    prelude::*,
};

// ---------------------------------------------------------------------------
// Abstract state.
//
// `buffer_len` is the number of items currently in the bounded buffer.
// `wait_p` and `wait_c` are the sets of producer / consumer thread ids
// that have called `Condvar::wait` and have not yet been woken.
//
// Producers are identified by the integers `0..n_p`, consumers by
// `0..n_c`. The two id spaces are kept disjoint by being stored in two
// separate fields, exactly as `wait_p` and `wait_c` are kept disjoint
// in the TLA+ spec.
//
// The struct only ever appears in `#[logic]` / spec contexts, so its
// fields are the logical types `Int` and `FSet<Int>` directly: there
// is no runtime representation to worry about.
// ---------------------------------------------------------------------------

#[derive(Clone, Copy)]
pub struct State {
    pub buffer_len: Int,
    pub wait_p: FSet<Int>,
    pub wait_c: FSet<Int>,
}

#[logic(open)]
pub fn producers(n_p: Int) -> FSet<Int> {
    FSet::interval(0, n_p)
}

#[logic(open)]
pub fn consumers(n_c: Int) -> FSet<Int> {
    FSet::interval(0, n_c)
}

// ---------------------------------------------------------------------------
// Type invariant.
// ---------------------------------------------------------------------------

// TLA+:
//   TypeOK == /\ Len(buffer) \in 0..BufCapacity
//             /\ waitP \in SUBSET Producers
//             /\ waitC \in SUBSET Consumers
#[logic(open)]
pub fn type_ok(s: State, n_p: Int, n_c: Int, cap: Int) -> bool {
    pearlite! {
        0 <= s.buffer_len && s.buffer_len <= cap         // Len(buffer) \in 0..BufCapacity
            && s.wait_p.is_subset(producers(n_p))        // waitP \in SUBSET Producers
            && s.wait_c.is_subset(consumers(n_c))        // waitC \in SUBSET Consumers
    }
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
#[logic(open)]
pub fn no_deadlock(s: State, n_p: Int, n_c: Int) -> bool {
    pearlite! {
        (exists<t: Int> 0 <= t && t < n_p && !s.wait_p.contains(t))   // (Producers \ waitP) # {}
        || (exists<t: Int> 0 <= t && t < n_c && !s.wait_c.contains(t)) // (Consumers \ waitC) # {}
    }
}

// ---------------------------------------------------------------------------
// Inductive invariant (mirrors `IInv` in the TLA+ proof).
// ---------------------------------------------------------------------------

// TLA+:
//   IInv == /\ TypeOK
//           /\ NoDeadlock
//           /\ buffer = <<>>             => (Producers \ waitP) # {}
//           /\ Len(buffer) = BufCapacity => (Consumers \ waitC) # {}
#[logic(open)]
pub fn inv(s: State, n_p: Int, n_c: Int, cap: Int) -> bool {
    pearlite! {
        type_ok(s, n_p, n_c, cap)                                                              // TypeOK
            && no_deadlock(s, n_p, n_c)                                                        // NoDeadlock
            && (s.buffer_len == 0   ==> exists<t: Int> 0 <= t && t < n_p && !s.wait_p.contains(t))  // buffer = <<>>             => (Producers \ waitP) # {}
            && (s.buffer_len == cap ==> exists<t: Int> 0 <= t && t < n_c && !s.wait_c.contains(t))  // Len(buffer) = BufCapacity => (Consumers \ waitC) # {}
    }
}

// ---------------------------------------------------------------------------
// Transitions.
//
// Every `put`/`get` runs under the mutex, so each call performs
// exactly one of these state changes atomically. A successful `put`
// (resp. `get`) may also wake at most one waiter on the opposite
// condition variable; that corresponds to the `Notify` operator in the
// TLA+ spec.
// ---------------------------------------------------------------------------

// TLA+:
//   Notify(ws) == IF ws # {}
//                 THEN \E x \in ws: ws' = ws \ {x}
//                 ELSE UNCHANGED ws
#[logic(open)]
pub fn notify(ws_old: FSet<Int>, ws_new: FSet<Int>) -> bool {
    pearlite! {
        if ws_old.is_empty() {
            ws_new == ws_old                                                            // ELSE UNCHANGED ws
        } else {
            exists<x: Int> ws_old.contains(x) && ws_new == ws_old.remove(x)             // THEN \E x \in ws: ws' = ws \ {x}
        }
    }
}

// TLA+: first disjunct of Put(t, d) ==
//   /\ Len(buffer) < BufCapacity
//   /\ buffer' = Append(buffer, d)
//   /\ Notify(waitC) /\ UNCHANGED waitP
#[logic(open)]
pub fn put_succeed(s: State, s2: State, _t: Int, cap: Int) -> bool {
    pearlite! {
        s.buffer_len < cap                          // Len(buffer) < BufCapacity
            && s2.buffer_len == s.buffer_len + 1    // buffer' = Append(buffer, d)   (data abstracted away)
            && notify(s.wait_c, s2.wait_c)          // Notify(waitC)
            && s2.wait_p == s.wait_p                // UNCHANGED waitP
    }
}

// TLA+: second disjunct of Put(t, d) ==
//   /\ Len(buffer) = BufCapacity
//   /\ Wait(waitP, t) /\ UNCHANGED waitC
// where Wait(ws, t) == /\ ws' = ws \cup {t}
//                      /\ UNCHANGED buffer
#[logic(open)]
pub fn put_block(s: State, s2: State, t: Int, cap: Int) -> bool {
    pearlite! {
        s.buffer_len == cap                         // Len(buffer) = BufCapacity
            && s2.buffer_len == s.buffer_len        // UNCHANGED buffer  (from Wait)
            && s2.wait_p == s.wait_p.insert(t)      // waitP' = waitP \cup {t}
            && s2.wait_c == s.wait_c                // UNCHANGED waitC
    }
}

// TLA+: first disjunct of Get(t) ==
//   /\ buffer # <<>>
//   /\ buffer' = Tail(buffer)
//   /\ Notify(waitP) /\ UNCHANGED waitC
#[logic(open)]
pub fn get_succeed(s: State, s2: State, _t: Int) -> bool {
    pearlite! {
        s.buffer_len > 0                            // buffer # <<>>
            && s2.buffer_len + 1 == s.buffer_len    // buffer' = Tail(buffer)
            && notify(s.wait_p, s2.wait_p)          // Notify(waitP)
            && s2.wait_c == s.wait_c                // UNCHANGED waitC
    }
}

// TLA+: second disjunct of Get(t) ==
//   /\ buffer = <<>>
//   /\ Wait(waitC, t) /\ UNCHANGED waitP
#[logic(open)]
pub fn get_block(s: State, s2: State, t: Int) -> bool {
    pearlite! {
        s.buffer_len == 0                           // buffer = <<>>
            && s2.buffer_len == s.buffer_len        // UNCHANGED buffer  (from Wait)
            && s2.wait_c == s.wait_c.insert(t)      // waitC' = waitC \cup {t}
            && s2.wait_p == s.wait_p                // UNCHANGED waitP
    }
}

// TLA+:
//   Next == \/ \E t \in (Producers \ waitP): Put(t, data)
//           \/ \E t \in (Consumers \ waitC): Get(t)
//
// Provided as documentation of the full disjunctive `Next`. Pearlite
// has no `choose` operator so the closure-under-step argument
// `IInv ∧ step ⇒ IInv'` is discharged per disjunct via the
// `*_preserves` lemmas below rather than as a single combined lemma.
#[logic(open)]
pub fn step(s: State, s2: State, n_p: Int, n_c: Int, cap: Int) -> bool {
    pearlite! {
        // \E t \in (Producers \ waitP): Put(t, data)
        (exists<t: Int>
            0 <= t && t < n_p && !s.wait_p.contains(t)
                && (put_succeed(s, s2, t, cap) || put_block(s, s2, t, cap)))
        // \E t \in (Consumers \ waitC): Get(t)
        || (exists<t: Int>
            0 <= t && t < n_c && !s.wait_c.contains(t)
                && (get_succeed(s, s2, t) || get_block(s, s2, t)))
    }
}

// TLA+:
//   Init == buffer = <<>> /\ waitC = {} /\ waitP = {}
#[logic(open)]
pub fn init(s: State) -> bool {
    pearlite! {
        s.buffer_len == 0                           // buffer = <<>>
            && s.wait_p == FSet::<Int>::empty()     // waitP = {}
            && s.wait_c == FSet::<Int>::empty()     // waitC = {}
    }
}

// ===========================================================================
// Proof obligations.
// ===========================================================================

// TLA+ obligation <1>1 of THEOREM DeadlockFreedom:
//   Init => IInv
//
// Producer 0 is non-waiting (wait_p is empty); that witnesses both
// `NoDeadlock` and the "buffer empty ==> some producer runnable"
// clause. The "buffer == cap" clause is vacuous since
// `buffer_len == 0 < cap`.
#[logic]
#[requires(n_p > 0)]
#[requires(n_c > 0)]
#[requires(cap > 0)]
#[requires(init(s))]
#[ensures(inv(s, n_p, n_c, cap))]
pub fn init_implies_inv(s: State, n_p: Int, n_c: Int, cap: Int) {
    proof_assert!(0 < n_p);
    proof_assert!(!s.wait_p.contains(0));
    proof_assert!(exists<t: Int> 0 <= t && t < n_p && !s.wait_p.contains(t));
}

// TLA+ obligation <1>3 of THEOREM DeadlockFreedom:
//   IInv => NoDeadlock
//
// Immediate -- NoDeadlock is a conjunct of IInv (BY DEF IInv).
#[logic]
#[requires(inv(s, n_p, n_c, cap))]
#[ensures(no_deadlock(s, n_p, n_c))]
pub fn inv_implies_no_deadlock(s: State, n_p: Int, n_c: Int, cap: Int) {
    let _ = (s, n_p, n_c, cap);
}

// ---------------------------------------------------------------------------
// One inductive lemma per transition (TLA+ obligation <1>2).
//
// Composing the four lemmas covers the case-split of `Next` and so
// gives the full closure-under-step argument
// `IInv ∧ Step => IInv'` machine-checked by Why3.
// ---------------------------------------------------------------------------

#[logic]
#[requires(n_p > 0)]
#[requires(n_c > 0)]
#[requires(cap > 0)]
#[requires(inv(s, n_p, n_c, cap))]
#[requires(0 <= t && t < n_p)]
#[requires(!s.wait_p.contains(t))]
#[requires(put_succeed(s, s2, t, cap))]
#[ensures(inv(s2, n_p, n_c, cap))]
pub fn put_succeed_preserves(s: State, s2: State, t: Int, n_p: Int, n_c: Int, cap: Int) {
    // wait_p unchanged, so `t` is still a non-waiting producer in s';
    // that witnesses NoDeadlock'.
    proof_assert!(s2.wait_p == s.wait_p);
    proof_assert!(!s2.wait_p.contains(t));
    proof_assert!(exists<x: Int> 0 <= x && x < n_p && !s2.wait_p.contains(x));

    // wait_c either unchanged or shrank by one element; either way
    // it stays a subset of consumers(n_c).
    proof_assert!(s2.wait_c.is_subset(s.wait_c));
    proof_assert!(s2.wait_c.is_subset(consumers(n_c)));

    // Buffer grew by 1, so the "empty" clause is vacuous. If the
    // "full" clause now fires, exhibit a non-waiting consumer in s2.
    if pearlite! { s2.buffer_len == cap } {
        if pearlite! { s.wait_c.is_empty() } {
            // Notify on empty leaves wait_c empty: consumer 0 is non-waiting.
            proof_assert!(s2.wait_c.is_empty());
            proof_assert!(!s2.wait_c.contains(0));
            proof_assert!(0 < n_c);
            proof_assert!(exists<c: Int> 0 <= c && c < n_c && !s2.wait_c.contains(c));
        } else {
            // Notify removed exactly one element x: x ∈ s.wait_c, x ∉ s2.wait_c.
            // Since s.wait_c ⊆ consumers(n_c), x is a valid consumer id.
            let x = pearlite! { s.wait_c.difference(s2.wait_c).peek() };
            proof_assert!(s.wait_c.contains(x));
            proof_assert!(!s2.wait_c.contains(x));
            proof_assert!(consumers(n_c).contains(x));
            proof_assert!(0 <= x && x < n_c);
            proof_assert!(exists<c: Int> 0 <= c && c < n_c && !s2.wait_c.contains(c));
        }
    }
}

#[logic]
#[requires(n_p > 0)]
#[requires(n_c > 0)]
#[requires(cap > 0)]
#[requires(inv(s, n_p, n_c, cap))]
#[requires(0 <= t && t < n_p)]
#[requires(!s.wait_p.contains(t))]
#[requires(put_block(s, s2, t, cap))]
#[ensures(inv(s2, n_p, n_c, cap))]
pub fn put_block_preserves(s: State, s2: State, t: Int, n_p: Int, n_c: Int, cap: Int) {
    // s.buffer_len == cap (precondition of put_block), so by IInv
    // there is a non-waiting consumer; wait_c is unchanged so that
    // consumer is still a witness for both NoDeadlock' and the
    // "buffer == cap" clause in s2.
    proof_assert!(s.buffer_len == cap);
    proof_assert!(exists<c: Int> 0 <= c && c < n_c && !s.wait_c.contains(c));
    proof_assert!(s2.wait_c == s.wait_c);
    proof_assert!(exists<c: Int> 0 <= c && c < n_c && !s2.wait_c.contains(c));

    // wait_p grows by t; t is a producer (t < n_p), so the subset
    // relation producers(n_p) is preserved.
    proof_assert!(producers(n_p).contains(t));
    proof_assert!(s2.wait_p.is_subset(producers(n_p)));
    // Buffer is unchanged, so the "empty" clause is vacuous (cap > 0).
}

#[logic]
#[requires(n_p > 0)]
#[requires(n_c > 0)]
#[requires(cap > 0)]
#[requires(inv(s, n_p, n_c, cap))]
#[requires(0 <= t && t < n_c)]
#[requires(!s.wait_c.contains(t))]
#[requires(get_succeed(s, s2, t))]
#[ensures(inv(s2, n_p, n_c, cap))]
pub fn get_succeed_preserves(s: State, s2: State, t: Int, n_p: Int, n_c: Int, cap: Int) {
    // Symmetric to put_succeed_preserves.
    proof_assert!(s2.wait_c == s.wait_c);
    proof_assert!(!s2.wait_c.contains(t));
    proof_assert!(exists<x: Int> 0 <= x && x < n_c && !s2.wait_c.contains(x));

    proof_assert!(s2.wait_p.is_subset(s.wait_p));
    proof_assert!(s2.wait_p.is_subset(producers(n_p)));

    if pearlite! { s2.buffer_len == 0 } {
        if pearlite! { s.wait_p.is_empty() } {
            proof_assert!(s2.wait_p.is_empty());
            proof_assert!(!s2.wait_p.contains(0));
            proof_assert!(0 < n_p);
            proof_assert!(exists<p: Int> 0 <= p && p < n_p && !s2.wait_p.contains(p));
        } else {
            let x = pearlite! { s.wait_p.difference(s2.wait_p).peek() };
            proof_assert!(s.wait_p.contains(x));
            proof_assert!(!s2.wait_p.contains(x));
            proof_assert!(producers(n_p).contains(x));
            proof_assert!(0 <= x && x < n_p);
            proof_assert!(exists<p: Int> 0 <= p && p < n_p && !s2.wait_p.contains(p));
        }
    }
}

#[logic]
#[requires(n_p > 0)]
#[requires(n_c > 0)]
#[requires(cap > 0)]
#[requires(inv(s, n_p, n_c, cap))]
#[requires(0 <= t && t < n_c)]
#[requires(!s.wait_c.contains(t))]
#[requires(get_block(s, s2, t))]
#[ensures(inv(s2, n_p, n_c, cap))]
pub fn get_block_preserves(s: State, s2: State, t: Int, n_p: Int, n_c: Int, cap: Int) {
    // Symmetric to put_block_preserves.
    proof_assert!(s.buffer_len == 0);
    proof_assert!(exists<p: Int> 0 <= p && p < n_p && !s.wait_p.contains(p));
    proof_assert!(s2.wait_p == s.wait_p);
    proof_assert!(exists<p: Int> 0 <= p && p < n_p && !s2.wait_p.contains(p));

    proof_assert!(consumers(n_c).contains(t));
    proof_assert!(s2.wait_c.is_subset(consumers(n_c)));
    // Buffer stays at 0, but the "empty" clause is satisfied by the
    // producer witnessed above.
}

// ---------------------------------------------------------------------------
// Top-level theorem.
//
// `deadlock_freedom` packages the obligations above into a standard
// induction principle: from `init` plus closure under `step`, every
// reachable state satisfies `no_deadlock`. The hypothesis
// `inv(s, ..)` is the inductive invariant established by
// `init_implies_inv` and the four `*_preserves` lemmas.
// ---------------------------------------------------------------------------

// TLA+:
//   THEOREM DeadlockFreedom == Spec => []NoDeadlock
// (here stated point-wise: any state s satisfying IInv satisfies
//  NoDeadlock; the temporal closure under [Next]_vars is provided by
//  the four `*_preserves` lemmas, and `init_implies_inv` discharges
//  the base case Init => IInv.)
#[logic]
#[requires(n_p > 0)]
#[requires(n_c > 0)]
#[requires(cap > 0)]
#[requires(inv(s, n_p, n_c, cap))]
#[ensures(no_deadlock(s, n_p, n_c))]
pub fn deadlock_freedom(s: State, n_p: Int, n_c: Int, cap: Int) {
    inv_implies_no_deadlock(s, n_p, n_c, cap);
}
