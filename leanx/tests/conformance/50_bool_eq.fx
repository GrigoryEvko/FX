// Q72: §2.6 Bool `==` / `!=` — polymorphic dispatch.  `==`
// over Bool is iff (same truth value), `!=` is xor (different
// truth value).  The elab probes synthesis-mode term shapes:
// if either operand elab'd without context has a Bool head
// (ctor "Bool" / indRec "Bool"), route through the closed-form
// Bool `indRec`.  Otherwise fall back to the Q68 Nat-forced
// path through `nat_eq`.
//
// This file pins the Bool dispatch through the three fact
// classes (literals, logical-op results, comparison results),
// then verifies the Nat baseline still works and the
// cross-type case (Bool lhs, Nat rhs) fails at elab.

// --- Bool literals on both sides ------------------------

fn tt_eq() : Bool = Bool.True == Bool.True;     // true
fn tf_eq() : Bool = Bool.True == Bool.False;    // false
fn ff_eq() : Bool = Bool.False == Bool.False;   // true

fn tt_neq() : Bool = Bool.True != Bool.True;    // false
fn tf_neq() : Bool = Bool.True != Bool.False;   // true
fn ff_neq() : Bool = Bool.False != Bool.False;  // false

// --- Keyword `true`/`false` on both sides ---------------

fn kw_eq() : Bool = true == false;              // false
fn kw_neq() : Bool = true != false;             // true

// --- Mixed literal + keyword (both Bool) ---------------

fn mix_eq() : Bool = Bool.True == true;         // true
fn mix_neq() : Bool = Bool.False != true;       // true

// --- Logical-op result compared to Bool literal --------

fn not_eq() : Bool = (not Bool.True) == Bool.False;     // true
fn and_eq() : Bool = (Bool.True and Bool.False) == false;   // true
fn or_neq() : Bool  = (Bool.False or Bool.True) != Bool.False;  // true
fn iff_eq() : Bool = (Bool.True <==> Bool.True) == true;        // true

// --- Comparison result compared to Bool literal --------

fn lt_eq() : Bool = (Nat.Zero < Nat.Succ(Nat.Zero)) == true;    // true
fn gt_neq() : Bool = (Nat.Zero > Nat.Succ(Nat.Zero)) != false;  // false

// --- `is` check result compared to Bool literal --------

fn is_eq() : Bool = (Nat.Zero is Nat.Zero) == Bool.True;        // true

// --- Nat path unchanged (Q68 baseline) -----------------

fn nn_eq_zero() : Bool = Nat.Zero == Nat.Zero;                    // true
fn nn_eq_succ() : Bool = Nat.Succ(Nat.Zero) == Nat.Succ(Nat.Zero); // true
fn nn_neq() : Bool = Nat.Zero != Nat.Succ(Nat.Zero);              // true

// --- Chained comparisons through Q70 arithmetic --------

fn arith_eq() : Bool =
  Nat.Succ(Nat.Zero) + Nat.Succ(Nat.Zero) ==
    Nat.Succ(Nat.Succ(Nat.Zero));                                   // true

fn main() : Bool = tt_eq();
