import LeanFX2.Graded.Semiring

/-! # Graded/Instances/Mutation — mutation lattice (4-chain)
`immutable < appendOnly < monotonic < readWrite`

Four-element mutation lattice for tracking how a binding may
change.  Encoded as a totally-ordered chain (distributive lattice):

* `+` = `max` (lattice join)        — combining yields the
                                       most-permissive direction
* `*` = `min` (lattice meet)        — scaling annihilates with `0`
* `0` = `immutable`                 — additive identity, lattice bottom
* `1` = `readWrite`                 — multiplicative identity, top
* `≤` = chain order                 — lower-mutability fits where
                                       higher expected (subsumption)

Per `fx_design.md` §6.3 dim 18 / §1.1: default is `immutable`.
The `appendOnly`, `monotonic`, and `readWrite` ranks unlock
progressively more mutability:

* `immutable`     — no mutation; default; initialized once
* `appendOnly`    — may add to tail (e.g., log buffer, queue)
* `monotonic`     — may change forward in declared partial order
                    (e.g., counter increments, gauge ratchets)
* `readWrite`     — any mutation (the unrestricted case)

## Why a chain (not a lattice with incomparable elements)

The mutation hierarchy is monotonically permissive — each rank
strictly subsumes the prior.  An `appendOnly` reference is a strict
specialization of `readWrite`, etc.  This makes the order total
(linear); chains are distributive lattices and satisfy every
GradeSemiring law.

## Cross-dimension interactions

* `monotonic × concurrent`         — soundness collision: if many
  threads ratchet, monotonic order reads must be acquire-loads
* `readWrite × shared`             — borrow checker requires
  exclusive access (`ref mut`); compile-time enforced

## Surface mode mapping

* default                          → `immutable`
* `let counter = ref(...)`         → `readWrite`
* `let log = ref append(...)`      → `appendOnly`
* `@[monotonic] let gauge = ...`   → `monotonic`

## Dependencies

* `Graded/Semiring.lean`

## Downstream

* `Graded/Rules.lean` — mutation tracked through ref operations
* `fx_design.md` §6.3 dim 18, §7.1 mode system

Zero-axiom verified per declaration.
-/

namespace LeanFX2.Graded.Instances

open LeanFX2.Graded

/-- Mutation grade: 4-chain `immutable < appendOnly < monotonic <
readWrite`.  Closed enum.  Values are listed in chain order so
addition (max) and multiplication (min) tables read top-down. -/
inductive MutationGrade : Type
  /-- Immutable; lattice bottom; default. -/
  | immutable
  /-- May add to tail. -/
  | appendOnly
  /-- May change forward in declared partial order. -/
  | monotonic
  /-- Any mutation; lattice top. -/
  | readWrite
  deriving DecidableEq, Repr

namespace MutationGrade

/-- Combining (parallel) is lattice max — full 16-case enumeration
of the chain max table. -/
def add : MutationGrade → MutationGrade → MutationGrade
  | .immutable,  .immutable  => .immutable
  | .immutable,  .appendOnly => .appendOnly
  | .immutable,  .monotonic  => .monotonic
  | .immutable,  .readWrite  => .readWrite
  | .appendOnly, .immutable  => .appendOnly
  | .appendOnly, .appendOnly => .appendOnly
  | .appendOnly, .monotonic  => .monotonic
  | .appendOnly, .readWrite  => .readWrite
  | .monotonic,  .immutable  => .monotonic
  | .monotonic,  .appendOnly => .monotonic
  | .monotonic,  .monotonic  => .monotonic
  | .monotonic,  .readWrite  => .readWrite
  | .readWrite,  .immutable  => .readWrite
  | .readWrite,  .appendOnly => .readWrite
  | .readWrite,  .monotonic  => .readWrite
  | .readWrite,  .readWrite  => .readWrite

/-- Scaling (sequential) is lattice min — annihilates with
`immutable`. -/
def mul : MutationGrade → MutationGrade → MutationGrade
  | .immutable,  _            => .immutable
  | .appendOnly, .immutable   => .immutable
  | .appendOnly, .appendOnly  => .appendOnly
  | .appendOnly, .monotonic   => .appendOnly
  | .appendOnly, .readWrite   => .appendOnly
  | .monotonic,  .immutable   => .immutable
  | .monotonic,  .appendOnly  => .appendOnly
  | .monotonic,  .monotonic   => .monotonic
  | .monotonic,  .readWrite   => .monotonic
  | .readWrite,  .immutable   => .immutable
  | .readWrite,  .appendOnly  => .appendOnly
  | .readWrite,  .monotonic   => .monotonic
  | .readWrite,  .readWrite   => .readWrite

/-- Subsumption preorder: chain order.  Full 16-case enumeration to
avoid propext leak from wildcards on a 4-element inductive (per
`feedback_lean_zero_axiom_match.md` guidance). -/
def le : MutationGrade → MutationGrade → Prop
  | .immutable,  .immutable   => True
  | .immutable,  .appendOnly  => True
  | .immutable,  .monotonic   => True
  | .immutable,  .readWrite   => True
  | .appendOnly, .immutable   => False
  | .appendOnly, .appendOnly  => True
  | .appendOnly, .monotonic   => True
  | .appendOnly, .readWrite   => True
  | .monotonic,  .immutable   => False
  | .monotonic,  .appendOnly  => False
  | .monotonic,  .monotonic   => True
  | .monotonic,  .readWrite   => True
  | .readWrite,  .immutable   => False
  | .readWrite,  .appendOnly  => False
  | .readWrite,  .monotonic   => False
  | .readWrite,  .readWrite   => True

end MutationGrade

/-- The mutation 4-chain Boolean-algebra-like semiring.  All 17
algebra/preorder laws discharged by full case enumeration over the
non-indexed 4-element inductive — no `decide`, no tactics that risk
axiom emission. -/
instance : GradeSemiring MutationGrade where
  zero := .immutable
  one  := .readWrite
  add  := MutationGrade.add
  mul  := MutationGrade.mul
  le   := MutationGrade.le

  add_assoc := fun first second third => match first, second, third with
    | .immutable,  .immutable,  .immutable  => rfl
    | .immutable,  .immutable,  .appendOnly => rfl
    | .immutable,  .immutable,  .monotonic  => rfl
    | .immutable,  .immutable,  .readWrite  => rfl
    | .immutable,  .appendOnly, .immutable  => rfl
    | .immutable,  .appendOnly, .appendOnly => rfl
    | .immutable,  .appendOnly, .monotonic  => rfl
    | .immutable,  .appendOnly, .readWrite  => rfl
    | .immutable,  .monotonic,  .immutable  => rfl
    | .immutable,  .monotonic,  .appendOnly => rfl
    | .immutable,  .monotonic,  .monotonic  => rfl
    | .immutable,  .monotonic,  .readWrite  => rfl
    | .immutable,  .readWrite,  .immutable  => rfl
    | .immutable,  .readWrite,  .appendOnly => rfl
    | .immutable,  .readWrite,  .monotonic  => rfl
    | .immutable,  .readWrite,  .readWrite  => rfl
    | .appendOnly, .immutable,  .immutable  => rfl
    | .appendOnly, .immutable,  .appendOnly => rfl
    | .appendOnly, .immutable,  .monotonic  => rfl
    | .appendOnly, .immutable,  .readWrite  => rfl
    | .appendOnly, .appendOnly, .immutable  => rfl
    | .appendOnly, .appendOnly, .appendOnly => rfl
    | .appendOnly, .appendOnly, .monotonic  => rfl
    | .appendOnly, .appendOnly, .readWrite  => rfl
    | .appendOnly, .monotonic,  .immutable  => rfl
    | .appendOnly, .monotonic,  .appendOnly => rfl
    | .appendOnly, .monotonic,  .monotonic  => rfl
    | .appendOnly, .monotonic,  .readWrite  => rfl
    | .appendOnly, .readWrite,  .immutable  => rfl
    | .appendOnly, .readWrite,  .appendOnly => rfl
    | .appendOnly, .readWrite,  .monotonic  => rfl
    | .appendOnly, .readWrite,  .readWrite  => rfl
    | .monotonic,  .immutable,  .immutable  => rfl
    | .monotonic,  .immutable,  .appendOnly => rfl
    | .monotonic,  .immutable,  .monotonic  => rfl
    | .monotonic,  .immutable,  .readWrite  => rfl
    | .monotonic,  .appendOnly, .immutable  => rfl
    | .monotonic,  .appendOnly, .appendOnly => rfl
    | .monotonic,  .appendOnly, .monotonic  => rfl
    | .monotonic,  .appendOnly, .readWrite  => rfl
    | .monotonic,  .monotonic,  .immutable  => rfl
    | .monotonic,  .monotonic,  .appendOnly => rfl
    | .monotonic,  .monotonic,  .monotonic  => rfl
    | .monotonic,  .monotonic,  .readWrite  => rfl
    | .monotonic,  .readWrite,  .immutable  => rfl
    | .monotonic,  .readWrite,  .appendOnly => rfl
    | .monotonic,  .readWrite,  .monotonic  => rfl
    | .monotonic,  .readWrite,  .readWrite  => rfl
    | .readWrite,  .immutable,  .immutable  => rfl
    | .readWrite,  .immutable,  .appendOnly => rfl
    | .readWrite,  .immutable,  .monotonic  => rfl
    | .readWrite,  .immutable,  .readWrite  => rfl
    | .readWrite,  .appendOnly, .immutable  => rfl
    | .readWrite,  .appendOnly, .appendOnly => rfl
    | .readWrite,  .appendOnly, .monotonic  => rfl
    | .readWrite,  .appendOnly, .readWrite  => rfl
    | .readWrite,  .monotonic,  .immutable  => rfl
    | .readWrite,  .monotonic,  .appendOnly => rfl
    | .readWrite,  .monotonic,  .monotonic  => rfl
    | .readWrite,  .monotonic,  .readWrite  => rfl
    | .readWrite,  .readWrite,  .immutable  => rfl
    | .readWrite,  .readWrite,  .appendOnly => rfl
    | .readWrite,  .readWrite,  .monotonic  => rfl
    | .readWrite,  .readWrite,  .readWrite  => rfl

  add_comm := fun first second => match first, second with
    | .immutable,  .immutable  => rfl
    | .immutable,  .appendOnly => rfl
    | .immutable,  .monotonic  => rfl
    | .immutable,  .readWrite  => rfl
    | .appendOnly, .immutable  => rfl
    | .appendOnly, .appendOnly => rfl
    | .appendOnly, .monotonic  => rfl
    | .appendOnly, .readWrite  => rfl
    | .monotonic,  .immutable  => rfl
    | .monotonic,  .appendOnly => rfl
    | .monotonic,  .monotonic  => rfl
    | .monotonic,  .readWrite  => rfl
    | .readWrite,  .immutable  => rfl
    | .readWrite,  .appendOnly => rfl
    | .readWrite,  .monotonic  => rfl
    | .readWrite,  .readWrite  => rfl

  add_zero_left  := fun value => match value with
    | .immutable  => rfl
    | .appendOnly => rfl
    | .monotonic  => rfl
    | .readWrite  => rfl
  add_zero_right := fun value => match value with
    | .immutable  => rfl
    | .appendOnly => rfl
    | .monotonic  => rfl
    | .readWrite  => rfl

  mul_assoc := fun first second third => match first, second, third with
    | .immutable,  .immutable,  .immutable  => rfl
    | .immutable,  .immutable,  .appendOnly => rfl
    | .immutable,  .immutable,  .monotonic  => rfl
    | .immutable,  .immutable,  .readWrite  => rfl
    | .immutable,  .appendOnly, .immutable  => rfl
    | .immutable,  .appendOnly, .appendOnly => rfl
    | .immutable,  .appendOnly, .monotonic  => rfl
    | .immutable,  .appendOnly, .readWrite  => rfl
    | .immutable,  .monotonic,  .immutable  => rfl
    | .immutable,  .monotonic,  .appendOnly => rfl
    | .immutable,  .monotonic,  .monotonic  => rfl
    | .immutable,  .monotonic,  .readWrite  => rfl
    | .immutable,  .readWrite,  .immutable  => rfl
    | .immutable,  .readWrite,  .appendOnly => rfl
    | .immutable,  .readWrite,  .monotonic  => rfl
    | .immutable,  .readWrite,  .readWrite  => rfl
    | .appendOnly, .immutable,  .immutable  => rfl
    | .appendOnly, .immutable,  .appendOnly => rfl
    | .appendOnly, .immutable,  .monotonic  => rfl
    | .appendOnly, .immutable,  .readWrite  => rfl
    | .appendOnly, .appendOnly, .immutable  => rfl
    | .appendOnly, .appendOnly, .appendOnly => rfl
    | .appendOnly, .appendOnly, .monotonic  => rfl
    | .appendOnly, .appendOnly, .readWrite  => rfl
    | .appendOnly, .monotonic,  .immutable  => rfl
    | .appendOnly, .monotonic,  .appendOnly => rfl
    | .appendOnly, .monotonic,  .monotonic  => rfl
    | .appendOnly, .monotonic,  .readWrite  => rfl
    | .appendOnly, .readWrite,  .immutable  => rfl
    | .appendOnly, .readWrite,  .appendOnly => rfl
    | .appendOnly, .readWrite,  .monotonic  => rfl
    | .appendOnly, .readWrite,  .readWrite  => rfl
    | .monotonic,  .immutable,  .immutable  => rfl
    | .monotonic,  .immutable,  .appendOnly => rfl
    | .monotonic,  .immutable,  .monotonic  => rfl
    | .monotonic,  .immutable,  .readWrite  => rfl
    | .monotonic,  .appendOnly, .immutable  => rfl
    | .monotonic,  .appendOnly, .appendOnly => rfl
    | .monotonic,  .appendOnly, .monotonic  => rfl
    | .monotonic,  .appendOnly, .readWrite  => rfl
    | .monotonic,  .monotonic,  .immutable  => rfl
    | .monotonic,  .monotonic,  .appendOnly => rfl
    | .monotonic,  .monotonic,  .monotonic  => rfl
    | .monotonic,  .monotonic,  .readWrite  => rfl
    | .monotonic,  .readWrite,  .immutable  => rfl
    | .monotonic,  .readWrite,  .appendOnly => rfl
    | .monotonic,  .readWrite,  .monotonic  => rfl
    | .monotonic,  .readWrite,  .readWrite  => rfl
    | .readWrite,  .immutable,  .immutable  => rfl
    | .readWrite,  .immutable,  .appendOnly => rfl
    | .readWrite,  .immutable,  .monotonic  => rfl
    | .readWrite,  .immutable,  .readWrite  => rfl
    | .readWrite,  .appendOnly, .immutable  => rfl
    | .readWrite,  .appendOnly, .appendOnly => rfl
    | .readWrite,  .appendOnly, .monotonic  => rfl
    | .readWrite,  .appendOnly, .readWrite  => rfl
    | .readWrite,  .monotonic,  .immutable  => rfl
    | .readWrite,  .monotonic,  .appendOnly => rfl
    | .readWrite,  .monotonic,  .monotonic  => rfl
    | .readWrite,  .monotonic,  .readWrite  => rfl
    | .readWrite,  .readWrite,  .immutable  => rfl
    | .readWrite,  .readWrite,  .appendOnly => rfl
    | .readWrite,  .readWrite,  .monotonic  => rfl
    | .readWrite,  .readWrite,  .readWrite  => rfl

  mul_one_left  := fun value => match value with
    | .immutable  => rfl
    | .appendOnly => rfl
    | .monotonic  => rfl
    | .readWrite  => rfl
  mul_one_right := fun value => match value with
    | .immutable  => rfl
    | .appendOnly => rfl
    | .monotonic  => rfl
    | .readWrite  => rfl

  mul_distrib_left := fun scalar leftAddend rightAddend =>
    match scalar, leftAddend, rightAddend with
    | .immutable,  _,           _           => rfl
    | .appendOnly, .immutable,  .immutable  => rfl
    | .appendOnly, .immutable,  .appendOnly => rfl
    | .appendOnly, .immutable,  .monotonic  => rfl
    | .appendOnly, .immutable,  .readWrite  => rfl
    | .appendOnly, .appendOnly, .immutable  => rfl
    | .appendOnly, .appendOnly, .appendOnly => rfl
    | .appendOnly, .appendOnly, .monotonic  => rfl
    | .appendOnly, .appendOnly, .readWrite  => rfl
    | .appendOnly, .monotonic,  .immutable  => rfl
    | .appendOnly, .monotonic,  .appendOnly => rfl
    | .appendOnly, .monotonic,  .monotonic  => rfl
    | .appendOnly, .monotonic,  .readWrite  => rfl
    | .appendOnly, .readWrite,  .immutable  => rfl
    | .appendOnly, .readWrite,  .appendOnly => rfl
    | .appendOnly, .readWrite,  .monotonic  => rfl
    | .appendOnly, .readWrite,  .readWrite  => rfl
    | .monotonic,  .immutable,  .immutable  => rfl
    | .monotonic,  .immutable,  .appendOnly => rfl
    | .monotonic,  .immutable,  .monotonic  => rfl
    | .monotonic,  .immutable,  .readWrite  => rfl
    | .monotonic,  .appendOnly, .immutable  => rfl
    | .monotonic,  .appendOnly, .appendOnly => rfl
    | .monotonic,  .appendOnly, .monotonic  => rfl
    | .monotonic,  .appendOnly, .readWrite  => rfl
    | .monotonic,  .monotonic,  .immutable  => rfl
    | .monotonic,  .monotonic,  .appendOnly => rfl
    | .monotonic,  .monotonic,  .monotonic  => rfl
    | .monotonic,  .monotonic,  .readWrite  => rfl
    | .monotonic,  .readWrite,  .immutable  => rfl
    | .monotonic,  .readWrite,  .appendOnly => rfl
    | .monotonic,  .readWrite,  .monotonic  => rfl
    | .monotonic,  .readWrite,  .readWrite  => rfl
    | .readWrite,  .immutable,  .immutable  => rfl
    | .readWrite,  .immutable,  .appendOnly => rfl
    | .readWrite,  .immutable,  .monotonic  => rfl
    | .readWrite,  .immutable,  .readWrite  => rfl
    | .readWrite,  .appendOnly, .immutable  => rfl
    | .readWrite,  .appendOnly, .appendOnly => rfl
    | .readWrite,  .appendOnly, .monotonic  => rfl
    | .readWrite,  .appendOnly, .readWrite  => rfl
    | .readWrite,  .monotonic,  .immutable  => rfl
    | .readWrite,  .monotonic,  .appendOnly => rfl
    | .readWrite,  .monotonic,  .monotonic  => rfl
    | .readWrite,  .monotonic,  .readWrite  => rfl
    | .readWrite,  .readWrite,  .immutable  => rfl
    | .readWrite,  .readWrite,  .appendOnly => rfl
    | .readWrite,  .readWrite,  .monotonic  => rfl
    | .readWrite,  .readWrite,  .readWrite  => rfl

  mul_distrib_right := fun leftAddend rightAddend scalar =>
    match leftAddend, rightAddend, scalar with
    | .immutable,  .immutable,  _           => rfl
    | .immutable,  .appendOnly, .immutable  => rfl
    | .immutable,  .appendOnly, .appendOnly => rfl
    | .immutable,  .appendOnly, .monotonic  => rfl
    | .immutable,  .appendOnly, .readWrite  => rfl
    | .immutable,  .monotonic,  .immutable  => rfl
    | .immutable,  .monotonic,  .appendOnly => rfl
    | .immutable,  .monotonic,  .monotonic  => rfl
    | .immutable,  .monotonic,  .readWrite  => rfl
    | .immutable,  .readWrite,  .immutable  => rfl
    | .immutable,  .readWrite,  .appendOnly => rfl
    | .immutable,  .readWrite,  .monotonic  => rfl
    | .immutable,  .readWrite,  .readWrite  => rfl
    | .appendOnly, .immutable,  .immutable  => rfl
    | .appendOnly, .immutable,  .appendOnly => rfl
    | .appendOnly, .immutable,  .monotonic  => rfl
    | .appendOnly, .immutable,  .readWrite  => rfl
    | .appendOnly, .appendOnly, .immutable  => rfl
    | .appendOnly, .appendOnly, .appendOnly => rfl
    | .appendOnly, .appendOnly, .monotonic  => rfl
    | .appendOnly, .appendOnly, .readWrite  => rfl
    | .appendOnly, .monotonic,  .immutable  => rfl
    | .appendOnly, .monotonic,  .appendOnly => rfl
    | .appendOnly, .monotonic,  .monotonic  => rfl
    | .appendOnly, .monotonic,  .readWrite  => rfl
    | .appendOnly, .readWrite,  .immutable  => rfl
    | .appendOnly, .readWrite,  .appendOnly => rfl
    | .appendOnly, .readWrite,  .monotonic  => rfl
    | .appendOnly, .readWrite,  .readWrite  => rfl
    | .monotonic,  .immutable,  .immutable  => rfl
    | .monotonic,  .immutable,  .appendOnly => rfl
    | .monotonic,  .immutable,  .monotonic  => rfl
    | .monotonic,  .immutable,  .readWrite  => rfl
    | .monotonic,  .appendOnly, .immutable  => rfl
    | .monotonic,  .appendOnly, .appendOnly => rfl
    | .monotonic,  .appendOnly, .monotonic  => rfl
    | .monotonic,  .appendOnly, .readWrite  => rfl
    | .monotonic,  .monotonic,  .immutable  => rfl
    | .monotonic,  .monotonic,  .appendOnly => rfl
    | .monotonic,  .monotonic,  .monotonic  => rfl
    | .monotonic,  .monotonic,  .readWrite  => rfl
    | .monotonic,  .readWrite,  .immutable  => rfl
    | .monotonic,  .readWrite,  .appendOnly => rfl
    | .monotonic,  .readWrite,  .monotonic  => rfl
    | .monotonic,  .readWrite,  .readWrite  => rfl
    | .readWrite,  .immutable,  .immutable  => rfl
    | .readWrite,  .immutable,  .appendOnly => rfl
    | .readWrite,  .immutable,  .monotonic  => rfl
    | .readWrite,  .immutable,  .readWrite  => rfl
    | .readWrite,  .appendOnly, .immutable  => rfl
    | .readWrite,  .appendOnly, .appendOnly => rfl
    | .readWrite,  .appendOnly, .monotonic  => rfl
    | .readWrite,  .appendOnly, .readWrite  => rfl
    | .readWrite,  .monotonic,  .immutable  => rfl
    | .readWrite,  .monotonic,  .appendOnly => rfl
    | .readWrite,  .monotonic,  .monotonic  => rfl
    | .readWrite,  .monotonic,  .readWrite  => rfl
    | .readWrite,  .readWrite,  .immutable  => rfl
    | .readWrite,  .readWrite,  .appendOnly => rfl
    | .readWrite,  .readWrite,  .monotonic  => rfl
    | .readWrite,  .readWrite,  .readWrite  => rfl

  mul_zero_left  := fun _ => rfl
  mul_zero_right := fun value => match value with
    | .immutable  => rfl
    | .appendOnly => rfl
    | .monotonic  => rfl
    | .readWrite  => rfl

  le_refl := fun value => match value with
    | .immutable  => True.intro
    | .appendOnly => True.intro
    | .monotonic  => True.intro
    | .readWrite  => True.intro

  le_trans := fun first second third firstLeSecond secondLeThird =>
    match first, second, third, firstLeSecond, secondLeThird with
    -- first = immutable: le .immutable third = True for any third (full enum)
    | .immutable,  .immutable,   .immutable,   _, _ => True.intro
    | .immutable,  .immutable,   .appendOnly,  _, _ => True.intro
    | .immutable,  .immutable,   .monotonic,   _, _ => True.intro
    | .immutable,  .immutable,   .readWrite,   _, _ => True.intro
    | .immutable,  .appendOnly,  .immutable,   _, _ => True.intro
    | .immutable,  .appendOnly,  .appendOnly,  _, _ => True.intro
    | .immutable,  .appendOnly,  .monotonic,   _, _ => True.intro
    | .immutable,  .appendOnly,  .readWrite,   _, _ => True.intro
    | .immutable,  .monotonic,   .immutable,   _, _ => True.intro
    | .immutable,  .monotonic,   .appendOnly,  _, _ => True.intro
    | .immutable,  .monotonic,   .monotonic,   _, _ => True.intro
    | .immutable,  .monotonic,   .readWrite,   _, _ => True.intro
    | .immutable,  .readWrite,   .immutable,   _, _ => True.intro
    | .immutable,  .readWrite,   .appendOnly,  _, _ => True.intro
    | .immutable,  .readWrite,   .monotonic,   _, _ => True.intro
    | .immutable,  .readWrite,   .readWrite,   _, _ => True.intro
    -- first = appendOnly: second ∈ {appOnly, mono, rw} via firstLeSecond
    | .appendOnly, .appendOnly,  .appendOnly,  _, _ => True.intro
    | .appendOnly, .appendOnly,  .monotonic,   _, _ => True.intro
    | .appendOnly, .appendOnly,  .readWrite,   _, _ => True.intro
    | .appendOnly, .monotonic,   .monotonic,   _, _ => True.intro
    | .appendOnly, .monotonic,   .readWrite,   _, _ => True.intro
    | .appendOnly, .readWrite,   .readWrite,   _, _ => True.intro
    -- first = monotonic: second ∈ {mono, rw}
    | .monotonic,  .monotonic,   .monotonic,   _, _ => True.intro
    | .monotonic,  .monotonic,   .readWrite,   _, _ => True.intro
    | .monotonic,  .readWrite,   .readWrite,   _, _ => True.intro
    -- first = readWrite: second = readWrite, third = readWrite
    | .readWrite,  .readWrite,   .readWrite,   _, _ => True.intro

  add_mono := fun leftLow leftHigh rightLow rightHigh leftLeq rightLeq =>
    match leftLow, leftHigh, rightLow, rightHigh, leftLeq, rightLeq with
    -- leftLow = immutable: leftHigh ∈ {imm, appOnly, mono, rw}
    | .immutable, .immutable, .immutable, .immutable, _, _ => True.intro
    | .immutable, .immutable, .immutable, .appendOnly, _, _ => True.intro
    | .immutable, .immutable, .immutable, .monotonic, _, _ => True.intro
    | .immutable, .immutable, .immutable, .readWrite, _, _ => True.intro
    | .immutable, .immutable, .appendOnly, .appendOnly, _, _ => True.intro
    | .immutable, .immutable, .appendOnly, .monotonic, _, _ => True.intro
    | .immutable, .immutable, .appendOnly, .readWrite, _, _ => True.intro
    | .immutable, .immutable, .monotonic, .monotonic, _, _ => True.intro
    | .immutable, .immutable, .monotonic, .readWrite, _, _ => True.intro
    | .immutable, .immutable, .readWrite, .readWrite, _, _ => True.intro
    | .immutable, .appendOnly, .immutable, .immutable, _, _ => True.intro
    | .immutable, .appendOnly, .immutable, .appendOnly, _, _ => True.intro
    | .immutable, .appendOnly, .immutable, .monotonic, _, _ => True.intro
    | .immutable, .appendOnly, .immutable, .readWrite, _, _ => True.intro
    | .immutable, .appendOnly, .appendOnly, .appendOnly, _, _ => True.intro
    | .immutable, .appendOnly, .appendOnly, .monotonic, _, _ => True.intro
    | .immutable, .appendOnly, .appendOnly, .readWrite, _, _ => True.intro
    | .immutable, .appendOnly, .monotonic, .monotonic, _, _ => True.intro
    | .immutable, .appendOnly, .monotonic, .readWrite, _, _ => True.intro
    | .immutable, .appendOnly, .readWrite, .readWrite, _, _ => True.intro
    | .immutable, .monotonic, .immutable, .immutable, _, _ => True.intro
    | .immutable, .monotonic, .immutable, .appendOnly, _, _ => True.intro
    | .immutable, .monotonic, .immutable, .monotonic, _, _ => True.intro
    | .immutable, .monotonic, .immutable, .readWrite, _, _ => True.intro
    | .immutable, .monotonic, .appendOnly, .appendOnly, _, _ => True.intro
    | .immutable, .monotonic, .appendOnly, .monotonic, _, _ => True.intro
    | .immutable, .monotonic, .appendOnly, .readWrite, _, _ => True.intro
    | .immutable, .monotonic, .monotonic, .monotonic, _, _ => True.intro
    | .immutable, .monotonic, .monotonic, .readWrite, _, _ => True.intro
    | .immutable, .monotonic, .readWrite, .readWrite, _, _ => True.intro
    | .immutable, .readWrite, .immutable, .immutable, _, _ => True.intro
    | .immutable, .readWrite, .immutable, .appendOnly, _, _ => True.intro
    | .immutable, .readWrite, .immutable, .monotonic, _, _ => True.intro
    | .immutable, .readWrite, .immutable, .readWrite, _, _ => True.intro
    | .immutable, .readWrite, .appendOnly, .appendOnly, _, _ => True.intro
    | .immutable, .readWrite, .appendOnly, .monotonic, _, _ => True.intro
    | .immutable, .readWrite, .appendOnly, .readWrite, _, _ => True.intro
    | .immutable, .readWrite, .monotonic, .monotonic, _, _ => True.intro
    | .immutable, .readWrite, .monotonic, .readWrite, _, _ => True.intro
    | .immutable, .readWrite, .readWrite, .readWrite, _, _ => True.intro
    -- leftLow = appendOnly: leftHigh ∈ {appOnly, mono, rw}
    | .appendOnly, .appendOnly, .immutable, .immutable, _, _ => True.intro
    | .appendOnly, .appendOnly, .immutable, .appendOnly, _, _ => True.intro
    | .appendOnly, .appendOnly, .immutable, .monotonic, _, _ => True.intro
    | .appendOnly, .appendOnly, .immutable, .readWrite, _, _ => True.intro
    | .appendOnly, .appendOnly, .appendOnly, .appendOnly, _, _ => True.intro
    | .appendOnly, .appendOnly, .appendOnly, .monotonic, _, _ => True.intro
    | .appendOnly, .appendOnly, .appendOnly, .readWrite, _, _ => True.intro
    | .appendOnly, .appendOnly, .monotonic, .monotonic, _, _ => True.intro
    | .appendOnly, .appendOnly, .monotonic, .readWrite, _, _ => True.intro
    | .appendOnly, .appendOnly, .readWrite, .readWrite, _, _ => True.intro
    | .appendOnly, .monotonic, .immutable, .immutable, _, _ => True.intro
    | .appendOnly, .monotonic, .immutable, .appendOnly, _, _ => True.intro
    | .appendOnly, .monotonic, .immutable, .monotonic, _, _ => True.intro
    | .appendOnly, .monotonic, .immutable, .readWrite, _, _ => True.intro
    | .appendOnly, .monotonic, .appendOnly, .appendOnly, _, _ => True.intro
    | .appendOnly, .monotonic, .appendOnly, .monotonic, _, _ => True.intro
    | .appendOnly, .monotonic, .appendOnly, .readWrite, _, _ => True.intro
    | .appendOnly, .monotonic, .monotonic, .monotonic, _, _ => True.intro
    | .appendOnly, .monotonic, .monotonic, .readWrite, _, _ => True.intro
    | .appendOnly, .monotonic, .readWrite, .readWrite, _, _ => True.intro
    | .appendOnly, .readWrite, .immutable, .immutable, _, _ => True.intro
    | .appendOnly, .readWrite, .immutable, .appendOnly, _, _ => True.intro
    | .appendOnly, .readWrite, .immutable, .monotonic, _, _ => True.intro
    | .appendOnly, .readWrite, .immutable, .readWrite, _, _ => True.intro
    | .appendOnly, .readWrite, .appendOnly, .appendOnly, _, _ => True.intro
    | .appendOnly, .readWrite, .appendOnly, .monotonic, _, _ => True.intro
    | .appendOnly, .readWrite, .appendOnly, .readWrite, _, _ => True.intro
    | .appendOnly, .readWrite, .monotonic, .monotonic, _, _ => True.intro
    | .appendOnly, .readWrite, .monotonic, .readWrite, _, _ => True.intro
    | .appendOnly, .readWrite, .readWrite, .readWrite, _, _ => True.intro
    -- leftLow = monotonic: leftHigh ∈ {mono, rw}
    | .monotonic, .monotonic, .immutable, .immutable, _, _ => True.intro
    | .monotonic, .monotonic, .immutable, .appendOnly, _, _ => True.intro
    | .monotonic, .monotonic, .immutable, .monotonic, _, _ => True.intro
    | .monotonic, .monotonic, .immutable, .readWrite, _, _ => True.intro
    | .monotonic, .monotonic, .appendOnly, .appendOnly, _, _ => True.intro
    | .monotonic, .monotonic, .appendOnly, .monotonic, _, _ => True.intro
    | .monotonic, .monotonic, .appendOnly, .readWrite, _, _ => True.intro
    | .monotonic, .monotonic, .monotonic, .monotonic, _, _ => True.intro
    | .monotonic, .monotonic, .monotonic, .readWrite, _, _ => True.intro
    | .monotonic, .monotonic, .readWrite, .readWrite, _, _ => True.intro
    | .monotonic, .readWrite, .immutable, .immutable, _, _ => True.intro
    | .monotonic, .readWrite, .immutable, .appendOnly, _, _ => True.intro
    | .monotonic, .readWrite, .immutable, .monotonic, _, _ => True.intro
    | .monotonic, .readWrite, .immutable, .readWrite, _, _ => True.intro
    | .monotonic, .readWrite, .appendOnly, .appendOnly, _, _ => True.intro
    | .monotonic, .readWrite, .appendOnly, .monotonic, _, _ => True.intro
    | .monotonic, .readWrite, .appendOnly, .readWrite, _, _ => True.intro
    | .monotonic, .readWrite, .monotonic, .monotonic, _, _ => True.intro
    | .monotonic, .readWrite, .monotonic, .readWrite, _, _ => True.intro
    | .monotonic, .readWrite, .readWrite, .readWrite, _, _ => True.intro
    -- leftLow = readWrite: leftHigh = readWrite
    | .readWrite, .readWrite, .immutable, .immutable, _, _ => True.intro
    | .readWrite, .readWrite, .immutable, .appendOnly, _, _ => True.intro
    | .readWrite, .readWrite, .immutable, .monotonic, _, _ => True.intro
    | .readWrite, .readWrite, .immutable, .readWrite, _, _ => True.intro
    | .readWrite, .readWrite, .appendOnly, .appendOnly, _, _ => True.intro
    | .readWrite, .readWrite, .appendOnly, .monotonic, _, _ => True.intro
    | .readWrite, .readWrite, .appendOnly, .readWrite, _, _ => True.intro
    | .readWrite, .readWrite, .monotonic, .monotonic, _, _ => True.intro
    | .readWrite, .readWrite, .monotonic, .readWrite, _, _ => True.intro
    | .readWrite, .readWrite, .readWrite, .readWrite, _, _ => True.intro

  mul_mono := fun leftLow leftHigh rightLow rightHigh leftLeq rightLeq =>
    match leftLow, leftHigh, rightLow, rightHigh, leftLeq, rightLeq with
    -- leftLow = immutable: leftHigh ∈ {imm, appOnly, mono, rw}; mul .immutable _ = .immutable
    | .immutable, .immutable, .immutable, .immutable, _, _ => True.intro
    | .immutable, .immutable, .immutable, .appendOnly, _, _ => True.intro
    | .immutable, .immutable, .immutable, .monotonic, _, _ => True.intro
    | .immutable, .immutable, .immutable, .readWrite, _, _ => True.intro
    | .immutable, .immutable, .appendOnly, .appendOnly, _, _ => True.intro
    | .immutable, .immutable, .appendOnly, .monotonic, _, _ => True.intro
    | .immutable, .immutable, .appendOnly, .readWrite, _, _ => True.intro
    | .immutable, .immutable, .monotonic, .monotonic, _, _ => True.intro
    | .immutable, .immutable, .monotonic, .readWrite, _, _ => True.intro
    | .immutable, .immutable, .readWrite, .readWrite, _, _ => True.intro
    | .immutable, .appendOnly, .immutable, .immutable, _, _ => True.intro
    | .immutable, .appendOnly, .immutable, .appendOnly, _, _ => True.intro
    | .immutable, .appendOnly, .immutable, .monotonic, _, _ => True.intro
    | .immutable, .appendOnly, .immutable, .readWrite, _, _ => True.intro
    | .immutable, .appendOnly, .appendOnly, .appendOnly, _, _ => True.intro
    | .immutable, .appendOnly, .appendOnly, .monotonic, _, _ => True.intro
    | .immutable, .appendOnly, .appendOnly, .readWrite, _, _ => True.intro
    | .immutable, .appendOnly, .monotonic, .monotonic, _, _ => True.intro
    | .immutable, .appendOnly, .monotonic, .readWrite, _, _ => True.intro
    | .immutable, .appendOnly, .readWrite, .readWrite, _, _ => True.intro
    | .immutable, .monotonic, .immutable, .immutable, _, _ => True.intro
    | .immutable, .monotonic, .immutable, .appendOnly, _, _ => True.intro
    | .immutable, .monotonic, .immutable, .monotonic, _, _ => True.intro
    | .immutable, .monotonic, .immutable, .readWrite, _, _ => True.intro
    | .immutable, .monotonic, .appendOnly, .appendOnly, _, _ => True.intro
    | .immutable, .monotonic, .appendOnly, .monotonic, _, _ => True.intro
    | .immutable, .monotonic, .appendOnly, .readWrite, _, _ => True.intro
    | .immutable, .monotonic, .monotonic, .monotonic, _, _ => True.intro
    | .immutable, .monotonic, .monotonic, .readWrite, _, _ => True.intro
    | .immutable, .monotonic, .readWrite, .readWrite, _, _ => True.intro
    | .immutable, .readWrite, .immutable, .immutable, _, _ => True.intro
    | .immutable, .readWrite, .immutable, .appendOnly, _, _ => True.intro
    | .immutable, .readWrite, .immutable, .monotonic, _, _ => True.intro
    | .immutable, .readWrite, .immutable, .readWrite, _, _ => True.intro
    | .immutable, .readWrite, .appendOnly, .appendOnly, _, _ => True.intro
    | .immutable, .readWrite, .appendOnly, .monotonic, _, _ => True.intro
    | .immutable, .readWrite, .appendOnly, .readWrite, _, _ => True.intro
    | .immutable, .readWrite, .monotonic, .monotonic, _, _ => True.intro
    | .immutable, .readWrite, .monotonic, .readWrite, _, _ => True.intro
    | .immutable, .readWrite, .readWrite, .readWrite, _, _ => True.intro
    -- leftLow = appendOnly: leftHigh ∈ {appOnly, mono, rw}
    | .appendOnly, .appendOnly, .immutable, .immutable, _, _ => True.intro
    | .appendOnly, .appendOnly, .immutable, .appendOnly, _, _ => True.intro
    | .appendOnly, .appendOnly, .immutable, .monotonic, _, _ => True.intro
    | .appendOnly, .appendOnly, .immutable, .readWrite, _, _ => True.intro
    | .appendOnly, .appendOnly, .appendOnly, .appendOnly, _, _ => True.intro
    | .appendOnly, .appendOnly, .appendOnly, .monotonic, _, _ => True.intro
    | .appendOnly, .appendOnly, .appendOnly, .readWrite, _, _ => True.intro
    | .appendOnly, .appendOnly, .monotonic, .monotonic, _, _ => True.intro
    | .appendOnly, .appendOnly, .monotonic, .readWrite, _, _ => True.intro
    | .appendOnly, .appendOnly, .readWrite, .readWrite, _, _ => True.intro
    | .appendOnly, .monotonic, .immutable, .immutable, _, _ => True.intro
    | .appendOnly, .monotonic, .immutable, .appendOnly, _, _ => True.intro
    | .appendOnly, .monotonic, .immutable, .monotonic, _, _ => True.intro
    | .appendOnly, .monotonic, .immutable, .readWrite, _, _ => True.intro
    | .appendOnly, .monotonic, .appendOnly, .appendOnly, _, _ => True.intro
    | .appendOnly, .monotonic, .appendOnly, .monotonic, _, _ => True.intro
    | .appendOnly, .monotonic, .appendOnly, .readWrite, _, _ => True.intro
    | .appendOnly, .monotonic, .monotonic, .monotonic, _, _ => True.intro
    | .appendOnly, .monotonic, .monotonic, .readWrite, _, _ => True.intro
    | .appendOnly, .monotonic, .readWrite, .readWrite, _, _ => True.intro
    | .appendOnly, .readWrite, .immutable, .immutable, _, _ => True.intro
    | .appendOnly, .readWrite, .immutable, .appendOnly, _, _ => True.intro
    | .appendOnly, .readWrite, .immutable, .monotonic, _, _ => True.intro
    | .appendOnly, .readWrite, .immutable, .readWrite, _, _ => True.intro
    | .appendOnly, .readWrite, .appendOnly, .appendOnly, _, _ => True.intro
    | .appendOnly, .readWrite, .appendOnly, .monotonic, _, _ => True.intro
    | .appendOnly, .readWrite, .appendOnly, .readWrite, _, _ => True.intro
    | .appendOnly, .readWrite, .monotonic, .monotonic, _, _ => True.intro
    | .appendOnly, .readWrite, .monotonic, .readWrite, _, _ => True.intro
    | .appendOnly, .readWrite, .readWrite, .readWrite, _, _ => True.intro
    -- leftLow = monotonic: leftHigh ∈ {mono, rw}
    | .monotonic, .monotonic, .immutable, .immutable, _, _ => True.intro
    | .monotonic, .monotonic, .immutable, .appendOnly, _, _ => True.intro
    | .monotonic, .monotonic, .immutable, .monotonic, _, _ => True.intro
    | .monotonic, .monotonic, .immutable, .readWrite, _, _ => True.intro
    | .monotonic, .monotonic, .appendOnly, .appendOnly, _, _ => True.intro
    | .monotonic, .monotonic, .appendOnly, .monotonic, _, _ => True.intro
    | .monotonic, .monotonic, .appendOnly, .readWrite, _, _ => True.intro
    | .monotonic, .monotonic, .monotonic, .monotonic, _, _ => True.intro
    | .monotonic, .monotonic, .monotonic, .readWrite, _, _ => True.intro
    | .monotonic, .monotonic, .readWrite, .readWrite, _, _ => True.intro
    | .monotonic, .readWrite, .immutable, .immutable, _, _ => True.intro
    | .monotonic, .readWrite, .immutable, .appendOnly, _, _ => True.intro
    | .monotonic, .readWrite, .immutable, .monotonic, _, _ => True.intro
    | .monotonic, .readWrite, .immutable, .readWrite, _, _ => True.intro
    | .monotonic, .readWrite, .appendOnly, .appendOnly, _, _ => True.intro
    | .monotonic, .readWrite, .appendOnly, .monotonic, _, _ => True.intro
    | .monotonic, .readWrite, .appendOnly, .readWrite, _, _ => True.intro
    | .monotonic, .readWrite, .monotonic, .monotonic, _, _ => True.intro
    | .monotonic, .readWrite, .monotonic, .readWrite, _, _ => True.intro
    | .monotonic, .readWrite, .readWrite, .readWrite, _, _ => True.intro
    -- leftLow = readWrite: leftHigh = readWrite
    | .readWrite, .readWrite, .immutable, .immutable, _, _ => True.intro
    | .readWrite, .readWrite, .immutable, .appendOnly, _, _ => True.intro
    | .readWrite, .readWrite, .immutable, .monotonic, _, _ => True.intro
    | .readWrite, .readWrite, .immutable, .readWrite, _, _ => True.intro
    | .readWrite, .readWrite, .appendOnly, .appendOnly, _, _ => True.intro
    | .readWrite, .readWrite, .appendOnly, .monotonic, _, _ => True.intro
    | .readWrite, .readWrite, .appendOnly, .readWrite, _, _ => True.intro
    | .readWrite, .readWrite, .monotonic, .monotonic, _, _ => True.intro
    | .readWrite, .readWrite, .monotonic, .readWrite, _, _ => True.intro
    | .readWrite, .readWrite, .readWrite, .readWrite, _, _ => True.intro

/-! ## Smoke samples -/

/-- Combining accumulates upward in the chain. -/
example : MutationGrade.add .immutable .monotonic = .monotonic := rfl

/-- Scaling preserves the most-restrictive. -/
example : MutationGrade.mul .immutable .readWrite = .immutable := rfl

/-- Immutable fits where any rank expected. -/
example : MutationGrade.le .immutable .readWrite := True.intro

/-- Read-write does NOT fit where immutable expected. -/
example : ¬ MutationGrade.le .readWrite .immutable :=
  fun absurdLe => absurdLe.elim

/-- Monotonic fits where read-write expected. -/
example : MutationGrade.le .monotonic .readWrite := True.intro

end LeanFX2.Graded.Instances
