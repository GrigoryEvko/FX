import LeanFX2.Graded.Semiring

/-! # Graded/Instances/Reentrancy — reentrancy lattice
`nonReentrant < reentrant`

Two-element reentrancy lattice for tracking whether a function may
self-call (re-entered while a prior invocation is still executing).
Encoded as the canonical 2-element Boolean algebra:

* `+` = `∨` (join, OR)             — combining yields the
                                       "more reentrant" of the two
* `*` = `∧` (meet, AND)            — scaling annihilates with `0`
* `0` = `nonReentrant`             — additive identity, lattice bottom
* `1` = `reentrant`                — multiplicative identity, lattice top
* `≤` = `nonReentrant ≤ reentrant` — non-reentrant is more restrictive

Per `fx_design.md` §6.3 dim 19 / §1.1: default is `nonReentrant`.
`reentrant` is granted via `rec` modifier (with `decreases` proof
or `with Div`) or `with Reentrant` effect.

## Why default is non-reentrant

A non-reentrant function may not be safely called from within its
own call stack (e.g., from an interrupt handler or via callback).
The default deny-by-default discipline forbids this; programmers
explicitly grant reentrancy when they've reasoned about
re-entrance safety.

## Cross-dimension interactions

* `reentrant × shared-mutable`     — must serialize on inner state
  to avoid interleaved updates breaking invariants
* `reentrant × HardIRQ`            — runtime forbids without
  spinlocks-with-IRQ-disabled (per §19.1 execution-context hierarchy)

## Surface mode mapping

* default                          → `nonReentrant`
* `rec` (with termination)         → `reentrant`
* `with Reentrant` effect          → `reentrant`

## Dependencies

* `Graded/Semiring.lean`

## Downstream

* `Graded/Rules.lean` — reentrancy tracked via App rule
* `fx_design.md` §6.3 dim 19, §19 (systems programming)

Zero-axiom verified per declaration.
-/

namespace LeanFX2.Graded.Instances

open LeanFX2.Graded

/-- Reentrancy grade: `nonReentrant < reentrant`.  Closed 2-element
enum.

* `nonReentrant` — default; function cannot be self-called
* `reentrant`    — explicitly granted via `rec` or `with Reentrant` -/
inductive ReentrancyGrade : Type
  /-- Default; cannot be re-entered. -/
  | nonReentrant
  /-- Explicitly reentrant; may be self-called. -/
  | reentrant
  deriving DecidableEq, Repr

namespace ReentrancyGrade

/-- Combining (parallel) is lattice join. -/
def add : ReentrancyGrade → ReentrancyGrade → ReentrancyGrade
  | .nonReentrant, rightOperand => rightOperand
  | .reentrant,    _            => .reentrant

/-- Scaling (sequential) is lattice meet — annihilates with
`nonReentrant`. -/
def mul : ReentrancyGrade → ReentrancyGrade → ReentrancyGrade
  | .nonReentrant, _             => .nonReentrant
  | .reentrant,    rightOperand  => rightOperand

/-- Subsumption preorder: non-reentrant fits where reentrant
expected (more restrictive); reverse violates the deny-by-default
discipline. -/
def le : ReentrancyGrade → ReentrancyGrade → Prop
  | .nonReentrant, _              => True
  | .reentrant,    .nonReentrant  => False
  | .reentrant,    .reentrant     => True

end ReentrancyGrade

/-- The reentrancy `{nonReentrant, reentrant}` Boolean-algebra
semiring.  All 17 algebra/preorder laws discharged by full case
enumeration. -/
instance : GradeSemiring ReentrancyGrade where
  zero := .nonReentrant
  one  := .reentrant
  add  := ReentrancyGrade.add
  mul  := ReentrancyGrade.mul
  le   := ReentrancyGrade.le

  add_assoc := fun first second third => match first, second, third with
    | .nonReentrant, _, _ => rfl
    | .reentrant,    _, _ => rfl

  add_comm := fun first second => match first, second with
    | .nonReentrant, .nonReentrant => rfl
    | .nonReentrant, .reentrant    => rfl
    | .reentrant,    .nonReentrant => rfl
    | .reentrant,    .reentrant    => rfl

  add_zero_left  := fun _ => rfl
  add_zero_right := fun value => match value with
    | .nonReentrant => rfl
    | .reentrant    => rfl

  mul_assoc := fun first second third => match first, second, third with
    | .nonReentrant, _,              _ => rfl
    | .reentrant,    .nonReentrant, _ => rfl
    | .reentrant,    .reentrant,    _ => rfl

  mul_one_left  := fun value => match value with
    | .nonReentrant => rfl
    | .reentrant    => rfl
  mul_one_right := fun value => match value with
    | .nonReentrant => rfl
    | .reentrant    => rfl

  mul_distrib_left := fun scalar leftAddend rightAddend =>
    match scalar, leftAddend, rightAddend with
    | .nonReentrant, _,              _              => rfl
    | .reentrant,    .nonReentrant, .nonReentrant  => rfl
    | .reentrant,    .nonReentrant, .reentrant     => rfl
    | .reentrant,    .reentrant,    .nonReentrant  => rfl
    | .reentrant,    .reentrant,    .reentrant     => rfl

  mul_distrib_right := fun leftAddend rightAddend scalar =>
    match leftAddend, rightAddend, scalar with
    | .nonReentrant, .nonReentrant, .nonReentrant => rfl
    | .nonReentrant, .nonReentrant, .reentrant    => rfl
    | .nonReentrant, .reentrant,    .nonReentrant => rfl
    | .nonReentrant, .reentrant,    .reentrant    => rfl
    | .reentrant,    .nonReentrant, .nonReentrant => rfl
    | .reentrant,    .nonReentrant, .reentrant    => rfl
    | .reentrant,    .reentrant,    .nonReentrant => rfl
    | .reentrant,    .reentrant,    .reentrant    => rfl

  mul_zero_left  := fun _ => rfl
  mul_zero_right := fun value => match value with
    | .nonReentrant => rfl
    | .reentrant    => rfl

  le_refl := fun value => match value with
    | .nonReentrant => True.intro
    | .reentrant    => True.intro

  le_trans := fun first second third firstLeSecond secondLeThird =>
    match first, second, third, firstLeSecond, secondLeThird with
    | .nonReentrant, _,           _,           _, _ => True.intro
    | .reentrant,    .reentrant, .reentrant, _, _ => True.intro

  add_mono := fun leftLow leftHigh rightLow rightHigh leftLeq rightLeq =>
    match leftLow, leftHigh, rightLow, rightHigh, leftLeq, rightLeq with
    | .nonReentrant, .nonReentrant, .nonReentrant, .nonReentrant, _, _ => True.intro
    | .nonReentrant, .nonReentrant, .nonReentrant, .reentrant,    _, _ => True.intro
    | .nonReentrant, .nonReentrant, .reentrant,    .reentrant,    _, _ => True.intro
    | .nonReentrant, .reentrant,    .nonReentrant, .nonReentrant, _, _ => True.intro
    | .nonReentrant, .reentrant,    .nonReentrant, .reentrant,    _, _ => True.intro
    | .nonReentrant, .reentrant,    .reentrant,    .reentrant,    _, _ => True.intro
    | .reentrant,    .reentrant,    .nonReentrant, .nonReentrant, _, _ => True.intro
    | .reentrant,    .reentrant,    .nonReentrant, .reentrant,    _, _ => True.intro
    | .reentrant,    .reentrant,    .reentrant,    .reentrant,    _, _ => True.intro

  mul_mono := fun leftLow leftHigh rightLow rightHigh leftLeq rightLeq =>
    match leftLow, leftHigh, rightLow, rightHigh, leftLeq, rightLeq with
    -- leftLow = nonReentrant (annihilates, le _ _ = True)
    | .nonReentrant, _,              _,              _,              _, _ => True.intro
    -- leftLow = reentrant (so leftHigh = reentrant by le)
    | .reentrant,    .reentrant,    .nonReentrant, .nonReentrant, _, _ => True.intro
    | .reentrant,    .reentrant,    .nonReentrant, .reentrant,    _, _ => True.intro
    | .reentrant,    .reentrant,    .reentrant,    .reentrant,    _, _ => True.intro

/-! ## Smoke samples -/

/-- Combining accumulates reentrancy. -/
example :
    ReentrancyGrade.add .nonReentrant .reentrant = .reentrant := rfl

/-- Scaling annihilates with non-reentrant. -/
example :
    ReentrancyGrade.mul .nonReentrant .reentrant = .nonReentrant := rfl

/-- Non-reentrant fits where reentrant expected. -/
example : ReentrancyGrade.le .nonReentrant .reentrant := True.intro

/-- Reentrant does NOT fit where non-reentrant expected. -/
example : ¬ ReentrancyGrade.le .reentrant .nonReentrant :=
  fun absurdLe => absurdLe.elim

end LeanFX2.Graded.Instances
