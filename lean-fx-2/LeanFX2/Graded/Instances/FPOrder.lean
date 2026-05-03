import LeanFX2.Graded.Semiring

/-! # Graded/Instances/FPOrder — floating-point order lattice
`strict < reassociate`

Two-element FP-order lattice for tracking whether floating-point
arithmetic may be reassociated by the compiler (for SIMD or
vectorization).  Encoded as the canonical 2-element Boolean algebra:

* `+` = `∨` (join, OR)             — combining yields the
                                       "more permissive" of the two
* `*` = `∧` (meet, AND)            — scaling annihilates with `0`
* `0` = `strict`                   — additive identity, lattice bottom
* `1` = `reassociate`              — multiplicative identity, lattice top
* `≤` = `strict ≤ reassociate`     — strict is more restrictive

Per `fx_design.md` §6.3 dim 17: default is `strict` — left-to-right
evaluation, bit-identical across platforms.  `reassociate` is a
GRANT — "compiler may reorder for SIMD".  Numerical reproducibility
(e.g., for cryptographic determinism) requires `strict`.

## Why default is strict

FP non-associativity means `(a + b) + c ≠ a + (b + c)` in the bit
representation, even though both equal the mathematical sum.  When
two systems compute "the same" expression with different
associativities, results diverge in the last few bits.  Default
deny rejects this divergence; programmers explicitly opt in via
`with Reassociate`.

## Cross-dimension interactions

* `reassociate × CT`               — soundness collision: SIMD
  reassociation can leak inputs through timing variation
* `reassociate × cryptographic_determinism` — must use `strict`
  for hash determinism

## Surface mode mapping

* default                          → `strict`
* `with Reassociate`               → `reassociate`

## Dependencies

* `Graded/Semiring.lean`

## Downstream

* `Graded/Rules.lean` — FP order tracked through arith ops
* `fx_design.md` §3.11 (FP control), §6.3 dim 17

Zero-axiom verified per declaration.
-/

namespace LeanFX2.Graded.Instances

open LeanFX2.Graded

/-- FP-order grade: `strict < reassociate`.  Closed 2-element enum.

* `strict` — bit-identical evaluation order; default
* `reassociate` — compiler may reorder for SIMD/vectorization -/
inductive FPOrderGrade : Type
  /-- Bit-identical left-to-right evaluation. -/
  | strict
  /-- Compiler may reorder for SIMD. -/
  | reassociate
  deriving DecidableEq, Repr

namespace FPOrderGrade

/-- Combining is lattice join. -/
def add : FPOrderGrade → FPOrderGrade → FPOrderGrade
  | .strict,      rightOperand => rightOperand
  | .reassociate, _            => .reassociate

/-- Scaling is lattice meet — annihilates with `strict`. -/
def mul : FPOrderGrade → FPOrderGrade → FPOrderGrade
  | .strict,      _            => .strict
  | .reassociate, rightOperand => rightOperand

/-- Subsumption preorder: strict fits where reassociate expected
(more restrictive). -/
def le : FPOrderGrade → FPOrderGrade → Prop
  | .strict,      _              => True
  | .reassociate, .strict        => False
  | .reassociate, .reassociate   => True

end FPOrderGrade

/-- The FP-order `{strict, reassociate}` Boolean-algebra semiring.
All 17 algebra/preorder laws discharged by full case enumeration. -/
instance : GradeSemiring FPOrderGrade where
  zero := .strict
  one  := .reassociate
  add  := FPOrderGrade.add
  mul  := FPOrderGrade.mul
  le   := FPOrderGrade.le

  add_assoc := fun first second third => match first, second, third with
    | .strict,      _, _ => rfl
    | .reassociate, _, _ => rfl

  add_comm := fun first second => match first, second with
    | .strict,      .strict      => rfl
    | .strict,      .reassociate => rfl
    | .reassociate, .strict      => rfl
    | .reassociate, .reassociate => rfl

  add_zero_left  := fun _ => rfl
  add_zero_right := fun value => match value with
    | .strict      => rfl
    | .reassociate => rfl

  mul_assoc := fun first second third => match first, second, third with
    | .strict,      _,            _ => rfl
    | .reassociate, .strict,      _ => rfl
    | .reassociate, .reassociate, _ => rfl

  mul_one_left  := fun value => match value with
    | .strict      => rfl
    | .reassociate => rfl
  mul_one_right := fun value => match value with
    | .strict      => rfl
    | .reassociate => rfl

  mul_distrib_left := fun scalar leftAddend rightAddend =>
    match scalar, leftAddend, rightAddend with
    | .strict,      _,            _            => rfl
    | .reassociate, .strict,      .strict      => rfl
    | .reassociate, .strict,      .reassociate => rfl
    | .reassociate, .reassociate, .strict      => rfl
    | .reassociate, .reassociate, .reassociate => rfl

  mul_distrib_right := fun leftAddend rightAddend scalar =>
    match leftAddend, rightAddend, scalar with
    | .strict,      .strict,      .strict      => rfl
    | .strict,      .strict,      .reassociate => rfl
    | .strict,      .reassociate, .strict      => rfl
    | .strict,      .reassociate, .reassociate => rfl
    | .reassociate, .strict,      .strict      => rfl
    | .reassociate, .strict,      .reassociate => rfl
    | .reassociate, .reassociate, .strict      => rfl
    | .reassociate, .reassociate, .reassociate => rfl

  mul_zero_left  := fun _ => rfl
  mul_zero_right := fun value => match value with
    | .strict      => rfl
    | .reassociate => rfl

  le_refl := fun value => match value with
    | .strict      => True.intro
    | .reassociate => True.intro

  le_trans := fun first second third firstLeSecond secondLeThird =>
    match first, second, third, firstLeSecond, secondLeThird with
    | .strict,      _,            _,            _, _ => True.intro
    | .reassociate, .reassociate, .reassociate, _, _ => True.intro

  add_mono := fun leftLow leftHigh rightLow rightHigh leftLeq rightLeq =>
    match leftLow, leftHigh, rightLow, rightHigh, leftLeq, rightLeq with
    | .strict,      .strict,      .strict,      .strict,      _, _ => True.intro
    | .strict,      .strict,      .strict,      .reassociate, _, _ => True.intro
    | .strict,      .strict,      .reassociate, .reassociate, _, _ => True.intro
    | .strict,      .reassociate, .strict,      .strict,      _, _ => True.intro
    | .strict,      .reassociate, .strict,      .reassociate, _, _ => True.intro
    | .strict,      .reassociate, .reassociate, .reassociate, _, _ => True.intro
    | .reassociate, .reassociate, .strict,      .strict,      _, _ => True.intro
    | .reassociate, .reassociate, .strict,      .reassociate, _, _ => True.intro
    | .reassociate, .reassociate, .reassociate, .reassociate, _, _ => True.intro

  mul_mono := fun leftLow leftHigh rightLow rightHigh leftLeq rightLeq =>
    match leftLow, leftHigh, rightLow, rightHigh, leftLeq, rightLeq with
    -- leftLow = strict (annihilates, le _ _ = True)
    | .strict,      _,            _,            _,            _, _ => True.intro
    -- leftLow = reassociate (so leftHigh = reassociate by le)
    | .reassociate, .reassociate, .strict,      .strict,      _, _ => True.intro
    | .reassociate, .reassociate, .strict,      .reassociate, _, _ => True.intro
    | .reassociate, .reassociate, .reassociate, .reassociate, _, _ => True.intro

/-! ## Smoke samples -/

/-- Combining accumulates permissiveness. -/
example :
    FPOrderGrade.add .strict .reassociate = .reassociate := rfl

/-- Scaling annihilates with strict. -/
example :
    FPOrderGrade.mul .strict .reassociate = .strict := rfl

/-- Strict fits where reassociate expected. -/
example : FPOrderGrade.le .strict .reassociate := True.intro

/-- Reassociate does NOT fit where strict expected. -/
example : ¬ FPOrderGrade.le .reassociate .strict :=
  fun absurdLe => absurdLe.elim

end LeanFX2.Graded.Instances
