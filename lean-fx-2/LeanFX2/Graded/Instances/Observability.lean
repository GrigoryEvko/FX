import LeanFX2.Graded.Semiring

/-! # Graded/Instances/Observability — observability lattice
`opaque < transparent`

Two-element observability lattice for tracking access-pattern
information leakage, encoded as the canonical 2-element Boolean
algebra `B = {opaque, transparent}` with:

* `+` = `∨` (join, OR)             — combining yields the "more
                                       observable" of the two
* `*` = `∧` (meet, AND)            — scaling annihilates with `0`
* `0` = `opaque`                   — additive identity, lattice bottom
* `1` = `transparent`              — multiplicative identity, lattice top
* `≤` = `opaque ≤ transparent`     — opaque is more restrictive

Per `fx_design.md` §6.3 dim 11: in a `with CT` (constant-time)
context, every value must be `opaque`.  `transparent` is a GRANT —
"this value's access pattern may leak its content".  Default is
`opaque` (deny by default).

## Why a Boolean algebra fits

Observability is a degenerate 2-element lattice — `opaque` is the
restrictive default and `transparent` is the explicitly-granted top.
The Boolean-algebra encoding gives every semiring law equationally
on the closed enum:

* combining (parallel): if EITHER branch is transparent, result is
  transparent (information about either may leak)
* scaling (sequential): if EITHER component is opaque, result is
  opaque (annihilation — opaque scaling preserves opacity)
* preorder: opaque fits where transparent expected (safe upgrade);
  reverse is unsafe (would leak access patterns)

## Cross-dimension interactions (§6.8)

* `transparent × CT`               — soundness collision: a
  transparent value used in `with CT` context leaks access pattern,
  which is exactly what CT forbids.  Checked at `GradeVector` level.

## Surface mode mapping

Per `fx_design.md` §6.3 / §12.5:
* default                          → `opaque` (deny by default)
* `transparent x`                  → `transparent` (explicit grant)
* CT context (`with CT`)           → forces all values to `opaque`

## Dependencies

* `Graded/Semiring.lean`

## Downstream

* `Graded/Rules.lean` — observability tracked through App/Let rules
* `fx_design.md` §12.5 — CT execution forbids transparent values

Zero-axiom verified per declaration.
-/

namespace LeanFX2.Graded.Instances

open LeanFX2.Graded

/-- Observability grade: `opaque < transparent`.  Closed 2-element
enum mirroring the Security pattern.

* `opaque` — access-pattern is hidden; lattice bottom; additive
  identity.  The default for every binding.

* `transparent` — access-pattern may leak; lattice top;
  multiplicative identity.  Explicitly granted via the
  `transparent` keyword. -/
inductive ObservabilityGrade : Type
  /-- Access-pattern hidden; lattice bottom; default. -/
  | opaque
  /-- Access-pattern may leak; lattice top; explicitly granted. -/
  | transparent
  deriving DecidableEq, Repr

namespace ObservabilityGrade

/-- Combining (parallel) is lattice join — `opaque ∨ x = x`,
`transparent ∨ x = transparent`.  Mixing observable and opaque
values yields a transparent (more-observable) result. -/
def add : ObservabilityGrade → ObservabilityGrade → ObservabilityGrade
  | .opaque,      rightOperand   => rightOperand
  | .transparent, _              => .transparent

/-- Scaling (sequential) is lattice meet — `opaque ∧ x = opaque`,
`transparent ∧ x = x`.  Annihilation: any scaling involving
`opaque` yields `opaque` (opaque computation preserves opacity). -/
def mul : ObservabilityGrade → ObservabilityGrade → ObservabilityGrade
  | .opaque,      _              => .opaque
  | .transparent, rightOperand   => rightOperand

/-- Subsumption preorder: `opaque ≤ transparent` (opaque is more
restrictive).  Opaque values fit where transparent expected; the
reverse violates CT and is rejected at typing. -/
def le : ObservabilityGrade → ObservabilityGrade → Prop
  | .opaque,      _              => True
  | .transparent, .opaque        => False
  | .transparent, .transparent   => True

end ObservabilityGrade

/-- The observability `{opaque, transparent}` Boolean-algebra
semiring.  All 17 algebra/preorder laws discharged by full case
enumeration over the non-indexed 2-element inductive — no `decide`,
no tactics that risk axiom emission. -/
instance : GradeSemiring ObservabilityGrade where
  zero := .opaque
  one  := .transparent
  add  := ObservabilityGrade.add
  mul  := ObservabilityGrade.mul
  le   := ObservabilityGrade.le

  add_assoc := fun first second third => match first, second, third with
    | .opaque,      _,              _              => rfl
    | .transparent, _,              _              => rfl

  add_comm := fun first second => match first, second with
    | .opaque,      .opaque        => rfl
    | .opaque,      .transparent   => rfl
    | .transparent, .opaque        => rfl
    | .transparent, .transparent   => rfl

  add_zero_left  := fun _ => rfl
  add_zero_right := fun value => match value with
    | .opaque        => rfl
    | .transparent   => rfl

  mul_assoc := fun first second third => match first, second, third with
    | .opaque,      _,              _              => rfl
    | .transparent, .opaque,        _              => rfl
    | .transparent, .transparent,   _              => rfl

  mul_one_left  := fun value => match value with
    | .opaque        => rfl
    | .transparent   => rfl
  mul_one_right := fun value => match value with
    | .opaque        => rfl
    | .transparent   => rfl

  mul_distrib_left := fun scalar leftAddend rightAddend =>
    match scalar, leftAddend, rightAddend with
    | .opaque,      _,              _              => rfl
    | .transparent, .opaque,        .opaque        => rfl
    | .transparent, .opaque,        .transparent   => rfl
    | .transparent, .transparent,   .opaque        => rfl
    | .transparent, .transparent,   .transparent   => rfl

  mul_distrib_right := fun leftAddend rightAddend scalar =>
    match leftAddend, rightAddend, scalar with
    | .opaque,      .opaque,        .opaque        => rfl
    | .opaque,      .opaque,        .transparent   => rfl
    | .opaque,      .transparent,   .opaque        => rfl
    | .opaque,      .transparent,   .transparent   => rfl
    | .transparent, .opaque,        .opaque        => rfl
    | .transparent, .opaque,        .transparent   => rfl
    | .transparent, .transparent,   .opaque        => rfl
    | .transparent, .transparent,   .transparent   => rfl

  mul_zero_left  := fun _ => rfl
  mul_zero_right := fun value => match value with
    | .opaque        => rfl
    | .transparent   => rfl

  le_refl := fun value => match value with
    | .opaque        => True.intro
    | .transparent   => True.intro

  le_trans := fun first second third firstLeSecond secondLeThird =>
    match first, second, third, firstLeSecond, secondLeThird with
    | .opaque,      _,              _,              _, _ => True.intro
    | .transparent, .transparent,   .transparent,   _, _ => True.intro

  add_mono := fun leftLow leftHigh rightLow rightHigh leftLeq rightLeq =>
    match leftLow, leftHigh, rightLow, rightHigh, leftLeq, rightLeq with
    | .opaque,      .opaque,        .opaque,        .opaque,        _, _ => True.intro
    | .opaque,      .opaque,        .opaque,        .transparent,   _, _ => True.intro
    | .opaque,      .opaque,        .transparent,   .transparent,   _, _ => True.intro
    | .opaque,      .transparent,   .opaque,        .opaque,        _, _ => True.intro
    | .opaque,      .transparent,   .opaque,        .transparent,   _, _ => True.intro
    | .opaque,      .transparent,   .transparent,   .transparent,   _, _ => True.intro
    | .transparent, .transparent,   .opaque,        .opaque,        _, _ => True.intro
    | .transparent, .transparent,   .opaque,        .transparent,   _, _ => True.intro
    | .transparent, .transparent,   .transparent,   .transparent,   _, _ => True.intro

  mul_mono := fun leftLow leftHigh rightLow rightHigh leftLeq rightLeq =>
    match leftLow, leftHigh, rightLow, rightHigh, leftLeq, rightLeq with
    -- leftLow = opaque (mul .opaque _ = .opaque, le .opaque _ = True)
    | .opaque,      _,              _,              _,              _, _ => True.intro
    -- leftLow = transparent (so leftHigh = transparent by le)
    | .transparent, .transparent,   .opaque,        .opaque,        _, _ => True.intro
    | .transparent, .transparent,   .opaque,        .transparent,   _, _ => True.intro
    | .transparent, .transparent,   .transparent,   .transparent,   _, _ => True.intro

/-! ## Smoke: combining vs scaling asymmetry -/

/-- Combining opaque with transparent yields transparent
(any-observable accumulates). -/
example :
    ObservabilityGrade.add .opaque .transparent = .transparent := rfl

/-- Scaling opaque by transparent yields opaque (annihilation:
opaque computation preserves opacity). -/
example :
    ObservabilityGrade.mul .opaque .transparent = .opaque := rfl

/-! ## Smoke: subsumption is uni-directional

Opaque fits where transparent expected (safe — additional opacity is
strictly more restrictive); transparent does NOT fit where opaque
expected (would leak access pattern in CT context). -/

/-- Opaque fits where transparent expected. -/
example : ObservabilityGrade.le .opaque .transparent := True.intro

/-- Transparent does NOT fit where opaque expected. -/
example : ¬ ObservabilityGrade.le .transparent .opaque :=
  fun absurdLe => absurdLe.elim

end LeanFX2.Graded.Instances
