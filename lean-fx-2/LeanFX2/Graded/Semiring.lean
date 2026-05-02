/-! # Graded/Semiring — generic semiring framework

A `GradeSemiring` is a semiring `(R, +, *, 0, 1, ≤)` plus a preorder
compatible with `+` and `*`.  Each of FX's 19 graded dimensions
instantiates this typeclass.

## Algebra (per `fx_design.md` §6.1)

```lean
class GradeSemiring (R : Type) where
  zero : R
  one  : R
  add  : R → R → R
  mul  : R → R → R
  le   : R → R → Prop
  -- laws:
  add_assoc      : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm       : ∀ a b,   add a b = add b a
  add_zero_left  : ∀ a,     add zero a = a
  mul_assoc      : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  mul_one_left   : ∀ a,     mul one a = a
  mul_one_right  : ∀ a,     mul a one = a
  mul_distrib_left  : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  mul_distrib_right : ∀ a b c, mul (add a b) c = add (mul a c) (mul b c)
  mul_zero_left  : ∀ a, mul zero a = zero
  mul_zero_right : ∀ a, mul a zero = zero
  -- preorder:
  le_refl        : ∀ a,     le a a
  le_trans       : ∀ a b c, le a b → le b c → le a c
  add_mono       : ∀ a b c d, le a b → le c d → le (add a c) (add b d)
  mul_mono       : ∀ a b c d, le a b → le c d → le (mul a c) (mul b d)
```

## Why typeclass

* Every dimension provides one — `instance Usage.semiring : GradeSemiring UsageGrade`,
  `instance Effect.semiring : GradeSemiring EffectGrade`, etc.
* Generic `GradeVector` (`Graded/GradeVector.lean`) is parameterized
  by the registered list of semirings; pointwise ops use the typeclass.
* Wood/Atkey context division `pi/p` (per `fx_design.md` §6.2) is
  defined generically: `pi/p = max { d : mul d p ≤ pi }`.  Each
  semiring provides the order; division is computable when the
  semiring is decidable.

## Laws as Prop, computation as data

The data fields (`zero, one, add, mul, le`) are the *operational*
content.  The `_assoc, _comm, ...` fields are *propositions* that
must be discharged when constructing an instance.

For decidable semirings, `Decidable (le a b)` enables typechecker-
internal grade comparisons.

## Dependencies

Layer 7 of Layer 7 — depends only on Lean core (no FX-specific code).

## Downstream

* `Graded/GradeVector.lean` — dependent product over registered dims
* `Graded/Rules.lean` — Wood-Atkey lambda rule via context division
* `Graded/Instances/*.lean` — concrete dim semirings

## Implementation plan (Phase 8)

1. Define `class GradeSemiring (R : Type)` with data + laws fields
2. Provide proof-helper API: `mul_zero_iff_zero_or_zero` etc.
3. Add `Decidable` constraint for runtime grade comparison
4. Smoke: trivial 1-element semiring (`Unit`) instances all laws

Target: ~150 lines.
-/

namespace LeanFX2.Graded

-- TODO Phase 8: GradeSemiring typeclass with data + laws
-- TODO Phase 8: Decidable extension for runtime grade comparisons
-- TODO Phase 8: context-division operator on top of semiring

end LeanFX2.Graded
