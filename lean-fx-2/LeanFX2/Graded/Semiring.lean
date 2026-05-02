/-! # Graded/Semiring — generic semiring framework for graded type system

A `GradeSemiring` is a semiring `(R, +, *, 0, 1, ≤)` with a preorder
compatible with `+` and `*`.  Each of FX's 19 graded dimensions
instantiates this typeclass.

Per `fx_design.md` §6.1.

## Algebra

* `(R, +, 0)` is a commutative monoid (parallel use)
* `(R, *, 1)` is a monoid (sequential use)
* `*` distributes over `+`
* `0 * r = r * 0 = 0` (annihilation)
* `≤` preorder compatible with `+` and `*` (monotonicity)

## Concrete instances (downstream `Graded/Instances/*`)

* `UsageGrade` = `{0, 1, ω}` — linearity tracking
* `EffectGrade` = set of effect labels — capability tracking
* `SecurityGrade` = `{unclassified < classified}` — info flow
* ... 19 total per `fx_design.md` §6.3

## Why typeclass

* Each dimension is a separate instance
* Generic `GradeVector` (next file) is parameterized by the registered
  list of semirings; pointwise ops use the typeclass
* Wood/Atkey context division `pi/p` (per §6.2) is defined generically:
  `pi/p = max { d : d * p ≤ pi }` — needs `Decidable` extension to
  compute in elaboration

## Layer

Pure Lean — no FX-specific dependencies.  Foundation for Graded layer.
-/

namespace LeanFX2.Graded

/-- Semiring with preorder for tracking graded resource usage along
one of FX's 19 type-system dimensions.  All algebra laws are bundled
to ensure each instance is verified. -/
class GradeSemiring (Carrier : Type) where
  /-- Additive identity (representing "no resource"). -/
  zero : Carrier
  /-- Multiplicative identity (representing "one use"). -/
  one  : Carrier
  /-- Parallel composition (resource union). -/
  add  : Carrier → Carrier → Carrier
  /-- Sequential composition (resource scaling). -/
  mul  : Carrier → Carrier → Carrier
  /-- Subsumption preorder (smaller = more restrictive). -/
  le   : Carrier → Carrier → Prop

  -- Additive monoid laws
  add_assoc      : ∀ first second third,
                     add (add first second) third = add first (add second third)
  add_comm       : ∀ first second, add first second = add second first
  add_zero_left  : ∀ value, add zero value = value
  add_zero_right : ∀ value, add value zero = value

  -- Multiplicative monoid laws
  mul_assoc      : ∀ first second third,
                     mul (mul first second) third = mul first (mul second third)
  mul_one_left   : ∀ value, mul one value = value
  mul_one_right  : ∀ value, mul value one = value

  -- Distribution laws
  mul_distrib_left  : ∀ scalar leftAddend rightAddend,
                        mul scalar (add leftAddend rightAddend) =
                        add (mul scalar leftAddend) (mul scalar rightAddend)
  mul_distrib_right : ∀ leftAddend rightAddend scalar,
                        mul (add leftAddend rightAddend) scalar =
                        add (mul leftAddend scalar) (mul rightAddend scalar)

  -- Annihilation
  mul_zero_left  : ∀ value, mul zero value = zero
  mul_zero_right : ∀ value, mul value zero = zero

  -- Preorder laws
  le_refl        : ∀ value, le value value
  le_trans       : ∀ first second third, le first second → le second third → le first third

  -- Monotonicity (preorder compatible with operations)
  add_mono : ∀ leftLow leftHigh rightLow rightHigh,
               le leftLow leftHigh → le rightLow rightHigh →
               le (add leftLow rightLow) (add leftHigh rightHigh)
  mul_mono : ∀ leftLow leftHigh rightLow rightHigh,
               le leftLow leftHigh → le rightLow rightHigh →
               le (mul leftLow rightLow) (mul leftHigh rightHigh)

namespace GradeSemiring

variable {Carrier : Type} [GradeSemiring Carrier]

/-- Sum-of-many-additions helper: `addAll [a, b, c] = a + b + c` (with
zero for the empty list).  Useful for grade-vector composition. -/
def addAll : List Carrier → Carrier
  | [] => zero
  | head :: rest => add head (addAll rest)

/-- Product-of-many helper: `mulAll [a, b, c] = a * b * c` (with one
for the empty list). -/
def mulAll : List Carrier → Carrier
  | [] => one
  | head :: rest => mul head (mulAll rest)

end GradeSemiring

/-- A `DecidableGradeSemiring` extends `GradeSemiring` with a decidable
preorder, enabling computation of subsumption checks at elaboration
time.  Required for any dimension whose grade comparisons appear in
typing rules. -/
class DecidableGradeSemiring (Carrier : Type) extends GradeSemiring Carrier where
  decideLe : ∀ first second, Decidable (le first second)
  decideEq : DecidableEq Carrier

namespace DecidableGradeSemiring

variable {Carrier : Type} [DecidableGradeSemiring Carrier]

/-- Re-export `decideLe` as a `Decidable` instance for use in `if
... then ... else ...` over the preorder. -/
instance : ∀ (first second : Carrier), Decidable (GradeSemiring.le first second) :=
  decideLe

end DecidableGradeSemiring

/-! ## Smoke: trivial 1-element semiring (Unit)

The unit semiring has a single element; all laws hold trivially.
Verifies the typeclass shape compiles and zero axioms are used. -/

instance : GradeSemiring Unit where
  zero := ()
  one  := ()
  add  := fun _ _ => ()
  mul  := fun _ _ => ()
  le   := fun _ _ => True
  add_assoc := fun _ _ _ => rfl
  add_comm  := fun _ _ => rfl
  add_zero_left  := fun _ => rfl
  add_zero_right := fun _ => rfl
  mul_assoc := fun _ _ _ => rfl
  mul_one_left  := fun _ => rfl
  mul_one_right := fun _ => rfl
  mul_distrib_left  := fun _ _ _ => rfl
  mul_distrib_right := fun _ _ _ => rfl
  mul_zero_left  := fun _ => rfl
  mul_zero_right := fun _ => rfl
  le_refl  := fun _ => True.intro
  le_trans := fun _ _ _ _ _ => True.intro
  add_mono := fun _ _ _ _ _ _ => True.intro
  mul_mono := fun _ _ _ _ _ _ => True.intro

end LeanFX2.Graded
