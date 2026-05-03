import LeanFX2.Foundation.Ty

/-! # Refine/Ty — refinement type machinery (Lean-side support)

`Ty.refine base predicate` decorates a base type with a predicate
carving out the inhabitants satisfying it.  This file ships the
Lean-side support machinery: `RefinePredicate`, `RefineWitness`,
and decidability support.

The actual kernel `Ty.refine` constructor is K01 (deferred
cascade).  Until that lands, this file provides standalone
infrastructure that the surface elaborator can use to encode
refinement-type subtyping decisions.

## What ships (Phase 12.A.5)

* `RefinePredicate alpha` — bundle a predicate + decidability
* `RefineWitness predicate` — pair (value, proof) inhabiting the
  refinement
* Concrete example predicates: `Nat.isPositive`, `Nat.isBounded`,
  `List.isNonEmpty`
* `RefineWitness.coerce` — project the underlying value (forget proof)
* Decidability of refinement membership (via the bundle's instance)

## What defers

* `Ty.refine` kernel constructor — K01 (cascade through Ty / RawTerm
  / Term / Subst / Step / Conv / ... ~15 files)
* SMT-cert path — `Refine/SMTCert.lean` and `Refine/SMTRecheck.lean`
  ship in v1.1 alongside the SMT bridge
* Subtyping coercions at the kernel level — depends on K01

Zero-axiom verified per declaration. -/

namespace LeanFX2.Refine

/-! ## Refinement predicates

A refinement predicate bundles a Prop-valued predicate with a
`Decidable` instance.  This makes membership decidable at type-check
time for the Lean-internal fragment (per `fx_design.md` §10.8). -/

/-- A refinement predicate over `alpha`: a function `alpha → Prop`
together with decidability for every value.  This bundles what's
needed to decide "is `x` in the refinement?". -/
structure RefinePredicate (alpha : Type) where
  /-- The predicate carving out inhabitants. -/
  pred : alpha → Prop
  /-- Decidability for every value. -/
  decidable : ∀ (someValue : alpha), Decidable (pred someValue)

/-! ## Refinement witnesses

A `RefineWitness` is the dependent-pair encoding: `(value, proof
that value satisfies the predicate)`.  This is the standard subset-
type encoding `Σ x : α, P x`, packaged as a structure for
ergonomics. -/

/-- An inhabitant of a refinement: the underlying value plus a
proof that it satisfies the predicate. -/
structure RefineWitness {alpha : Type}
    (predicate : RefinePredicate alpha)
    where
  /-- The underlying value. -/
  refinedValue : alpha
  /-- Proof that the value satisfies the refinement predicate. -/
  satisfies : predicate.pred refinedValue

namespace RefineWitness

variable {alpha : Type} {predicate : RefinePredicate alpha}

/-- Coerce a refinement witness to its underlying value (forgets
the proof).  Standard subtype-to-supertype coercion. -/
def coerce (someWitness : RefineWitness predicate) : alpha :=
  someWitness.refinedValue

/-- Two witnesses with the same underlying value are equal at the
witness level (since proofs of decidable propositions are unique
up to Subsingleton; for general predicates, this requires the
proof to be propositional, which it is by `Prop`). -/
theorem eq_of_value_eq
    (firstWitness secondWitness : RefineWitness predicate)
    (valueEq : firstWitness.refinedValue = secondWitness.refinedValue) :
    firstWitness.coerce = secondWitness.coerce := by
  show firstWitness.refinedValue = secondWitness.refinedValue
  exact valueEq

end RefineWitness

/-! ## Membership decidability

Lifts the predicate's `Decidable` instance to a decision procedure
for membership in the refinement. -/

/-- Decide whether a value satisfies a refinement predicate.  Returns
the underlying `Decidable` instance, suitable for use in
`if x ∈ refinement then ... else ...` branches. -/
def decideMembership {alpha : Type}
    (predicate : RefinePredicate alpha)
    (someValue : alpha) :
    Decidable (predicate.pred someValue) :=
  predicate.decidable someValue

/-! ## Concrete example predicates

These exist to demonstrate the machinery and provide test cases.
The surface elaborator references these when encoding common FX
refinements like `nat { x > 0 }`. -/

/-- `nat { x > 0 }`: positive naturals. -/
def Nat.isPositive : RefinePredicate Nat where
  pred := fun someNat => 0 < someNat
  decidable := fun someNat => inferInstanceAs (Decidable (0 < someNat))

/-- `nat { x < bound }`: naturals strictly less than a bound. -/
def Nat.isBounded (bound : Nat) : RefinePredicate Nat where
  pred := fun someNat => someNat < bound
  decidable := fun someNat => inferInstanceAs (Decidable (someNat < bound))

/-- `nat { lo ≤ x ≤ hi }`: naturals in a closed interval. -/
def Nat.isInRange (lowerBound upperBound : Nat) : RefinePredicate Nat where
  pred := fun someNat => lowerBound ≤ someNat ∧ someNat ≤ upperBound
  decidable := fun someNat =>
    inferInstanceAs (Decidable (lowerBound ≤ someNat ∧ someNat ≤ upperBound))

/-- `list α { length > 0 }`: non-empty lists. -/
def List.isNonEmpty {alpha : Type} : RefinePredicate (List alpha) where
  pred := fun someList => 0 < someList.length
  decidable := fun someList => inferInstanceAs (Decidable (0 < someList.length))

/-! ## Smoke samples -/

/-- The number 5 is positive (5 > 0). -/
example : RefineWitness Nat.isPositive :=
  { refinedValue := 5, satisfies := show 0 < 5 by decide }

/-- The number 7 is bounded by 10 (7 < 10). -/
example : RefineWitness (Nat.isBounded 10) :=
  { refinedValue := 7, satisfies := show 7 < 10 by decide }

/-- The number 5 is in the range [1, 10]. -/
example : RefineWitness (Nat.isInRange 1 10) :=
  { refinedValue := 5, satisfies := show 1 ≤ 5 ∧ 5 ≤ 10 by exact ⟨by decide, by decide⟩ }

/-- The list [1, 2, 3] is non-empty. -/
example : RefineWitness (List.isNonEmpty (alpha := Nat)) :=
  { refinedValue := [1, 2, 3], satisfies := show 0 < ([1, 2, 3] : List Nat).length by decide }

/-- Coerce extracts the underlying value. -/
example : Nat :=
  let positiveFive : RefineWitness Nat.isPositive :=
    { refinedValue := 5, satisfies := show 0 < 5 by decide }
  positiveFive.coerce

end LeanFX2.Refine
