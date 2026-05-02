import LeanFX2.HoTT.Equivalence
import LeanFX2.HoTT.Path.Groupoid

/-! # HoTT/NTypes — h-prop / h-set stratification

The HoTT n-type hierarchy classifies types by the complexity of
their identity structure:

* (-2)-type: contractible (one inhabitant up to path)
* (-1)-type: proposition (any two values are equal)
* 0-type: set (path-equality is propositional)
* 1-type: groupoid (path-of-paths is propositional)
* ...

For v1.0 set-level we ship the foundational levels (contr, prop,
set) plus interconversion lemmas + concrete instances.  The
uniform Nat-indexed `IsHType` form is deferred to v1.1 — it
requires careful universe management for the recursive case
where the inductive predicate is applied to an `Eq` (which lives
in `Prop`).

## What ships

* `IsProp T` — any two values of T are propositionally equal
* `IsSet T`  — IsProp on every identity type
* `IsGroupoidLevel T` — IsSet on every identity type
* `IsContr.toProp` — contractible types are propositions
* `IsProp.toSet`   — propositions are sets (via Subsingleton)
* `IsContr.toSet`  — composition of the two lifts
* Concrete instances: `IsProp.unit`, `IsSet.unit / bool / nat`

## Why h-set matters for v1.0

At h-set, K-axiom-like reasoning applies WITHOUT globally
assuming K.  Most "data" types (Nat, Bool, List, String,
products of sets) are sets.  HITs (deferred to v1.1+) introduce
types that are NOT sets (e.g., S^1 has non-trivial loops).

## Zero-axiom

All declarations propext-free.  IsProp/IsSet are Π over identity;
their proofs go via `Subsingleton.allEq` (a propext-free Lean
stdlib operation when the type is proven Subsingleton).

## Dependencies

* `HoTT/Equivalence.lean` — IsContr base case
* `HoTT/Path/Groupoid.lean` — Path operations for ascent

## Downstream consumers

* `HoTT/Univalence.lean` — univalence classified by n-types
* `HoTT/HIT/*` — HITs have specific n-type characters
-/

namespace LeanFX2

universe nLevel

/-! ## Foundational n-types -/

/-- A type is a **proposition** (h-prop, (-1)-type) when any two
inhabitants are propositionally equal.  At h-prop, the type is
"truth-valued" — either contradictory (no inhabitants) or
"singleton" (exactly one inhabitant up to equality). -/
def IsProp (SomeType : Sort nLevel) : Prop :=
  ∀ (firstValue secondValue : SomeType), firstValue = secondValue

/-- A type is a **set** (h-set, 0-type) when its identity types
are propositions.  Sets are the natural home for "data" — types
where path-of-paths uniqueness holds. -/
def IsSet (SomeType : Sort nLevel) : Prop :=
  ∀ (firstValue secondValue : SomeType),
    IsProp (firstValue = secondValue)

/-- A type is an **h-groupoid** (1-type) when its identity types
are sets. -/
def IsGroupoidLevel (SomeType : Sort nLevel) : Prop :=
  ∀ (firstValue secondValue : SomeType),
    IsSet (firstValue = secondValue)

/-! ## Lifting between levels: contr -> prop -> set -> ... -/

/-- Contractibility implies h-prop: if there's a center value
that everything equals, then any two values both equal the
center, hence each other (via path symmetry + composition). -/
theorem IsContr.toProp {SomeType : Sort nLevel}
    (contrWitness : IsContr SomeType) :
    IsProp SomeType := by
  intro firstValue secondValue
  have firstAtCenter  : firstValue  = contrWitness.center :=
    contrWitness.spoke firstValue
  have secondAtCenter : secondValue = contrWitness.center :=
    contrWitness.spoke secondValue
  exact Eq.trans firstAtCenter (Eq.symm secondAtCenter)

/-- An h-prop type is automatically a `Subsingleton` instance —
this lets `Subsingleton.allEq` discharge h-set proofs. -/
instance IsProp.subsingleton {SomeType : Sort nLevel}
    (_propWitness : IsProp SomeType) :
    Subsingleton SomeType where
  allEq := _propWitness

/-- An h-prop type is an h-set: any path between values must
itself be unique.  The proof routes through Lean stdlib's
`Subsingleton.allEq`, which is propext-free when the underlying
Subsingleton instance is propext-free. -/
theorem IsProp.toSet {SomeType : Sort nLevel}
    (propWitness : IsProp SomeType) :
    IsSet SomeType := by
  intro firstValue secondValue firstPath secondPath
  have _instance := IsProp.subsingleton propWitness
  exact Subsingleton.allEq _ _

/-- Contractibility lifts directly to h-set (composing the two
lift theorems). -/
theorem IsContr.toSet {SomeType : Sort nLevel}
    (contrWitness : IsContr SomeType) :
    IsSet SomeType :=
  IsProp.toSet (IsContr.toProp contrWitness)

/-! ## Concrete instances at h-set -/

/-- `Unit` is contractible. -/
def IsContr.unitInstance : IsContr Unit :=
  IsContr.unit

/-- `Unit` is a proposition (lifted from contractibility). -/
theorem IsProp.unit : IsProp Unit :=
  IsContr.toProp IsContr.unitInstance

/-- `Unit` is a set (lifted from h-prop). -/
theorem IsSet.unit : IsSet Unit :=
  IsProp.toSet IsProp.unit

/-- `Bool` is a set.  Direct via Lean's `Subsingleton` machinery
on `firstValue = secondValue` (which is decidable, hence
proof-irrelevant). -/
theorem IsSet.bool : IsSet Bool := by
  intro firstValue secondValue firstPath secondPath
  exact Subsingleton.allEq _ _

/-- `Nat` is a set.  Same machinery as Bool — DecidableEq Nat
gives Subsingleton on identity types. -/
theorem IsSet.nat : IsSet Nat := by
  intro firstValue secondValue firstPath secondPath
  exact Subsingleton.allEq _ _

/-! ## Smoke samples -/

example : IsProp Unit := IsProp.unit
example : IsSet Unit  := IsSet.unit
example : IsSet Bool  := IsSet.bool
example : IsSet Nat   := IsSet.nat

/-- A contractible type's two values are equal.  Direct
application of toProp. -/
example (someValue : Unit) :
    someValue = (IsContr.unitInstance).center :=
  IsContr.unitInstance.spoke someValue

/-- The identity path on `()` is unique — h-set witness. -/
example (firstPath secondPath : (() : Unit) = ()) :
    firstPath = secondPath :=
  IsSet.unit () () firstPath secondPath

end LeanFX2
