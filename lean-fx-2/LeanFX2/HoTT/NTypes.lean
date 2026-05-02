import LeanFX2.HoTT.Equivalence

/-! # HoTT/NTypes — n-type stratification

The HoTT hierarchy:
* (-2)-type: contractible
* (-1)-type: proposition (any two elements are propositionally equal)
* 0-type: set (paths between paths are unique — UIP-like)
* 1-type: groupoid
* ...

```lean
def isContr (A : Type) : Type :=
  Σ (a : A), ∀ x, Id A a x

def isProp (A : Type) : Type :=
  ∀ x y : A, Id A x y

def isSet (A : Type) : Type :=
  ∀ x y : A, isProp (Id A x y)

def isGroupoid (A : Type) : Type :=
  ∀ x y : A, isSet (Id A x y)

-- ... (general isNType n-1)
```

## Why this matters

n-type predicates classify how "complex" a type's identity structure
is.  In particular:
* `isProp` classifies "really propositional" types where homotopy
  triviality holds.  Proof irrelevance reduces to `isProp`-typed
  results.
* `isSet` classifies types where K-axiom-like reasoning applies
  *without* assuming K globally.  Most "data" types (Nat, Bool,
  List) are sets.
* HITs introduce types that are *not* sets (e.g., S¹ has non-trivial
  loops).

## Key lemmas

* Subtypes of n-types are n-types
* Π and Σ over n-types are n-types
* `isProp (isProp A)` — being a proposition is a proposition

## Dependencies

* `HoTT/Equivalence.lean`

## Downstream consumers

* `HoTT/Univalence.lean` — univalence at universe levels classified
  by n-types
* `HoTT/HIT/*` — HITs have specific n-type characters
-/

namespace LeanFX2

end LeanFX2
