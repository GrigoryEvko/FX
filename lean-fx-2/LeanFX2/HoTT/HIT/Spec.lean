import LeanFX2.HoTT.Path.Groupoid

/-! # HoTT/HIT/Spec — Higher Inductive Type specifications

A HIT is a type defined by:
1. **Point constructors** — usual data constructors
2. **Path constructors** — identity proofs between point constructors

```lean
structure HITSpec where
  points  : List (Σ args, args → Type)        -- point constructors
  paths   : List (Σ args, ParseId)             -- path constructors
  -- coherence proofs etc.
```

## Examples

* `Circle (S¹)` — one point `base`, one path `loop : Id S¹ base base`
* `Suspension (Susp A)` — `north`, `south`, `merid : A → Id (Susp A) north south`
* `Quotient A R` — points from A, paths witnessing R

## Setoid encoding

In standard MLTT (no native HITs), we encode HITs via setoids
(Quotient inductive types).  Each HIT becomes:
* Underlying inductive with point constructors
* Path constructors as `axiom`s OR as quotient relations

lean-fx-2 uses the latter (Quotient inductive with manual respect
proofs) per the empirical recipe in lean-fx's
`feedback_lean_zero_axiom_match.md`.  This avoids propext while
getting the HIT semantics.

## Dependencies

* `HoTT/Path/Groupoid.lean`

## Downstream consumers

* `HoTT/HIT/Setoid.lean` — encoding
* `HoTT/HIT/Eliminator.lean` — HIT induction
* `HoTT/HIT/Examples.lean` — concrete HITs
-/

namespace LeanFX2

end LeanFX2
