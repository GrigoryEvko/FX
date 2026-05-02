import LeanFX2.Term.Inversion
import LeanFX2.Reduction.Conv

/-! # Reduction/ConvCanonical — Conv between canonical-head terms

For each nullary canonical-head Term ctor (`unit`, `boolTrue`,
`boolFalse`, `natZero`), any two terms with that raw projection
in the same context are convertible — regardless of the stated
type, since the raw form forces the type via Term inversion
(Phase 7.A).

Each theorem is a 3-line `cases sourceTerm; cases targetTerm;
Conv.refl _`.  Combines the typed Term inversions (Phase 7.A)
with `Conv.refl` (Phase 3.C) to give the strongest possible
typed Conv corollary at the canonical-head level.

## Why these matter

These give the BASE CASES of typed conversion checking:
when the elaborator encounters two canonical-head terms, it
can immediately conclude they're convertible without recursing
on sub-structure.  Combined with the upcoming Conv cong family
(blocked on subject reduction), this gives the typed conversion
algorithm.

## Pattern

Each follows the schema:

```lean
theorem Conv.canonical_<ctor>
    {sourceType targetType}
    (sourceTerm : Term ctx sourceType (RawTerm.<ctor> ...))
    (targetTerm : Term ctx targetType (RawTerm.<ctor> ...)) :
    Conv sourceTerm targetTerm := by
  cases sourceTerm
  cases targetTerm
  exact Conv.refl _
```

The implicit `sourceType` / `targetType` is critical — Lean's
matcher needs the types as metavariables to unify them with the
type of the matched ctor (e.g., `Ty.unit` for `Term.unit`).
With concrete types specified, the matcher gets stuck on the
`var` case because `varType context position` is opaque.
-/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}

/-- Two `.unit`-raw terms are convertible. -/
theorem Conv.canonical_unit
    {sourceType targetType : Ty level scope}
    (sourceTerm : Term context sourceType (RawTerm.unit (scope := scope)))
    (targetTerm : Term context targetType (RawTerm.unit (scope := scope))) :
    Conv sourceTerm targetTerm := by
  cases sourceTerm
  cases targetTerm
  exact Conv.refl _

/-- Two `.boolTrue`-raw terms are convertible. -/
theorem Conv.canonical_boolTrue
    {sourceType targetType : Ty level scope}
    (sourceTerm : Term context sourceType (RawTerm.boolTrue (scope := scope)))
    (targetTerm : Term context targetType (RawTerm.boolTrue (scope := scope))) :
    Conv sourceTerm targetTerm := by
  cases sourceTerm
  cases targetTerm
  exact Conv.refl _

/-- Two `.boolFalse`-raw terms are convertible. -/
theorem Conv.canonical_boolFalse
    {sourceType targetType : Ty level scope}
    (sourceTerm : Term context sourceType (RawTerm.boolFalse (scope := scope)))
    (targetTerm : Term context targetType (RawTerm.boolFalse (scope := scope))) :
    Conv sourceTerm targetTerm := by
  cases sourceTerm
  cases targetTerm
  exact Conv.refl _

/-- Two `.natZero`-raw terms are convertible. -/
theorem Conv.canonical_natZero
    {sourceType targetType : Ty level scope}
    (sourceTerm : Term context sourceType (RawTerm.natZero (scope := scope)))
    (targetTerm : Term context targetType (RawTerm.natZero (scope := scope))) :
    Conv sourceTerm targetTerm := by
  cases sourceTerm
  cases targetTerm
  exact Conv.refl _

end LeanFX2
