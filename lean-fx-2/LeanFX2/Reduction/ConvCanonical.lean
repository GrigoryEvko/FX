import LeanFX2.Term.Inversion
import LeanFX2.Term.SubjectReduction
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

/-! ## Parameterized canonical heads

For ctors whose type carries a parameter (listNil's element type,
optionNone's element type), the Conv theorem requires the stated
types to match — the term value depends on the parameter.

Pattern: cases both terms first (which specializes both types),
then cases on the type equality (giving structural equality of
the parameters), then `Conv.refl` works on the now-identical
terms.
-/

/-- Two `.listNil`-raw terms at equal types are convertible. -/
theorem Conv.canonical_listNil
    {sourceType targetType : Ty level scope}
    (sourceTerm : Term context sourceType (RawTerm.listNil (scope := scope)))
    (targetTerm : Term context targetType (RawTerm.listNil (scope := scope)))
    (sameType : sourceType = targetType) :
    Conv sourceTerm targetTerm := by
  cases sourceTerm
  cases targetTerm
  cases sameType
  exact Conv.refl _

/-- Two `.optionNone`-raw terms at equal types are convertible. -/
theorem Conv.canonical_optionNone
    {sourceType targetType : Ty level scope}
    (sourceTerm : Term context sourceType (RawTerm.optionNone (scope := scope)))
    (targetTerm : Term context targetType (RawTerm.optionNone (scope := scope)))
    (sameType : sourceType = targetType) :
    Conv sourceTerm targetTerm := by
  cases sourceTerm
  cases targetTerm
  cases sameType
  exact Conv.refl _

/-- Two `.refl rawWitness`-raw terms at equal types are
convertible.  The identity-type structure is forced: both sides
are at `Ty.id carrier rawWitness rawWitness` (HoTT reflexivity-as-types). -/
theorem Conv.canonical_refl
    {sourceType targetType : Ty level scope}
    {rawWitness : RawTerm scope}
    (sourceTerm : Term context sourceType (RawTerm.refl rawWitness))
    (targetTerm : Term context targetType (RawTerm.refl rawWitness))
    (sameType : sourceType = targetType) :
    Conv sourceTerm targetTerm := by
  cases sourceTerm
  cases targetTerm
  cases sameType
  exact Conv.refl _

/-! ## Unary canonical heads at `Ty.nat`

Subject reduction (`StepStar.preserves_ty_nat`) constrains the
existentially-quantified middle type in `Conv` for `Ty.nat`-typed
predecessors.  The resulting cong rule lifts `Conv` between
`Ty.nat`-typed predecessors to `Conv` between their `natSucc`-
wrappers.
-/

/-- Cong rule: `Conv` on nat-typed predecessors lifts to `Conv` on
their `Term.natSucc` wrappers. -/
theorem Conv.natSucc_cong
    {predRawA predRawB : RawTerm scope}
    {predTermA : Term context Ty.nat predRawA}
    {predTermB : Term context Ty.nat predRawB}
    (predConv : Conv predTermA predTermB) :
    Conv (Term.natSucc predTermA) (Term.natSucc predTermB) := by
  obtain ⟨midType, midRaw, midTerm, chainA, chainB⟩ := predConv
  have midIsNat : midType = Ty.nat := StepStar.preserves_ty_nat chainA rfl
  refine ⟨Ty.nat, RawTerm.natSucc midRaw, Term.natSucc (midIsNat ▸ midTerm),
          ?_, ?_⟩
  · exact StepStar.natSucc_lift_general chainA rfl midIsNat
  · exact StepStar.natSucc_lift_general chainB rfl midIsNat

end LeanFX2
