import LeanFX2.Term.Inversion
import LeanFX2.Term.SubjectReduction
import LeanFX2.Reduction.Conv
import LeanFX2.Reduction.ConvCongIsClosedTy

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
their `Term.natSucc` wrappers.  1-step parameterization of
`Conv.cong_at_isClosedTy`. -/
theorem Conv.natSucc_cong
    {predRawA predRawB : RawTerm scope}
    {predTermA : Term context Ty.nat predRawA}
    {predTermB : Term context Ty.nat predRawB}
    (predConv : Conv predTermA predTermB) :
    Conv (Term.natSucc predTermA) (Term.natSucc predTermB) :=
  Conv.cong_at_isClosedTy
    (resultTy := Ty.nat) IsClosedTy.nat
    (wrapRaw := RawTerm.natSucc) (fun term => Term.natSucc term)
    (fun step => Step.natSuccPred step)
    predConv

/-- Scrutinee cong rule: `Conv` on bool-typed scrutinees lifts to
`Conv` on `boolElim`-wrappers (with shared motive + branches).
1-step parameterization of `Conv.cong_at_isClosedTy`. -/
theorem Conv.boolElimScrutinee_cong
    {motiveType : Ty level scope}
    {scrutRawA scrutRawB thenRaw elseRaw : RawTerm scope}
    {scrutA : Term context Ty.bool scrutRawA}
    {scrutB : Term context Ty.bool scrutRawB}
    (thenBranch : Term context motiveType thenRaw)
    (elseBranch : Term context motiveType elseRaw)
    (scrutConv : Conv scrutA scrutB) :
    Conv (Term.boolElim scrutA thenBranch elseBranch)
         (Term.boolElim scrutB thenBranch elseBranch) :=
  Conv.cong_at_isClosedTy
    (resultTy := motiveType) IsClosedTy.bool
    (wrapRaw := fun raw => RawTerm.boolElim raw thenRaw elseRaw)
    (fun term => Term.boolElim term thenBranch elseBranch)
    (fun step => Step.boolElimScrutinee step)
    scrutConv

/-- Scrutinee cong rule: `Conv` on nat-typed scrutinees lifts to
`Conv` on `natElim`-wrappers. -/
theorem Conv.natElimScrutinee_cong
    {motiveType : Ty level scope}
    {scrutRawA scrutRawB zeroRaw succRaw : RawTerm scope}
    {scrutA : Term context Ty.nat scrutRawA}
    {scrutB : Term context Ty.nat scrutRawB}
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw)
    (scrutConv : Conv scrutA scrutB) :
    Conv (Term.natElim scrutA zeroBranch succBranch)
         (Term.natElim scrutB zeroBranch succBranch) :=
  Conv.cong_at_isClosedTy
    (resultTy := motiveType) IsClosedTy.nat
    (wrapRaw := fun raw => RawTerm.natElim raw zeroRaw succRaw)
    (fun term => Term.natElim term zeroBranch succBranch)
    (fun step => Step.natElimScrutinee step)
    scrutConv

/-- Scrutinee cong rule: `Conv` on nat-typed scrutinees lifts to
`Conv` on `natRec`-wrappers. -/
theorem Conv.natRecScrutinee_cong
    {motiveType : Ty level scope}
    {scrutRawA scrutRawB zeroRaw succRaw : RawTerm scope}
    {scrutA : Term context Ty.nat scrutRawA}
    {scrutB : Term context Ty.nat scrutRawB}
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch : Term context
                    (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw)
    (scrutConv : Conv scrutA scrutB) :
    Conv (Term.natRec scrutA zeroBranch succBranch)
         (Term.natRec scrutB zeroBranch succBranch) :=
  Conv.cong_at_isClosedTy
    (resultTy := motiveType) IsClosedTy.nat
    (wrapRaw := fun raw => RawTerm.natRec raw zeroRaw succRaw)
    (fun term => Term.natRec term zeroBranch succBranch)
    (fun step => Step.natRecScrutinee step)
    scrutConv

/-! ## Branch cong rules at closed motive types

For `boolElim`'s then-branch with closed motive type
(`Ty.unit`/`Ty.bool`/`Ty.nat`), `Conv` on the branch lifts to
`Conv` on the `boolElim` wrapper.  Three explicit variants per
closed motive — generic motive needs general subject reduction
(Phase 7.D, deferred). -/

/-- `Conv` on `boolElim`'s then-branch at `Ty.unit` motive. -/
theorem Conv.boolElimThen_cong_unit
    {scrutRaw thenRawA thenRawB elseRaw : RawTerm scope}
    (scrutinee : Term context Ty.bool scrutRaw)
    {thenA : Term context Ty.unit thenRawA}
    {thenB : Term context Ty.unit thenRawB}
    (elseBranch : Term context Ty.unit elseRaw)
    (thenConv : Conv thenA thenB) :
    Conv (Term.boolElim scrutinee thenA elseBranch)
         (Term.boolElim scrutinee thenB elseBranch) :=
  Conv.cong_at_isClosedTy
    (resultTy := Ty.unit) IsClosedTy.unit
    (wrapRaw := fun raw => RawTerm.boolElim scrutRaw raw elseRaw)
    (fun term => Term.boolElim scrutinee term elseBranch)
    (fun step => Step.boolElimThen step) thenConv

/-- `Conv` on `boolElim`'s then-branch at `Ty.bool` motive. -/
theorem Conv.boolElimThen_cong_bool
    {scrutRaw thenRawA thenRawB elseRaw : RawTerm scope}
    (scrutinee : Term context Ty.bool scrutRaw)
    {thenA : Term context Ty.bool thenRawA}
    {thenB : Term context Ty.bool thenRawB}
    (elseBranch : Term context Ty.bool elseRaw)
    (thenConv : Conv thenA thenB) :
    Conv (Term.boolElim scrutinee thenA elseBranch)
         (Term.boolElim scrutinee thenB elseBranch) :=
  Conv.cong_at_isClosedTy
    (resultTy := Ty.bool) IsClosedTy.bool
    (wrapRaw := fun raw => RawTerm.boolElim scrutRaw raw elseRaw)
    (fun term => Term.boolElim scrutinee term elseBranch)
    (fun step => Step.boolElimThen step) thenConv

/-- `Conv` on `boolElim`'s then-branch at `Ty.nat` motive. -/
theorem Conv.boolElimThen_cong_nat
    {scrutRaw thenRawA thenRawB elseRaw : RawTerm scope}
    (scrutinee : Term context Ty.bool scrutRaw)
    {thenA : Term context Ty.nat thenRawA}
    {thenB : Term context Ty.nat thenRawB}
    (elseBranch : Term context Ty.nat elseRaw)
    (thenConv : Conv thenA thenB) :
    Conv (Term.boolElim scrutinee thenA elseBranch)
         (Term.boolElim scrutinee thenB elseBranch) :=
  Conv.cong_at_isClosedTy
    (resultTy := Ty.nat) IsClosedTy.nat
    (wrapRaw := fun raw => RawTerm.boolElim scrutRaw raw elseRaw)
    (fun term => Term.boolElim scrutinee term elseBranch)
    (fun step => Step.boolElimThen step) thenConv

/-- `Conv` on `boolElim`'s else-branch at `Ty.unit` motive. -/
theorem Conv.boolElimElse_cong_unit
    {scrutRaw thenRaw elseRawA elseRawB : RawTerm scope}
    (scrutinee : Term context Ty.bool scrutRaw)
    (thenBranch : Term context Ty.unit thenRaw)
    {elseA : Term context Ty.unit elseRawA}
    {elseB : Term context Ty.unit elseRawB}
    (elseConv : Conv elseA elseB) :
    Conv (Term.boolElim scrutinee thenBranch elseA)
         (Term.boolElim scrutinee thenBranch elseB) :=
  Conv.cong_at_isClosedTy
    (resultTy := Ty.unit) IsClosedTy.unit
    (wrapRaw := fun raw => RawTerm.boolElim scrutRaw thenRaw raw)
    (fun term => Term.boolElim scrutinee thenBranch term)
    (fun step => Step.boolElimElse step) elseConv

/-- `Conv` on `boolElim`'s else-branch at `Ty.bool` motive. -/
theorem Conv.boolElimElse_cong_bool
    {scrutRaw thenRaw elseRawA elseRawB : RawTerm scope}
    (scrutinee : Term context Ty.bool scrutRaw)
    (thenBranch : Term context Ty.bool thenRaw)
    {elseA : Term context Ty.bool elseRawA}
    {elseB : Term context Ty.bool elseRawB}
    (elseConv : Conv elseA elseB) :
    Conv (Term.boolElim scrutinee thenBranch elseA)
         (Term.boolElim scrutinee thenBranch elseB) :=
  Conv.cong_at_isClosedTy
    (resultTy := Ty.bool) IsClosedTy.bool
    (wrapRaw := fun raw => RawTerm.boolElim scrutRaw thenRaw raw)
    (fun term => Term.boolElim scrutinee thenBranch term)
    (fun step => Step.boolElimElse step) elseConv

/-- `Conv` on `boolElim`'s else-branch at `Ty.nat` motive. -/
theorem Conv.boolElimElse_cong_nat
    {scrutRaw thenRaw elseRawA elseRawB : RawTerm scope}
    (scrutinee : Term context Ty.bool scrutRaw)
    (thenBranch : Term context Ty.nat thenRaw)
    {elseA : Term context Ty.nat elseRawA}
    {elseB : Term context Ty.nat elseRawB}
    (elseConv : Conv elseA elseB) :
    Conv (Term.boolElim scrutinee thenBranch elseA)
         (Term.boolElim scrutinee thenBranch elseB) :=
  Conv.cong_at_isClosedTy
    (resultTy := Ty.nat) IsClosedTy.nat
    (wrapRaw := fun raw => RawTerm.boolElim scrutRaw thenRaw raw)
    (fun term => Term.boolElim scrutinee thenBranch term)
    (fun step => Step.boolElimElse step) elseConv

/-! ## natElim/natRec zero-branch cong rules at closed motive types -/

/-- `Conv` on `natElim`'s zero-branch at `Ty.unit` motive. -/
theorem Conv.natElimZero_cong_unit
    {scrutRaw zeroRawA zeroRawB succRaw : RawTerm scope}
    (scrutinee : Term context Ty.nat scrutRaw)
    {zeroA : Term context Ty.unit zeroRawA}
    {zeroB : Term context Ty.unit zeroRawB}
    (succBranch : Term context (Ty.arrow Ty.nat Ty.unit) succRaw)
    (zeroConv : Conv zeroA zeroB) :
    Conv (Term.natElim scrutinee zeroA succBranch)
         (Term.natElim scrutinee zeroB succBranch) :=
  Conv.cong_at_isClosedTy
    (resultTy := Ty.unit) IsClosedTy.unit
    (wrapRaw := fun raw => RawTerm.natElim scrutRaw raw succRaw)
    (fun term => Term.natElim scrutinee term succBranch)
    (fun step => Step.natElimZero step) zeroConv

/-- `Conv` on `natElim`'s zero-branch at `Ty.bool` motive. -/
theorem Conv.natElimZero_cong_bool
    {scrutRaw zeroRawA zeroRawB succRaw : RawTerm scope}
    (scrutinee : Term context Ty.nat scrutRaw)
    {zeroA : Term context Ty.bool zeroRawA}
    {zeroB : Term context Ty.bool zeroRawB}
    (succBranch : Term context (Ty.arrow Ty.nat Ty.bool) succRaw)
    (zeroConv : Conv zeroA zeroB) :
    Conv (Term.natElim scrutinee zeroA succBranch)
         (Term.natElim scrutinee zeroB succBranch) :=
  Conv.cong_at_isClosedTy
    (resultTy := Ty.bool) IsClosedTy.bool
    (wrapRaw := fun raw => RawTerm.natElim scrutRaw raw succRaw)
    (fun term => Term.natElim scrutinee term succBranch)
    (fun step => Step.natElimZero step) zeroConv

/-- `Conv` on `natElim`'s zero-branch at `Ty.nat` motive. -/
theorem Conv.natElimZero_cong_nat
    {scrutRaw zeroRawA zeroRawB succRaw : RawTerm scope}
    (scrutinee : Term context Ty.nat scrutRaw)
    {zeroA : Term context Ty.nat zeroRawA}
    {zeroB : Term context Ty.nat zeroRawB}
    (succBranch : Term context (Ty.arrow Ty.nat Ty.nat) succRaw)
    (zeroConv : Conv zeroA zeroB) :
    Conv (Term.natElim scrutinee zeroA succBranch)
         (Term.natElim scrutinee zeroB succBranch) :=
  Conv.cong_at_isClosedTy
    (resultTy := Ty.nat) IsClosedTy.nat
    (wrapRaw := fun raw => RawTerm.natElim scrutRaw raw succRaw)
    (fun term => Term.natElim scrutinee term succBranch)
    (fun step => Step.natElimZero step) zeroConv

/-- `Conv` on `natRec`'s zero-branch at `Ty.unit` motive. -/
theorem Conv.natRecZero_cong_unit
    {scrutRaw zeroRawA zeroRawB succRaw : RawTerm scope}
    (scrutinee : Term context Ty.nat scrutRaw)
    {zeroA : Term context Ty.unit zeroRawA}
    {zeroB : Term context Ty.unit zeroRawB}
    (succBranch : Term context
                    (Ty.arrow Ty.nat (Ty.arrow Ty.unit Ty.unit)) succRaw)
    (zeroConv : Conv zeroA zeroB) :
    Conv (Term.natRec scrutinee zeroA succBranch)
         (Term.natRec scrutinee zeroB succBranch) :=
  Conv.cong_at_isClosedTy
    (resultTy := Ty.unit) IsClosedTy.unit
    (wrapRaw := fun raw => RawTerm.natRec scrutRaw raw succRaw)
    (fun term => Term.natRec scrutinee term succBranch)
    (fun step => Step.natRecZero step) zeroConv

end LeanFX2
