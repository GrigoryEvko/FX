import LeanFX2.Term.SubjectReductionGeneral

/-! # Term/SubjectReduction — per-type SR specializations + cong lifters

Per-type subject reduction at the closed leaves (`Ty.unit`,
`Ty.bool`, `Ty.nat`) plus cong-rule lifters at those types.

## Architecture (post-refactor)

The general SR theorems (`Step.preserves_isClosedTy`,
`StepStar.preserves_isClosedTy`) and their leaf-invariance
building blocks live in `Term/SubjectReductionGeneral.lean`.
This file consumes them to produce the per-type specializations
that downstream callers (`Reduction/ConvCanonical.lean`, the
cong-rule lifters below) need.

Per-type lemmas are now **one-line corollaries** of the general
theorem instantiated at `IsClosedTy.{unit, bool, nat}`.  This
reduces ~80 lines of duplicate proof to ~12 lines while keeping
the same call-site API.

## What's proved here

* `Step.preserves_ty_unit / bool / nat` — corollaries
* `StepStar.preserves_ty_unit / bool / nat` — corollaries
* `StepStar.{natSucc, boolElimScrutinee, natElimScrutinee,
   natRecScrutinee}_lift` — cong-rule lifters
* `StepStar.boolElim{Then,Else}Branch_lift` — branch lifters at
   closed motive types

## What's elsewhere

* General SR (over `IsClosedTy`): `SubjectReductionGeneral.lean`
* Closed-type families (arrow, list, option, either):
  `SubjectReductionGeneral.lean`
* Open-type SR (piTy, sigmaTy, id, ...): deferred to a later
  phase requiring richer machinery.
-/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}

/-! ## Per-type SR corollaries

Each is a one-line specialization of `Step.preserves_isClosedTy`
(resp. StepStar variant) at the matching `IsClosedTy` leaf
witness.  Functionally equivalent to the previous bespoke
proofs; the same `induction someStep + first` tactic combo lives
in the general theorem rather than being duplicated three times. -/

/-- Subject reduction for `Ty.nat`: every `Step` whose source
type is `Ty.nat` produces a target of type `Ty.nat`. -/
theorem Step.preserves_ty_nat
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    (someStep : Step sourceTerm targetTerm)
    (sourceIsNat : sourceType = Ty.nat) :
    targetType = Ty.nat :=
  Step.preserves_isClosedTy IsClosedTy.nat someStep sourceIsNat

/-- Subject reduction for `Ty.unit`. -/
theorem Step.preserves_ty_unit
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    (someStep : Step sourceTerm targetTerm)
    (sourceIsUnit : sourceType = Ty.unit) :
    targetType = Ty.unit :=
  Step.preserves_isClosedTy IsClosedTy.unit someStep sourceIsUnit

/-- Subject reduction for `Ty.bool`. -/
theorem Step.preserves_ty_bool
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    (someStep : Step sourceTerm targetTerm)
    (sourceIsBool : sourceType = Ty.bool) :
    targetType = Ty.bool :=
  Step.preserves_isClosedTy IsClosedTy.bool someStep sourceIsBool

/-! ## Lifts to StepStar -/

/-- Subject reduction extended to `StepStar` for `Ty.nat`. -/
theorem StepStar.preserves_ty_nat
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    (chain : StepStar sourceTerm targetTerm)
    (sourceIsNat : sourceType = Ty.nat) :
    targetType = Ty.nat :=
  StepStar.preserves_isClosedTy IsClosedTy.nat chain sourceIsNat

/-- Subject reduction extended to `StepStar` for `Ty.unit`. -/
theorem StepStar.preserves_ty_unit
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    (chain : StepStar sourceTerm targetTerm)
    (sourceIsUnit : sourceType = Ty.unit) :
    targetType = Ty.unit :=
  StepStar.preserves_isClosedTy IsClosedTy.unit chain sourceIsUnit

/-- Subject reduction extended to `StepStar` for `Ty.bool`. -/
theorem StepStar.preserves_ty_bool
    {sourceType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetType : Ty level scope}
    {targetTerm : Term context targetType targetRaw}
    (chain : StepStar sourceTerm targetTerm)
    (sourceIsBool : sourceType = Ty.bool) :
    targetType = Ty.bool :=
  StepStar.preserves_isClosedTy IsClosedTy.bool chain sourceIsBool

/-! ## Cong-rule lifters at `Ty.nat`

Subject reduction enables a single-binder cong rule
`StepStar.natSucc_lift`: any `StepStar` between nat-typed terms
lifts to a `StepStar` between their `natSucc`-wrappers.  This
is the workhorse for `Conv.canonical_natSucc`. -/

/-- Generalized lift: any `StepStar` chain whose source/target
are nat-typed lifts to a `StepStar` chain on the `natSucc`-wrappers.
1-step parameterization of `StepStar.lift_at_isClosedTy` at
`IsClosedTy.nat` + the `Term.natSucc` wrapper. -/
theorem StepStar.natSucc_lift_general
    {srcTy tgtTy : Ty level scope}
    {srcRaw tgtRaw : RawTerm scope}
    {srcTerm : Term context srcTy srcRaw}
    {tgtTerm : Term context tgtTy tgtRaw}
    (someChain : StepStar srcTerm tgtTerm)
    (srcIsNat : srcTy = Ty.nat)
    (tgtIsNat : tgtTy = Ty.nat) :
    StepStar (Term.natSucc (srcIsNat ▸ srcTerm))
             (Term.natSucc (tgtIsNat ▸ tgtTerm)) :=
  StepStar.lift_at_isClosedTy
    (resultTy := Ty.nat) IsClosedTy.nat
    (wrapRaw := RawTerm.natSucc) (fun term => Term.natSucc term)
    (fun step => Step.natSuccPred step)
    someChain srcIsNat tgtIsNat

/-- Lift a `StepStar` chain between nat-typed terms to a
`StepStar` chain between their `natSucc`-wrappers. -/
theorem StepStar.natSucc_lift
    {predRawSource predRawTarget : RawTerm scope}
    {predSource : Term context Ty.nat predRawSource}
    {predTarget : Term context Ty.nat predRawTarget}
    (chain : StepStar predSource predTarget) :
    StepStar (Term.natSucc predSource) (Term.natSucc predTarget) :=
  StepStar.natSucc_lift_general chain rfl rfl

/-! ## Scrutinee lifters at closed types

For each eliminator with a closed-type scrutinee
(`boolElim`/`natElim`/`natRec` at `Ty.bool`/`Ty.nat`),
subject reduction enables a cong rule that lifts a `StepStar`
on the scrutinee to a `StepStar` on the eliminator outer. -/

/-- Generalized lift for `boolElim` scrutinee cong.  1-step
parameterization of `StepStar.lift_at_isClosedTy`. -/
theorem StepStar.boolElimScrutinee_lift_general
    {srcTy tgtTy : Ty level scope}
    {srcRaw tgtRaw : RawTerm scope}
    {srcTerm : Term context srcTy srcRaw}
    {tgtTerm : Term context tgtTy tgtRaw}
    (someChain : StepStar srcTerm tgtTerm)
    (srcIsBool : srcTy = Ty.bool)
    (tgtIsBool : tgtTy = Ty.bool)
    {motiveType : Ty level scope}
    {thenRaw elseRaw : RawTerm scope}
    (thenBranch : Term context motiveType thenRaw)
    (elseBranch : Term context motiveType elseRaw) :
    StepStar (Term.boolElim (srcIsBool ▸ srcTerm) thenBranch elseBranch)
             (Term.boolElim (tgtIsBool ▸ tgtTerm) thenBranch elseBranch) :=
  StepStar.lift_at_isClosedTy
    (resultTy := motiveType) IsClosedTy.bool
    (wrapRaw := fun raw => RawTerm.boolElim raw thenRaw elseRaw)
    (fun term => Term.boolElim term thenBranch elseBranch)
    (fun step => Step.boolElimScrutinee step)
    someChain srcIsBool tgtIsBool

/-- Lift a `StepStar` between bool-typed terms to a `StepStar`
between `boolElim`-wrappers. -/
theorem StepStar.boolElimScrutinee_lift
    {scrutRawA scrutRawB : RawTerm scope}
    {scrutA : Term context Ty.bool scrutRawA}
    {scrutB : Term context Ty.bool scrutRawB}
    (chain : StepStar scrutA scrutB)
    {motiveType : Ty level scope}
    {thenRaw elseRaw : RawTerm scope}
    (thenBranch : Term context motiveType thenRaw)
    (elseBranch : Term context motiveType elseRaw) :
    StepStar (Term.boolElim scrutA thenBranch elseBranch)
             (Term.boolElim scrutB thenBranch elseBranch) :=
  StepStar.boolElimScrutinee_lift_general chain rfl rfl thenBranch elseBranch

/-- Generalized lift for `natElim` scrutinee cong.  1-step
parameterization of `StepStar.lift_at_isClosedTy`. -/
theorem StepStar.natElimScrutinee_lift_general
    {srcTy tgtTy : Ty level scope}
    {srcRaw tgtRaw : RawTerm scope}
    {srcTerm : Term context srcTy srcRaw}
    {tgtTerm : Term context tgtTy tgtRaw}
    (someChain : StepStar srcTerm tgtTerm)
    (srcIsNat : srcTy = Ty.nat)
    (tgtIsNat : tgtTy = Ty.nat)
    {motiveType : Ty level scope}
    {zeroRaw succRaw : RawTerm scope}
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw) :
    StepStar (Term.natElim (srcIsNat ▸ srcTerm) zeroBranch succBranch)
             (Term.natElim (tgtIsNat ▸ tgtTerm) zeroBranch succBranch) :=
  StepStar.lift_at_isClosedTy
    (resultTy := motiveType) IsClosedTy.nat
    (wrapRaw := fun raw => RawTerm.natElim raw zeroRaw succRaw)
    (fun term => Term.natElim term zeroBranch succBranch)
    (fun step => Step.natElimScrutinee step)
    someChain srcIsNat tgtIsNat

/-- Lift a `StepStar` between nat-typed terms to a `StepStar`
between `natElim`-wrappers. -/
theorem StepStar.natElimScrutinee_lift
    {scrutRawA scrutRawB : RawTerm scope}
    {scrutA : Term context Ty.nat scrutRawA}
    {scrutB : Term context Ty.nat scrutRawB}
    (chain : StepStar scrutA scrutB)
    {motiveType : Ty level scope}
    {zeroRaw succRaw : RawTerm scope}
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw) :
    StepStar (Term.natElim scrutA zeroBranch succBranch)
             (Term.natElim scrutB zeroBranch succBranch) :=
  StepStar.natElimScrutinee_lift_general chain rfl rfl zeroBranch succBranch

/-- Generalized lift for `natRec` scrutinee cong.  1-step
parameterization of `StepStar.lift_at_isClosedTy`. -/
theorem StepStar.natRecScrutinee_lift_general
    {srcTy tgtTy : Ty level scope}
    {srcRaw tgtRaw : RawTerm scope}
    {srcTerm : Term context srcTy srcRaw}
    {tgtTerm : Term context tgtTy tgtRaw}
    (someChain : StepStar srcTerm tgtTerm)
    (srcIsNat : srcTy = Ty.nat)
    (tgtIsNat : tgtTy = Ty.nat)
    {motiveType : Ty level scope}
    {zeroRaw succRaw : RawTerm scope}
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch : Term context
                    (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw) :
    StepStar (Term.natRec (srcIsNat ▸ srcTerm) zeroBranch succBranch)
             (Term.natRec (tgtIsNat ▸ tgtTerm) zeroBranch succBranch) :=
  StepStar.lift_at_isClosedTy
    (resultTy := motiveType) IsClosedTy.nat
    (wrapRaw := fun raw => RawTerm.natRec raw zeroRaw succRaw)
    (fun term => Term.natRec term zeroBranch succBranch)
    (fun step => Step.natRecScrutinee step)
    someChain srcIsNat tgtIsNat

/-- Lift a `StepStar` between nat-typed terms to a `StepStar`
between `natRec`-wrappers. -/
theorem StepStar.natRecScrutinee_lift
    {scrutRawA scrutRawB : RawTerm scope}
    {scrutA : Term context Ty.nat scrutRawA}
    {scrutB : Term context Ty.nat scrutRawB}
    (chain : StepStar scrutA scrutB)
    {motiveType : Ty level scope}
    {zeroRaw succRaw : RawTerm scope}
    (zeroBranch : Term context motiveType zeroRaw)
    (succBranch : Term context
                    (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType)) succRaw) :
    StepStar (Term.natRec scrutA zeroBranch succBranch)
             (Term.natRec scrutB zeroBranch succBranch) :=
  StepStar.natRecScrutinee_lift_general chain rfl rfl zeroBranch succBranch

/-! ## Branch lifters — REMOVED.

Previous versions of this file shipped 10 hand-rolled branch
lifters (boolElimThen + boolElimElse + natElimZero + natRecZero,
each with a `_lift_generic` parameterized variant + 3 per-motive
`_lift_general_X` specializations).  They are all subsumed by
`StepStar.lift_at_isClosedTy` (the generic IsClosedTy chain
lifter).

Downstream `Conv.X_cong_Y` rules in
`Reduction/ConvCanonical.lean` now invoke
`Conv.cong_at_isClosedTy` directly, parameterized by the
matching wrapper Term + Step cong ctor.  No external code refers
to the removed lifters; ~230 lines of bespoke proof eliminated. -/

end LeanFX2
