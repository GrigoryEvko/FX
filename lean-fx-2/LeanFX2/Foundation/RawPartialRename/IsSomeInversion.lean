import LeanFX2.Foundation.RawPartialRename.Strengthen

/-! # Foundation/RawPartialRename/IsSomeInversion

Per-`RawTerm`-constructor inversion of `(RawTerm.<ctor> args).partialRename? back`
from the composite `.isSome = true` to per-sub-field `.isSome = true`.

These are the raw-side siblings of the Ty inversion lemmas in
`Foundation/TyStrengthenInversion.lean`.  Each multi-child `RawTerm`
constructor's `partialRename?` is defined via `Option.mapTwo` /
`Option.mapThree` / a direct `match`; the composite succeeds iff
every sub-field succeeds.  Inversion at the success direction is
structurally trivial — `dsimp only` unfolds the constructor's arm,
then nested `match` cases extract per-sub-field `partialRename?`
witnesses and discharge impossible `none` arms via `cases`.

These inversion lemmas are consumed by the eventual universal
typed-strengthening driver (Block B `Step.par.preserves_rename_image`,
#2022): the structural-induction driver dispatches type-side
hypotheses through `Foundation/TyStrengthenInversion.lean`
counterparts and raw-side hypotheses through the lemmas in this
file.

## Pilot coverage

This pilot ships 6 representative ctors across binder / Option.mapTwo
binary / Option.mapTwo + match shapes:

* `lam` (1-child binder via `partialRenaming.lift`)
* `app` (2-child `Option.mapTwo`)
* `pair` (2-child `Option.mapTwo`)
* `fst` (1-child direct `match`)
* `snd` (1-child direct `match`)
* `listCons` (2-child `Option.mapTwo`)

Future ralph cycles can clone the same recipe for the remaining
65+ `RawTerm` ctors. Each lemma is mechanically identical except for
which child's `match` is being scrutinised.

## Tactics

`dsimp only [RawTerm.partialRename?, Option.mapTwo]` unfolds the
constructor's arm to the underlying match, then a `match` with
witness extracts per-sub-field `partialRename?` results and
discharges impossible cases via `cases`.  Zero axioms. -/

namespace LeanFX2

namespace RawTerm

variable {sourceScope targetScope : Nat}

/-- Inversion of `RawTerm.lam` partial-renaming `.isSome`.

If the composite lam strengthens, the body (under the lifted
back-renaming) also strengthens. -/
theorem partialRename?_lam_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (body : RawTerm (sourceScope + 1))
    (composite :
      ((RawTerm.lam body).partialRename? back).isSome = true) :
    (body.partialRename? back.lift).isSome = true := by
  dsimp only [RawTerm.partialRename?] at composite
  match bodyBranch : body.partialRename? back.lift with
  | none => rw [bodyBranch] at composite; cases composite
  | some _ => rfl

/-- Inversion of `RawTerm.app` partial-renaming `.isSome`.

If the composite app strengthens, both function and argument
strengthen. -/
theorem partialRename?_app_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (functionTerm argumentTerm : RawTerm sourceScope)
    (composite :
      ((RawTerm.app functionTerm argumentTerm).partialRename? back).isSome
        = true) :
    (functionTerm.partialRename? back).isSome = true ∧
      (argumentTerm.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?, Option.mapTwo] at composite
  refine ⟨?_, ?_⟩
  · match functionBranch : functionTerm.partialRename? back with
    | none => rw [functionBranch] at composite; cases composite
    | some _ => rfl
  · match argumentBranch : argumentTerm.partialRename? back with
    | none =>
        rw [argumentBranch] at composite
        match functionBranch : functionTerm.partialRename? back with
        | none => rw [functionBranch] at composite; cases composite
        | some _ => rw [functionBranch] at composite; cases composite
    | some _ => rfl

/-- Inversion of `RawTerm.pair` partial-renaming `.isSome`.

If the composite pair strengthens, both first and second components
strengthen. -/
theorem partialRename?_pair_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (firstValue secondValue : RawTerm sourceScope)
    (composite :
      ((RawTerm.pair firstValue secondValue).partialRename? back).isSome
        = true) :
    (firstValue.partialRename? back).isSome = true ∧
      (secondValue.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?, Option.mapTwo] at composite
  refine ⟨?_, ?_⟩
  · match firstBranch : firstValue.partialRename? back with
    | none => rw [firstBranch] at composite; cases composite
    | some _ => rfl
  · match secondBranch : secondValue.partialRename? back with
    | none =>
        rw [secondBranch] at composite
        match firstBranch : firstValue.partialRename? back with
        | none => rw [firstBranch] at composite; cases composite
        | some _ => rw [firstBranch] at composite; cases composite
    | some _ => rfl

/-- Inversion of `RawTerm.fst` partial-renaming `.isSome`.

If the composite fst strengthens, the pair payload strengthens. -/
theorem partialRename?_fst_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (pairTerm : RawTerm sourceScope)
    (composite :
      ((RawTerm.fst pairTerm).partialRename? back).isSome = true) :
    (pairTerm.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?] at composite
  match pairBranch : pairTerm.partialRename? back with
  | none => rw [pairBranch] at composite; cases composite
  | some _ => rfl

/-- Inversion of `RawTerm.snd` partial-renaming `.isSome`.

If the composite snd strengthens, the pair payload strengthens. -/
theorem partialRename?_snd_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (pairTerm : RawTerm sourceScope)
    (composite :
      ((RawTerm.snd pairTerm).partialRename? back).isSome = true) :
    (pairTerm.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?] at composite
  match pairBranch : pairTerm.partialRename? back with
  | none => rw [pairBranch] at composite; cases composite
  | some _ => rfl

/-- Inversion of `RawTerm.listCons` partial-renaming `.isSome`.

If the composite listCons strengthens, both head and tail
strengthen. -/
theorem partialRename?_listCons_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (headTerm tailTerm : RawTerm sourceScope)
    (composite :
      ((RawTerm.listCons headTerm tailTerm).partialRename? back).isSome
        = true) :
    (headTerm.partialRename? back).isSome = true ∧
      (tailTerm.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?, Option.mapTwo] at composite
  refine ⟨?_, ?_⟩
  · match headBranch : headTerm.partialRename? back with
    | none => rw [headBranch] at composite; cases composite
    | some _ => rfl
  · match tailBranch : tailTerm.partialRename? back with
    | none =>
        rw [tailBranch] at composite
        match headBranch : headTerm.partialRename? back with
        | none => rw [headBranch] at composite; cases composite
        | some _ => rw [headBranch] at composite; cases composite
    | some _ => rfl

/-- Inversion of `RawTerm.natSucc` partial-renaming `.isSome`.

If the composite natSucc strengthens, the predecessor strengthens. -/
theorem partialRename?_natSucc_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (predecessor : RawTerm sourceScope)
    (composite :
      ((RawTerm.natSucc predecessor).partialRename? back).isSome = true) :
    (predecessor.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?] at composite
  match predecessorBranch : predecessor.partialRename? back with
  | none => rw [predecessorBranch] at composite; cases composite
  | some _ => rfl

/-- Inversion of `RawTerm.optionSome` partial-renaming `.isSome`.

If the composite optionSome strengthens, the wrapped value strengthens. -/
theorem partialRename?_optionSome_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (valueTerm : RawTerm sourceScope)
    (composite :
      ((RawTerm.optionSome valueTerm).partialRename? back).isSome = true) :
    (valueTerm.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?] at composite
  match valueBranch : valueTerm.partialRename? back with
  | none => rw [valueBranch] at composite; cases composite
  | some _ => rfl

/-- Inversion of `RawTerm.eitherInl` partial-renaming `.isSome`.

If the composite eitherInl strengthens, the wrapped value strengthens. -/
theorem partialRename?_eitherInl_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (valueTerm : RawTerm sourceScope)
    (composite :
      ((RawTerm.eitherInl valueTerm).partialRename? back).isSome = true) :
    (valueTerm.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?] at composite
  match valueBranch : valueTerm.partialRename? back with
  | none => rw [valueBranch] at composite; cases composite
  | some _ => rfl

/-- Inversion of `RawTerm.eitherInr` partial-renaming `.isSome`.

If the composite eitherInr strengthens, the wrapped value strengthens. -/
theorem partialRename?_eitherInr_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (valueTerm : RawTerm sourceScope)
    (composite :
      ((RawTerm.eitherInr valueTerm).partialRename? back).isSome = true) :
    (valueTerm.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?] at composite
  match valueBranch : valueTerm.partialRename? back with
  | none => rw [valueBranch] at composite; cases composite
  | some _ => rfl

/-- Inversion of `RawTerm.refl` partial-renaming `.isSome`.

If the composite refl strengthens, the witness strengthens. -/
theorem partialRename?_refl_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (rawWitness : RawTerm sourceScope)
    (composite :
      ((RawTerm.refl rawWitness).partialRename? back).isSome = true) :
    (rawWitness.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?] at composite
  match witnessBranch : rawWitness.partialRename? back with
  | none => rw [witnessBranch] at composite; cases composite
  | some _ => rfl

/-- Inversion of `RawTerm.modIntro` partial-renaming `.isSome`.

If the composite modIntro strengthens, the wrapped raw strengthens. -/
theorem partialRename?_modIntro_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (raw : RawTerm sourceScope)
    (composite :
      ((RawTerm.modIntro raw).partialRename? back).isSome = true) :
    (raw.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?] at composite
  match rawBranch : raw.partialRename? back with
  | none => rw [rawBranch] at composite; cases composite
  | some _ => rfl

/-- Inversion of `RawTerm.modElim` partial-renaming `.isSome`.

If the composite modElim strengthens, the wrapped raw strengthens. -/
theorem partialRename?_modElim_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (raw : RawTerm sourceScope)
    (composite :
      ((RawTerm.modElim raw).partialRename? back).isSome = true) :
    (raw.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?] at composite
  match rawBranch : raw.partialRename? back with
  | none => rw [rawBranch] at composite; cases composite
  | some _ => rfl

/-- Inversion of `RawTerm.subsume` partial-renaming `.isSome`.

If the composite subsume strengthens, the wrapped raw strengthens. -/
theorem partialRename?_subsume_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (raw : RawTerm sourceScope)
    (composite :
      ((RawTerm.subsume raw).partialRename? back).isSome = true) :
    (raw.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?] at composite
  match rawBranch : raw.partialRename? back with
  | none => rw [rawBranch] at composite; cases composite
  | some _ => rfl

/-- Inversion of `RawTerm.intervalOpp` partial-renaming `.isSome`.

If the composite intervalOpp strengthens, the interval child strengthens. -/
theorem partialRename?_intervalOpp_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (intervalTerm : RawTerm sourceScope)
    (composite :
      ((RawTerm.intervalOpp intervalTerm).partialRename? back).isSome
        = true) :
    (intervalTerm.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?] at composite
  match intervalBranch : intervalTerm.partialRename? back with
  | none => rw [intervalBranch] at composite; cases composite
  | some _ => rfl

/-- Inversion of `RawTerm.glueElim` partial-renaming `.isSome`.

If the composite glueElim strengthens, the glued value strengthens. -/
theorem partialRename?_glueElim_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (gluedValue : RawTerm sourceScope)
    (composite :
      ((RawTerm.glueElim gluedValue).partialRename? back).isSome = true) :
    (gluedValue.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?] at composite
  match gluedBranch : gluedValue.partialRename? back with
  | none => rw [gluedBranch] at composite; cases composite
  | some _ => rfl

/-- Inversion of `RawTerm.idJ` partial-renaming `.isSome`.

If the composite idJ strengthens, both base case and witness
strengthen. -/
theorem partialRename?_idJ_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (baseCase witness : RawTerm sourceScope)
    (composite :
      ((RawTerm.idJ baseCase witness).partialRename? back).isSome = true) :
    (baseCase.partialRename? back).isSome = true ∧
      (witness.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?, Option.mapTwo] at composite
  refine ⟨?_, ?_⟩
  · match baseBranch : baseCase.partialRename? back with
    | none => rw [baseBranch] at composite; cases composite
    | some _ => rfl
  · match witnessBranch : witness.partialRename? back with
    | none =>
        rw [witnessBranch] at composite
        match baseBranch : baseCase.partialRename? back with
        | none => rw [baseBranch] at composite; cases composite
        | some _ => rw [baseBranch] at composite; cases composite
    | some _ => rfl

/-- Inversion of `RawTerm.intervalMeet` partial-renaming `.isSome`.

If the composite intervalMeet strengthens, both interval operands
strengthen. -/
theorem partialRename?_intervalMeet_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (leftInterval rightInterval : RawTerm sourceScope)
    (composite :
      ((RawTerm.intervalMeet leftInterval rightInterval).partialRename?
          back).isSome = true) :
    (leftInterval.partialRename? back).isSome = true ∧
      (rightInterval.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?, Option.mapTwo] at composite
  refine ⟨?_, ?_⟩
  · match leftBranch : leftInterval.partialRename? back with
    | none => rw [leftBranch] at composite; cases composite
    | some _ => rfl
  · match rightBranch : rightInterval.partialRename? back with
    | none =>
        rw [rightBranch] at composite
        match leftBranch : leftInterval.partialRename? back with
        | none => rw [leftBranch] at composite; cases composite
        | some _ => rw [leftBranch] at composite; cases composite
    | some _ => rfl

/-- Inversion of `RawTerm.intervalJoin` partial-renaming `.isSome`.

If the composite intervalJoin strengthens, both interval operands
strengthen. -/
theorem partialRename?_intervalJoin_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (leftInterval rightInterval : RawTerm sourceScope)
    (composite :
      ((RawTerm.intervalJoin leftInterval rightInterval).partialRename?
          back).isSome = true) :
    (leftInterval.partialRename? back).isSome = true ∧
      (rightInterval.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?, Option.mapTwo] at composite
  refine ⟨?_, ?_⟩
  · match leftBranch : leftInterval.partialRename? back with
    | none => rw [leftBranch] at composite; cases composite
    | some _ => rfl
  · match rightBranch : rightInterval.partialRename? back with
    | none =>
        rw [rightBranch] at composite
        match leftBranch : leftInterval.partialRename? back with
        | none => rw [leftBranch] at composite; cases composite
        | some _ => rw [leftBranch] at composite; cases composite
    | some _ => rfl

/-- Inversion of `RawTerm.pathApp` partial-renaming `.isSome`.

If the composite pathApp strengthens, both path term and interval
argument strengthen. -/
theorem partialRename?_pathApp_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (pathTerm intervalArg : RawTerm sourceScope)
    (composite :
      ((RawTerm.pathApp pathTerm intervalArg).partialRename? back).isSome
        = true) :
    (pathTerm.partialRename? back).isSome = true ∧
      (intervalArg.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?, Option.mapTwo] at composite
  refine ⟨?_, ?_⟩
  · match pathBranch : pathTerm.partialRename? back with
    | none => rw [pathBranch] at composite; cases composite
    | some _ => rfl
  · match intervalBranch : intervalArg.partialRename? back with
    | none =>
        rw [intervalBranch] at composite
        match pathBranch : pathTerm.partialRename? back with
        | none => rw [pathBranch] at composite; cases composite
        | some _ => rw [pathBranch] at composite; cases composite
    | some _ => rfl

/-- Inversion of `RawTerm.glueIntro` partial-renaming `.isSome`.

If the composite glueIntro strengthens, both base value and partial
value strengthen. -/
theorem partialRename?_glueIntro_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (baseValue partialValue : RawTerm sourceScope)
    (composite :
      ((RawTerm.glueIntro baseValue partialValue).partialRename?
          back).isSome = true) :
    (baseValue.partialRename? back).isSome = true ∧
      (partialValue.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?, Option.mapTwo] at composite
  refine ⟨?_, ?_⟩
  · match baseBranch : baseValue.partialRename? back with
    | none => rw [baseBranch] at composite; cases composite
    | some _ => rfl
  · match partialBranch : partialValue.partialRename? back with
    | none =>
        rw [partialBranch] at composite
        match baseBranch : baseValue.partialRename? back with
        | none => rw [baseBranch] at composite; cases composite
        | some _ => rw [baseBranch] at composite; cases composite
    | some _ => rfl

/-- Inversion of `RawTerm.transp` partial-renaming `.isSome`.

If the composite transp strengthens, both path and source
strengthen. -/
theorem partialRename?_transp_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (path source : RawTerm sourceScope)
    (composite :
      ((RawTerm.transp path source).partialRename? back).isSome
        = true) :
    (path.partialRename? back).isSome = true ∧
      (source.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?, Option.mapTwo] at composite
  refine ⟨?_, ?_⟩
  · match pathBranch : path.partialRename? back with
    | none => rw [pathBranch] at composite; cases composite
    | some _ => rfl
  · match sourceBranch : source.partialRename? back with
    | none =>
        rw [sourceBranch] at composite
        match pathBranch : path.partialRename? back with
        | none => rw [pathBranch] at composite; cases composite
        | some _ => rw [pathBranch] at composite; cases composite
    | some _ => rfl

/-- Inversion of `RawTerm.boolElim` partial-renaming `.isSome`.

If the composite boolElim strengthens, scrutinee, then-branch, and
else-branch all strengthen. -/
theorem partialRename?_boolElim_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (scrutinee thenBranch elseBranch : RawTerm sourceScope)
    (composite :
      ((RawTerm.boolElim scrutinee thenBranch elseBranch).partialRename?
          back).isSome = true) :
    (scrutinee.partialRename? back).isSome = true ∧
      (thenBranch.partialRename? back).isSome = true ∧
        (elseBranch.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?, Option.mapThree] at composite
  refine ⟨?_, ?_, ?_⟩
  · match scrutBranch : scrutinee.partialRename? back with
    | none => rw [scrutBranch] at composite; cases composite
    | some _ => rfl
  · match thenBr : thenBranch.partialRename? back with
    | none =>
        rw [thenBr] at composite
        match scrutBranch : scrutinee.partialRename? back with
        | none => rw [scrutBranch] at composite; cases composite
        | some _ => rw [scrutBranch] at composite; cases composite
    | some _ => rfl
  · match elseBr : elseBranch.partialRename? back with
    | none =>
        rw [elseBr] at composite
        match scrutBranch : scrutinee.partialRename? back with
        | none => rw [scrutBranch] at composite; cases composite
        | some _ =>
            match thenBr : thenBranch.partialRename? back with
            | none =>
                rw [scrutBranch, thenBr] at composite
                cases composite
            | some _ =>
                rw [scrutBranch, thenBr] at composite
                cases composite
    | some _ => rfl

/-- Inversion of `RawTerm.natElim` partial-renaming `.isSome`.

If the composite natElim strengthens, scrutinee, zero-branch, and
successor-branch all strengthen. -/
theorem partialRename?_natElim_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (scrutinee zeroBranch succBranch : RawTerm sourceScope)
    (composite :
      ((RawTerm.natElim scrutinee zeroBranch succBranch).partialRename?
          back).isSome = true) :
    (scrutinee.partialRename? back).isSome = true ∧
      (zeroBranch.partialRename? back).isSome = true ∧
        (succBranch.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?, Option.mapThree] at composite
  refine ⟨?_, ?_, ?_⟩
  · match scrutBranch : scrutinee.partialRename? back with
    | none => rw [scrutBranch] at composite; cases composite
    | some _ => rfl
  · match zeroBr : zeroBranch.partialRename? back with
    | none =>
        rw [zeroBr] at composite
        match scrutBranch : scrutinee.partialRename? back with
        | none => rw [scrutBranch] at composite; cases composite
        | some _ => rw [scrutBranch] at composite; cases composite
    | some _ => rfl
  · match succBr : succBranch.partialRename? back with
    | none =>
        rw [succBr] at composite
        match scrutBranch : scrutinee.partialRename? back with
        | none => rw [scrutBranch] at composite; cases composite
        | some _ =>
            match zeroBr : zeroBranch.partialRename? back with
            | none =>
                rw [scrutBranch, zeroBr] at composite
                cases composite
            | some _ =>
                rw [scrutBranch, zeroBr] at composite
                cases composite
    | some _ => rfl

/-- Inversion of `RawTerm.natRec` partial-renaming `.isSome`.

If the composite natRec strengthens, scrutinee, zero-branch, and
successor-branch all strengthen. -/
theorem partialRename?_natRec_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (scrutinee zeroBranch succBranch : RawTerm sourceScope)
    (composite :
      ((RawTerm.natRec scrutinee zeroBranch succBranch).partialRename?
          back).isSome = true) :
    (scrutinee.partialRename? back).isSome = true ∧
      (zeroBranch.partialRename? back).isSome = true ∧
        (succBranch.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?, Option.mapThree] at composite
  refine ⟨?_, ?_, ?_⟩
  · match scrutBranch : scrutinee.partialRename? back with
    | none => rw [scrutBranch] at composite; cases composite
    | some _ => rfl
  · match zeroBr : zeroBranch.partialRename? back with
    | none =>
        rw [zeroBr] at composite
        match scrutBranch : scrutinee.partialRename? back with
        | none => rw [scrutBranch] at composite; cases composite
        | some _ => rw [scrutBranch] at composite; cases composite
    | some _ => rfl
  · match succBr : succBranch.partialRename? back with
    | none =>
        rw [succBr] at composite
        match scrutBranch : scrutinee.partialRename? back with
        | none => rw [scrutBranch] at composite; cases composite
        | some _ =>
            match zeroBr : zeroBranch.partialRename? back with
            | none =>
                rw [scrutBranch, zeroBr] at composite
                cases composite
            | some _ =>
                rw [scrutBranch, zeroBr] at composite
                cases composite
    | some _ => rfl

/-- Inversion of `RawTerm.listElim` partial-renaming `.isSome`.

If the composite listElim strengthens, scrutinee, nil-branch, and
cons-branch all strengthen. -/
theorem partialRename?_listElim_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (scrutinee nilBranch consBranch : RawTerm sourceScope)
    (composite :
      ((RawTerm.listElim scrutinee nilBranch consBranch).partialRename?
          back).isSome = true) :
    (scrutinee.partialRename? back).isSome = true ∧
      (nilBranch.partialRename? back).isSome = true ∧
        (consBranch.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?, Option.mapThree] at composite
  refine ⟨?_, ?_, ?_⟩
  · match scrutBranch : scrutinee.partialRename? back with
    | none => rw [scrutBranch] at composite; cases composite
    | some _ => rfl
  · match nilBr : nilBranch.partialRename? back with
    | none =>
        rw [nilBr] at composite
        match scrutBranch : scrutinee.partialRename? back with
        | none => rw [scrutBranch] at composite; cases composite
        | some _ => rw [scrutBranch] at composite; cases composite
    | some _ => rfl
  · match consBr : consBranch.partialRename? back with
    | none =>
        rw [consBr] at composite
        match scrutBranch : scrutinee.partialRename? back with
        | none => rw [scrutBranch] at composite; cases composite
        | some _ =>
            match nilBr : nilBranch.partialRename? back with
            | none =>
                rw [scrutBranch, nilBr] at composite
                cases composite
            | some _ =>
                rw [scrutBranch, nilBr] at composite
                cases composite
    | some _ => rfl

/-- Inversion of `RawTerm.optionMatch` partial-renaming `.isSome`.

If the composite optionMatch strengthens, scrutinee, none-branch, and
some-branch all strengthen. -/
theorem partialRename?_optionMatch_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (scrutinee noneBranch someBranch : RawTerm sourceScope)
    (composite :
      ((RawTerm.optionMatch scrutinee noneBranch someBranch).partialRename?
          back).isSome = true) :
    (scrutinee.partialRename? back).isSome = true ∧
      (noneBranch.partialRename? back).isSome = true ∧
        (someBranch.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?, Option.mapThree] at composite
  refine ⟨?_, ?_, ?_⟩
  · match scrutBranch : scrutinee.partialRename? back with
    | none => rw [scrutBranch] at composite; cases composite
    | some _ => rfl
  · match noneBr : noneBranch.partialRename? back with
    | none =>
        rw [noneBr] at composite
        match scrutBranch : scrutinee.partialRename? back with
        | none => rw [scrutBranch] at composite; cases composite
        | some _ => rw [scrutBranch] at composite; cases composite
    | some _ => rfl
  · match someBr : someBranch.partialRename? back with
    | none =>
        rw [someBr] at composite
        match scrutBranch : scrutinee.partialRename? back with
        | none => rw [scrutBranch] at composite; cases composite
        | some _ =>
            match noneBr : noneBranch.partialRename? back with
            | none =>
                rw [scrutBranch, noneBr] at composite
                cases composite
            | some _ =>
                rw [scrutBranch, noneBr] at composite
                cases composite
    | some _ => rfl

/-- Inversion of `RawTerm.eitherMatch` partial-renaming `.isSome`.

If the composite eitherMatch strengthens, scrutinee, left-branch,
and right-branch all strengthen. -/
theorem partialRename?_eitherMatch_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (scrutinee leftBranch rightBranch : RawTerm sourceScope)
    (composite :
      ((RawTerm.eitherMatch scrutinee leftBranch rightBranch).partialRename?
          back).isSome = true) :
    (scrutinee.partialRename? back).isSome = true ∧
      (leftBranch.partialRename? back).isSome = true ∧
        (rightBranch.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?, Option.mapThree] at composite
  refine ⟨?_, ?_, ?_⟩
  · match scrutBranch : scrutinee.partialRename? back with
    | none => rw [scrutBranch] at composite; cases composite
    | some _ => rfl
  · match leftBr : leftBranch.partialRename? back with
    | none =>
        rw [leftBr] at composite
        match scrutBranch : scrutinee.partialRename? back with
        | none => rw [scrutBranch] at composite; cases composite
        | some _ => rw [scrutBranch] at composite; cases composite
    | some _ => rfl
  · match rightBr : rightBranch.partialRename? back with
    | none =>
        rw [rightBr] at composite
        match scrutBranch : scrutinee.partialRename? back with
        | none => rw [scrutBranch] at composite; cases composite
        | some _ =>
            match leftBr : leftBranch.partialRename? back with
            | none =>
                rw [scrutBranch, leftBr] at composite
                cases composite
            | some _ =>
                rw [scrutBranch, leftBr] at composite
                cases composite
    | some _ => rfl

/-- Inversion of `RawTerm.oeqRefl` partial-renaming `.isSome`.

If the composite oeqRefl strengthens, the witness strengthens. -/
theorem partialRename?_oeqRefl_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (witnessTerm : RawTerm sourceScope)
    (composite :
      ((RawTerm.oeqRefl witnessTerm).partialRename? back).isSome = true) :
    (witnessTerm.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?] at composite
  match witnessBranch : witnessTerm.partialRename? back with
  | none => rw [witnessBranch] at composite; cases composite
  | some _ => rfl

/-- Inversion of `RawTerm.oeqFunext` partial-renaming `.isSome`.

If the composite oeqFunext strengthens, the pointwise equality
strengthens. -/
theorem partialRename?_oeqFunext_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (pointwiseEquality : RawTerm sourceScope)
    (composite :
      ((RawTerm.oeqFunext pointwiseEquality).partialRename? back).isSome
        = true) :
    (pointwiseEquality.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?] at composite
  match pointwiseBranch : pointwiseEquality.partialRename? back with
  | none => rw [pointwiseBranch] at composite; cases composite
  | some _ => rfl

/-- Inversion of `RawTerm.idStrictRefl` partial-renaming `.isSome`.

If the composite idStrictRefl strengthens, the witness strengthens. -/
theorem partialRename?_idStrictRefl_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (witnessTerm : RawTerm sourceScope)
    (composite :
      ((RawTerm.idStrictRefl witnessTerm).partialRename? back).isSome
        = true) :
    (witnessTerm.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?] at composite
  match witnessBranch : witnessTerm.partialRename? back with
  | none => rw [witnessBranch] at composite; cases composite
  | some _ => rfl

/-- Inversion of `RawTerm.refineElim` partial-renaming `.isSome`.

If the composite refineElim strengthens, the refined value
strengthens. -/
theorem partialRename?_refineElim_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (refinedValue : RawTerm sourceScope)
    (composite :
      ((RawTerm.refineElim refinedValue).partialRename? back).isSome
        = true) :
    (refinedValue.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?] at composite
  match refinedBranch : refinedValue.partialRename? back with
  | none => rw [refinedBranch] at composite; cases composite
  | some _ => rfl

/-- Inversion of `RawTerm.recordIntro` partial-renaming `.isSome`.

If the composite recordIntro strengthens, the first field
strengthens. -/
theorem partialRename?_recordIntro_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (firstField : RawTerm sourceScope)
    (composite :
      ((RawTerm.recordIntro firstField).partialRename? back).isSome
        = true) :
    (firstField.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?] at composite
  match fieldBranch : firstField.partialRename? back with
  | none => rw [fieldBranch] at composite; cases composite
  | some _ => rfl

/-- Inversion of `RawTerm.recordProj` partial-renaming `.isSome`.

If the composite recordProj strengthens, the record value
strengthens. -/
theorem partialRename?_recordProj_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (recordValue : RawTerm sourceScope)
    (composite :
      ((RawTerm.recordProj recordValue).partialRename? back).isSome
        = true) :
    (recordValue.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?] at composite
  match recordBranch : recordValue.partialRename? back with
  | none => rw [recordBranch] at composite; cases composite
  | some _ => rfl

/-- Inversion of `RawTerm.codataDest` partial-renaming `.isSome`.

If the composite codataDest strengthens, the codata value
strengthens. -/
theorem partialRename?_codataDest_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (codataValue : RawTerm sourceScope)
    (composite :
      ((RawTerm.codataDest codataValue).partialRename? back).isSome
        = true) :
    (codataValue.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?] at composite
  match codataBranch : codataValue.partialRename? back with
  | none => rw [codataBranch] at composite; cases composite
  | some _ => rfl

/-- Inversion of `RawTerm.sessionRecv` partial-renaming `.isSome`.

If the composite sessionRecv strengthens, the channel strengthens. -/
theorem partialRename?_sessionRecv_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (channel : RawTerm sourceScope)
    (composite :
      ((RawTerm.sessionRecv channel).partialRename? back).isSome
        = true) :
    (channel.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?] at composite
  match channelBranch : channel.partialRename? back with
  | none => rw [channelBranch] at composite; cases composite
  | some _ => rfl

/-- Inversion of `RawTerm.listCode` partial-renaming `.isSome`.

If the composite listCode strengthens, the element-code strengthens. -/
theorem partialRename?_listCode_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (elementCode : RawTerm sourceScope)
    (composite :
      ((RawTerm.listCode elementCode).partialRename? back).isSome
        = true) :
    (elementCode.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?] at composite
  match elementBranch : elementCode.partialRename? back with
  | none => rw [elementBranch] at composite; cases composite
  | some _ => rfl

/-- Inversion of `RawTerm.optionCode` partial-renaming `.isSome`.

If the composite optionCode strengthens, the element-code strengthens. -/
theorem partialRename?_optionCode_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (elementCode : RawTerm sourceScope)
    (composite :
      ((RawTerm.optionCode elementCode).partialRename? back).isSome
        = true) :
    (elementCode.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?] at composite
  match elementBranch : elementCode.partialRename? back with
  | none => rw [elementBranch] at composite; cases composite
  | some _ => rfl

/-- Inversion of `RawTerm.cumulUpMarker` partial-renaming `.isSome`.

If the composite cumulUpMarker strengthens, the inner code
strengthens. -/
theorem partialRename?_cumulUpMarker_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (innerCodeRaw : RawTerm sourceScope)
    (composite :
      ((RawTerm.cumulUpMarker innerCodeRaw).partialRename? back).isSome
        = true) :
    (innerCodeRaw.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?] at composite
  match innerBranch : innerCodeRaw.partialRename? back with
  | none => rw [innerBranch] at composite; cases composite
  | some _ => rfl

/-- Inversion of `RawTerm.uaToEquiv` partial-renaming `.isSome`.

If the composite uaToEquiv strengthens, the proof strengthens. -/
theorem partialRename?_uaToEquiv_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (proofRaw : RawTerm sourceScope)
    (composite :
      ((RawTerm.uaToEquiv proofRaw).partialRename? back).isSome
        = true) :
    (proofRaw.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?] at composite
  match proofBranch : proofRaw.partialRename? back with
  | none => rw [proofBranch] at composite; cases composite
  | some _ => rfl

/-- Inversion of `RawTerm.idToEquiv` partial-renaming `.isSome`.

If the composite idToEquiv strengthens, the proof strengthens. -/
theorem partialRename?_idToEquiv_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (proofRaw : RawTerm sourceScope)
    (composite :
      ((RawTerm.idToEquiv proofRaw).partialRename? back).isSome
        = true) :
    (proofRaw.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?] at composite
  match proofBranch : proofRaw.partialRename? back with
  | none => rw [proofBranch] at composite; cases composite
  | some _ => rfl

/-- Inversion of `RawTerm.hcomp` partial-renaming `.isSome`. -/
theorem partialRename?_hcomp_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (sides cap : RawTerm sourceScope)
    (composite :
      ((RawTerm.hcomp sides cap).partialRename? back).isSome = true) :
    (sides.partialRename? back).isSome = true ∧
      (cap.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?, Option.mapTwo] at composite
  refine ⟨?_, ?_⟩
  · match sidesBranch : sides.partialRename? back with
    | none => rw [sidesBranch] at composite; cases composite
    | some _ => rfl
  · match capBranch : cap.partialRename? back with
    | none =>
        rw [capBranch] at composite
        match sidesBranch : sides.partialRename? back with
        | none => rw [sidesBranch] at composite; cases composite
        | some _ => rw [sidesBranch] at composite; cases composite
    | some _ => rfl

/-- Inversion of `RawTerm.oeqJ` partial-renaming `.isSome`. -/
theorem partialRename?_oeqJ_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (baseCase witness : RawTerm sourceScope)
    (composite :
      ((RawTerm.oeqJ baseCase witness).partialRename? back).isSome = true) :
    (baseCase.partialRename? back).isSome = true ∧
      (witness.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?, Option.mapTwo] at composite
  refine ⟨?_, ?_⟩
  · match baseBranch : baseCase.partialRename? back with
    | none => rw [baseBranch] at composite; cases composite
    | some _ => rfl
  · match witnessBranch : witness.partialRename? back with
    | none =>
        rw [witnessBranch] at composite
        match baseBranch : baseCase.partialRename? back with
        | none => rw [baseBranch] at composite; cases composite
        | some _ => rw [baseBranch] at composite; cases composite
    | some _ => rfl

/-- Inversion of `RawTerm.idStrictRec` partial-renaming `.isSome`. -/
theorem partialRename?_idStrictRec_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (baseCase witness : RawTerm sourceScope)
    (composite :
      ((RawTerm.idStrictRec baseCase witness).partialRename? back).isSome
        = true) :
    (baseCase.partialRename? back).isSome = true ∧
      (witness.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?, Option.mapTwo] at composite
  refine ⟨?_, ?_⟩
  · match baseBranch : baseCase.partialRename? back with
    | none => rw [baseBranch] at composite; cases composite
    | some _ => rfl
  · match witnessBranch : witness.partialRename? back with
    | none =>
        rw [witnessBranch] at composite
        match baseBranch : baseCase.partialRename? back with
        | none => rw [baseBranch] at composite; cases composite
        | some _ => rw [baseBranch] at composite; cases composite
    | some _ => rfl

/-- Inversion of `RawTerm.equivIntro` partial-renaming `.isSome`. -/
theorem partialRename?_equivIntro_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (forwardFn backwardFn : RawTerm sourceScope)
    (composite :
      ((RawTerm.equivIntro forwardFn backwardFn).partialRename? back).isSome
        = true) :
    (forwardFn.partialRename? back).isSome = true ∧
      (backwardFn.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?, Option.mapTwo] at composite
  refine ⟨?_, ?_⟩
  · match fwdBranch : forwardFn.partialRename? back with
    | none => rw [fwdBranch] at composite; cases composite
    | some _ => rfl
  · match bwdBranch : backwardFn.partialRename? back with
    | none =>
        rw [bwdBranch] at composite
        match fwdBranch : forwardFn.partialRename? back with
        | none => rw [fwdBranch] at composite; cases composite
        | some _ => rw [fwdBranch] at composite; cases composite
    | some _ => rfl

/-- Inversion of `RawTerm.equivApp` partial-renaming `.isSome`. -/
theorem partialRename?_equivApp_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (equivTerm argument : RawTerm sourceScope)
    (composite :
      ((RawTerm.equivApp equivTerm argument).partialRename? back).isSome
        = true) :
    (equivTerm.partialRename? back).isSome = true ∧
      (argument.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?, Option.mapTwo] at composite
  refine ⟨?_, ?_⟩
  · match equivBranch : equivTerm.partialRename? back with
    | none => rw [equivBranch] at composite; cases composite
    | some _ => rfl
  · match argBranch : argument.partialRename? back with
    | none =>
        rw [argBranch] at composite
        match equivBranch : equivTerm.partialRename? back with
        | none => rw [equivBranch] at composite; cases composite
        | some _ => rw [equivBranch] at composite; cases composite
    | some _ => rfl

/-- Inversion of `RawTerm.refineIntro` partial-renaming `.isSome`. -/
theorem partialRename?_refineIntro_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (rawValue predicateProof : RawTerm sourceScope)
    (composite :
      ((RawTerm.refineIntro rawValue predicateProof).partialRename?
          back).isSome = true) :
    (rawValue.partialRename? back).isSome = true ∧
      (predicateProof.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?, Option.mapTwo] at composite
  refine ⟨?_, ?_⟩
  · match valueBranch : rawValue.partialRename? back with
    | none => rw [valueBranch] at composite; cases composite
    | some _ => rfl
  · match predicateBranch : predicateProof.partialRename? back with
    | none =>
        rw [predicateBranch] at composite
        match valueBranch : rawValue.partialRename? back with
        | none => rw [valueBranch] at composite; cases composite
        | some _ => rw [valueBranch] at composite; cases composite
    | some _ => rfl

/-- Inversion of `RawTerm.codataUnfold` partial-renaming `.isSome`. -/
theorem partialRename?_codataUnfold_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (initialState transition : RawTerm sourceScope)
    (composite :
      ((RawTerm.codataUnfold initialState transition).partialRename?
          back).isSome = true) :
    (initialState.partialRename? back).isSome = true ∧
      (transition.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?, Option.mapTwo] at composite
  refine ⟨?_, ?_⟩
  · match initBranch : initialState.partialRename? back with
    | none => rw [initBranch] at composite; cases composite
    | some _ => rfl
  · match transBranch : transition.partialRename? back with
    | none =>
        rw [transBranch] at composite
        match initBranch : initialState.partialRename? back with
        | none => rw [initBranch] at composite; cases composite
        | some _ => rw [initBranch] at composite; cases composite
    | some _ => rfl

/-- Inversion of `RawTerm.sessionSend` partial-renaming `.isSome`. -/
theorem partialRename?_sessionSend_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (channel payload : RawTerm sourceScope)
    (composite :
      ((RawTerm.sessionSend channel payload).partialRename? back).isSome
        = true) :
    (channel.partialRename? back).isSome = true ∧
      (payload.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?, Option.mapTwo] at composite
  refine ⟨?_, ?_⟩
  · match channelBranch : channel.partialRename? back with
    | none => rw [channelBranch] at composite; cases composite
    | some _ => rfl
  · match payloadBranch : payload.partialRename? back with
    | none =>
        rw [payloadBranch] at composite
        match channelBranch : channel.partialRename? back with
        | none => rw [channelBranch] at composite; cases composite
        | some _ => rw [channelBranch] at composite; cases composite
    | some _ => rfl

/-- Inversion of `RawTerm.effectPerform` partial-renaming `.isSome`. -/
theorem partialRename?_effectPerform_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (operationTag arguments : RawTerm sourceScope)
    (composite :
      ((RawTerm.effectPerform operationTag arguments).partialRename?
          back).isSome = true) :
    (operationTag.partialRename? back).isSome = true ∧
      (arguments.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?, Option.mapTwo] at composite
  refine ⟨?_, ?_⟩
  · match opBranch : operationTag.partialRename? back with
    | none => rw [opBranch] at composite; cases composite
    | some _ => rfl
  · match argsBranch : arguments.partialRename? back with
    | none =>
        rw [argsBranch] at composite
        match opBranch : operationTag.partialRename? back with
        | none => rw [opBranch] at composite; cases composite
        | some _ => rw [opBranch] at composite; cases composite
    | some _ => rfl

/-- Inversion of `RawTerm.arrowCode` partial-renaming `.isSome`. -/
theorem partialRename?_arrowCode_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (domainCode codomainCode : RawTerm sourceScope)
    (composite :
      ((RawTerm.arrowCode domainCode codomainCode).partialRename?
          back).isSome = true) :
    (domainCode.partialRename? back).isSome = true ∧
      (codomainCode.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?, Option.mapTwo] at composite
  refine ⟨?_, ?_⟩
  · match domainBranch : domainCode.partialRename? back with
    | none => rw [domainBranch] at composite; cases composite
    | some _ => rfl
  · match codomainBranch : codomainCode.partialRename? back with
    | none =>
        rw [codomainBranch] at composite
        match domainBranch : domainCode.partialRename? back with
        | none => rw [domainBranch] at composite; cases composite
        | some _ => rw [domainBranch] at composite; cases composite
    | some _ => rfl

/-- Inversion of `RawTerm.productCode` partial-renaming `.isSome`. -/
theorem partialRename?_productCode_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (firstCode secondCode : RawTerm sourceScope)
    (composite :
      ((RawTerm.productCode firstCode secondCode).partialRename?
          back).isSome = true) :
    (firstCode.partialRename? back).isSome = true ∧
      (secondCode.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?, Option.mapTwo] at composite
  refine ⟨?_, ?_⟩
  · match firstBranch : firstCode.partialRename? back with
    | none => rw [firstBranch] at composite; cases composite
    | some _ => rfl
  · match secondBranch : secondCode.partialRename? back with
    | none =>
        rw [secondBranch] at composite
        match firstBranch : firstCode.partialRename? back with
        | none => rw [firstBranch] at composite; cases composite
        | some _ => rw [firstBranch] at composite; cases composite
    | some _ => rfl

/-- Inversion of `RawTerm.sumCode` partial-renaming `.isSome`. -/
theorem partialRename?_sumCode_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (leftCode rightCode : RawTerm sourceScope)
    (composite :
      ((RawTerm.sumCode leftCode rightCode).partialRename? back).isSome
        = true) :
    (leftCode.partialRename? back).isSome = true ∧
      (rightCode.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?, Option.mapTwo] at composite
  refine ⟨?_, ?_⟩
  · match leftBranch : leftCode.partialRename? back with
    | none => rw [leftBranch] at composite; cases composite
    | some _ => rfl
  · match rightBranch : rightCode.partialRename? back with
    | none =>
        rw [rightBranch] at composite
        match leftBranch : leftCode.partialRename? back with
        | none => rw [leftBranch] at composite; cases composite
        | some _ => rw [leftBranch] at composite; cases composite
    | some _ => rfl

/-- Inversion of `RawTerm.eitherCode` partial-renaming `.isSome`. -/
theorem partialRename?_eitherCode_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (leftCode rightCode : RawTerm sourceScope)
    (composite :
      ((RawTerm.eitherCode leftCode rightCode).partialRename? back).isSome
        = true) :
    (leftCode.partialRename? back).isSome = true ∧
      (rightCode.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?, Option.mapTwo] at composite
  refine ⟨?_, ?_⟩
  · match leftBranch : leftCode.partialRename? back with
    | none => rw [leftBranch] at composite; cases composite
    | some _ => rfl
  · match rightBranch : rightCode.partialRename? back with
    | none =>
        rw [rightBranch] at composite
        match leftBranch : leftCode.partialRename? back with
        | none => rw [leftBranch] at composite; cases composite
        | some _ => rw [leftBranch] at composite; cases composite
    | some _ => rfl

/-- Inversion of `RawTerm.equivCode` partial-renaming `.isSome`. -/
theorem partialRename?_equivCode_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (leftTypeCode rightTypeCode : RawTerm sourceScope)
    (composite :
      ((RawTerm.equivCode leftTypeCode rightTypeCode).partialRename?
          back).isSome = true) :
    (leftTypeCode.partialRename? back).isSome = true ∧
      (rightTypeCode.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?, Option.mapTwo] at composite
  refine ⟨?_, ?_⟩
  · match leftBranch : leftTypeCode.partialRename? back with
    | none => rw [leftBranch] at composite; cases composite
    | some _ => rfl
  · match rightBranch : rightTypeCode.partialRename? back with
    | none =>
        rw [rightBranch] at composite
        match leftBranch : leftTypeCode.partialRename? back with
        | none => rw [leftBranch] at composite; cases composite
        | some _ => rw [leftBranch] at composite; cases composite
    | some _ => rfl

/-- Inversion of `RawTerm.equivApply` partial-renaming `.isSome`. -/
theorem partialRename?_equivApply_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (equivRaw argRaw : RawTerm sourceScope)
    (composite :
      ((RawTerm.equivApply equivRaw argRaw).partialRename? back).isSome
        = true) :
    (equivRaw.partialRename? back).isSome = true ∧
      (argRaw.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?, Option.mapTwo] at composite
  refine ⟨?_, ?_⟩
  · match equivBranch : equivRaw.partialRename? back with
    | none => rw [equivBranch] at composite; cases composite
    | some _ => rfl
  · match argBranch : argRaw.partialRename? back with
    | none =>
        rw [argBranch] at composite
        match equivBranch : equivRaw.partialRename? back with
        | none => rw [equivBranch] at composite; cases composite
        | some _ => rw [equivBranch] at composite; cases composite
    | some _ => rfl

/-- Inversion of `RawTerm.pathCompose` partial-renaming `.isSome`. -/
theorem partialRename?_pathCompose_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (leftPathRaw rightPathRaw : RawTerm sourceScope)
    (composite :
      ((RawTerm.pathCompose leftPathRaw rightPathRaw).partialRename?
          back).isSome = true) :
    (leftPathRaw.partialRename? back).isSome = true ∧
      (rightPathRaw.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?, Option.mapTwo] at composite
  refine ⟨?_, ?_⟩
  · match leftBranch : leftPathRaw.partialRename? back with
    | none => rw [leftBranch] at composite; cases composite
    | some _ => rfl
  · match rightBranch : rightPathRaw.partialRename? back with
    | none =>
        rw [rightBranch] at composite
        match leftBranch : leftPathRaw.partialRename? back with
        | none => rw [leftBranch] at composite; cases composite
        | some _ => rw [leftBranch] at composite; cases composite
    | some _ => rfl

/-- Inversion of `RawTerm.oeqTrans` partial-renaming `.isSome`. -/
theorem partialRename?_oeqTrans_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (firstProof secondProof : RawTerm sourceScope)
    (composite :
      ((RawTerm.oeqTrans firstProof secondProof).partialRename?
          back).isSome = true) :
    (firstProof.partialRename? back).isSome = true ∧
      (secondProof.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?, Option.mapTwo] at composite
  refine ⟨?_, ?_⟩
  · match firstBranch : firstProof.partialRename? back with
    | none => rw [firstBranch] at composite; cases composite
    | some _ => rfl
  · match secondBranch : secondProof.partialRename? back with
    | none =>
        rw [secondBranch] at composite
        match firstBranch : firstProof.partialRename? back with
        | none => rw [firstBranch] at composite; cases composite
        | some _ => rw [firstBranch] at composite; cases composite
    | some _ => rfl

/-- Inversion of `RawTerm.equivCompose` partial-renaming `.isSome`. -/
theorem partialRename?_equivCompose_isSome
    (back : PartialRawRenaming sourceScope targetScope)
    (firstEquiv secondEquiv : RawTerm sourceScope)
    (composite :
      ((RawTerm.equivCompose firstEquiv secondEquiv).partialRename?
          back).isSome = true) :
    (firstEquiv.partialRename? back).isSome = true ∧
      (secondEquiv.partialRename? back).isSome = true := by
  dsimp only [RawTerm.partialRename?, Option.mapTwo] at composite
  refine ⟨?_, ?_⟩
  · match firstBranch : firstEquiv.partialRename? back with
    | none => rw [firstBranch] at composite; cases composite
    | some _ => rfl
  · match secondBranch : secondEquiv.partialRename? back with
    | none =>
        rw [secondBranch] at composite
        match firstBranch : firstEquiv.partialRename? back with
        | none => rw [firstBranch] at composite; cases composite
        | some _ => rw [firstBranch] at composite; cases composite
    | some _ => rfl

end RawTerm

end LeanFX2
