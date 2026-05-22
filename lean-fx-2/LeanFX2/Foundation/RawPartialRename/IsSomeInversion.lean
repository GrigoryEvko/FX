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

end RawTerm

end LeanFX2
