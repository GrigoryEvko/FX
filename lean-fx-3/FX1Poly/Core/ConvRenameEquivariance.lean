import FX1Poly.Core.RawTermRenameInjective
import FX1Poly.Core.ConvSubstRename
import FX1Poly.Core.ExistsStepOfNotNormal

/-! # FX1Poly/Core/ConvRenameEquivariance — the Conv/NF renaming-equivariance bundle

The grown-strengthening campaign (route H) consumed renaming PRESERVATION (`Conv.rename`, #370) and
renaming REFLECTION (`Conv.reflectRename` + the injective instances, #1167 / `RawTermRenameInjective`)
as separate halves.  This file assembles them into the two-sided EQUIVARIANCE statements the
whnf-directed checker compares classifiers with — `Conv` and structural normality are both invariant
under injective renaming, as IFFS:

  * `Conv.rename_iff_ofFinInjective` — ★ `Conv (rename ρ a) (rename ρ b) ↔ Conv a b` for any
    Fin-injective `ρ` (forward = `Conv.rename`, backward = `Conv.reflectRenameOfFinInjective`).
  * `Conv.renameWeaken_iff` — the `weaken` instance (injectivity via `RawTerm.weaken_injective`).
  * `Conv.renameLift_iff` — the binder instance at `RawRenaming.lift ρ` (injectivity via
    `RawRenaming.lift_injective` — the binder-descent form the pinned reflection's arms use).
  * `RawTerm.isStepNormalForm_rename_iff` — structural normality is invariant under EVERY renaming
    (no injectivity needed): forward strips the renaming via `Step.reflectRename`, backward pushes a
    source step through `Step.rename`.  This is the normalize/whnf-rename commutation fact in its
    `Step`-reflection form: the checker may normalize before or after renaming and reach normal
    forms in the same positions (`StepStar.rename` / `StepStar.reflectRename` carry the chains).

## Zero-axiom verification

Each iff is a pairing of the two shipped halves; the normality iff is a `Bool`-valued case split
(no excluded middle) feeding `exists_step_of_not_isStepNormalForm` against
`isStepNormalForm_blocks_step` through `Step.rename` / `Step.reflectRename`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation

/-- **★ `Conv` is equivariant under Fin-injective renaming** — the two shipped halves as one iff:
forward is preservation (`Conv.rename`), backward is reflection
(`Conv.reflectRenameOfFinInjective`). -/
theorem Conv.rename_iff_ofFinInjective {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope) (rhoInjective : Function.Injective rho)
    {leftTerm rightTerm : RawTerm sourceScope} :
    Conv (RawTerm.rename rho leftTerm) (RawTerm.rename rho rightTerm) ↔
      Conv leftTerm rightTerm :=
  ⟨Conv.reflectRenameOfFinInjective rho rhoInjective, Conv.rename rho⟩

/-- **The `weaken` instance**: convertibility under one binder weakening is exactly convertibility
at the source scope. -/
theorem Conv.renameWeaken_iff {scope : Nat} {leftTerm rightTerm : RawTerm scope} :
    Conv (RawTerm.weaken leftTerm) (RawTerm.weaken rightTerm) ↔ Conv leftTerm rightTerm :=
  ⟨Conv.reflectWeaken, Conv.rename RawRenaming.weaken⟩

/-- **The binder-descent instance**: convertibility under `RawRenaming.lift ρ` for Fin-injective
`ρ` is exactly convertibility at the source scope — the form the pinned reflection's binder arms
consume. -/
theorem Conv.renameLift_iff {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope) (rhoInjective : Function.Injective rho)
    {leftTerm rightTerm : RawTerm (sourceScope + 1)} :
    Conv (RawTerm.rename (RawRenaming.lift rho) leftTerm)
        (RawTerm.rename (RawRenaming.lift rho) rightTerm) ↔
      Conv leftTerm rightTerm :=
  ⟨Conv.reflectLiftRename rho rhoInjective, Conv.rename (RawRenaming.lift rho)⟩

/-- **Structural normality is invariant under EVERY renaming** (no injectivity needed): a step of
the source pushes through `Step.rename`, a step of the image pulls back through
`Step.reflectRename`.  The normalize-before-or-after-renaming commutation fact at the checker's
classifier-comparison points. -/
theorem RawTerm.isStepNormalForm_rename_iff {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope) (term : RawTerm sourceScope) :
    RawTerm.isStepNormalForm (RawTerm.rename rho term) ↔ RawTerm.isStepNormalForm term := by
  constructor
  · intro renamedNormal
    cases sourceNormalValue : RawTerm.isStepNormalFormBool term with
    | true => exact sourceNormalValue
    | false =>
        obtain ⟨sourceReduct, sourceStep⟩ :=
          exists_step_of_not_isStepNormalForm
            (fun normalProof => Bool.noConfusion (sourceNormalValue.symm.trans normalProof))
        exact absurd (Step.rename rho sourceStep)
          (RawTerm.isStepNormalForm_blocks_step renamedNormal _)
  · intro sourceNormal
    cases renamedNormalValue : RawTerm.isStepNormalFormBool (RawTerm.rename rho term) with
    | true => exact renamedNormalValue
    | false =>
        obtain ⟨renamedReduct, renamedStep⟩ :=
          exists_step_of_not_isStepNormalForm
            (fun normalProof => Bool.noConfusion (renamedNormalValue.symm.trans normalProof))
        obtain ⟨sourceReduct, sourceStep, _renameEq⟩ := Step.reflectRename rho renamedStep
        exact absurd sourceStep (RawTerm.isStepNormalForm_blocks_step sourceNormal _)

end FX1Poly.Core
