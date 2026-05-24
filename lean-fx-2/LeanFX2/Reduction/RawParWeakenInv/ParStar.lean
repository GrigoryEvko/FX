import LeanFX2.Confluence.RawDiamond
import LeanFX2.Reduction.RawParCompatible.NamedCompatibility

/-! # ParStar — TODO POLYCELL: BODY DISABLED

Body depends on cd_lemma / Conv.canonical_form / parStar.confluence /
RawStep.parStar orchestration deleted in commit c2efaccf (cascade-fake
bulldoze).  Replacement: FXcdLemma / FXConv view defs per polycell.md §5.
Imports are preserved at top so downstream transitive imports still work.
-/

/- TODO POLYCELL: original body preserved as block comment


/-! # Reduction/RawParWeakenInv/ParStar

Multi-step raw rename-image preservation for `RawStep.parStar`.

The one-step theorem `RawStep.par.target_in_rename_image` only proves image
membership for the target of a single parallel-reduction step.  This file lifts
that result through the reflexive-transitive closure by raw induction over the
`parStar` chain.
-/

namespace LeanFX2

/-- Raw `parStar` is compatible with renaming.

Forward equivariance is a direct lift of one-step
`RawStep.par.rename_compatible` through the reflexive-transitive closure. -/
theorem RawStep.parStar.rename_compatible
    {sourceScope targetScope : Nat}
    (rawRenaming : RawRenaming sourceScope targetScope)
    {beforeTerm afterTerm : RawTerm sourceScope}
    (parallelChain : RawStep.parStar beforeTerm afterTerm) :
    RawStep.parStar (beforeTerm.rename rawRenaming)
      (afterTerm.rename rawRenaming) := by
  induction parallelChain with
  | refl term =>
      exact RawStep.parStar.refl (term.rename rawRenaming)
  | trans firstStep _ restIH =>
      exact RawStep.parStar.trans
        (RawStep.par.rename_compatible rawRenaming firstStep)
        restIH

/-- Canonical-weaken specialization of `rename_compatible` for raw
multi-step parallel chains.  Surface form `beforeTerm.weaken` /
`afterTerm.weaken` matches the shape Phase G β-η critical pair and
K13 NbE β step consumers reach for at call sites. -/
theorem RawStep.parStar.weaken_compatible
    {scope : Nat}
    {beforeTerm afterTerm : RawTerm scope}
    (parallelChain : RawStep.parStar beforeTerm afterTerm) :
    RawStep.parStar beforeTerm.weaken afterTerm.weaken :=
  RawStep.parStar.rename_compatible RawRenaming.weaken parallelChain

/-- Multi-step lift of `RawStep.par.subst_compatible_same`.

Raw multi-step parallel reduction is preserved by applying the same
substitution to both sides of the chain.  Proved via `mapStep` lift
through the single-step compatibility theorem, per the
`feedback_lean_mapStep_pattern.md` discipline. -/
theorem RawStep.parStar.subst_compatible_same
    {sourceScope targetScope : Nat}
    (rawSubst : RawTermSubst sourceScope targetScope)
    {beforeTerm afterTerm : RawTerm sourceScope}
    (parallelChain : RawStep.parStar beforeTerm afterTerm) :
    RawStep.parStar (beforeTerm.subst rawSubst)
                    (afterTerm.subst rawSubst) :=
  RawStep.parStar.mapStep
    (fun term => term.subst rawSubst)
    (fun step => RawStep.par.subst_compatible_same rawSubst step)
    parallelChain

/-- Singleton-substitution specialization of
`RawStep.parStar.subst_compatible_same`.

Surface form `body.subst0 arg` matches the β-redex shape downstream
K12.28 Geuvers 1992 critical-pair joinability and K13 NbE β-step
consumers reach for at the raw multi-step level.  Specializes the
general subst compatibility theorem to `RawTermSubst.singleton`. -/
theorem RawStep.parStar.subst0_compatible_same
    {scope : Nat}
    (argTerm : RawTerm scope)
    {beforeBody afterBody : RawTerm (scope + 1)}
    (parallelChain : RawStep.parStar beforeBody afterBody) :
    RawStep.parStar (beforeBody.subst0 argTerm)
                    (afterBody.subst0 argTerm) :=
  RawStep.parStar.subst_compatible_same
    (RawTermSubst.singleton argTerm) parallelChain

/-- Heterogeneous multi-step singleton-substitution lift of
`RawStep.par.subst0_par`.

Given a body-chain `body1 ~~> body2` AND an arg-chain `arg1 ~~> arg2`
(both at the raw multi-step parallel level), the β-redex chain
`(body1.subst0 arg1) ~~> (body2.subst0 arg2)` follows by chaining the
two homogeneous lifts and composing via `RawStep.parStar.append`:
* lift body-chain at fixed `arg1`: `body1.subst0 arg1 ~~> body2.subst0 arg1`
* lift arg-chain at fixed `body2` via `mapStep` + `RawStep.par.subst0_par`
  with reflexive body step: `body2.subst0 arg1 ~~> body2.subst0 arg2`

This is the multi-step heterogeneous form of `RawStep.par.subst0_par`.
β-step bisimulations and Geuvers 1992 β-η critical-pair joinability
reach for this exact shape: both sides of a redex evolve through their
own parallel chain. -/
theorem RawStep.parStar.subst0_par {scope : Nat}
    {bodySource bodyTarget : RawTerm (scope + 1)}
    {argSource argTarget : RawTerm scope}
    (bodyChain : RawStep.parStar bodySource bodyTarget)
    (argChain : RawStep.parStar argSource argTarget) :
    RawStep.parStar (bodySource.subst0 argSource)
                    (bodyTarget.subst0 argTarget) :=
  let leftHalf :
      RawStep.parStar (bodySource.subst0 argSource)
                      (bodyTarget.subst0 argSource) :=
    RawStep.parStar.subst0_compatible_same argSource bodyChain
  let rightHalf :
      RawStep.parStar (bodyTarget.subst0 argSource)
                      (bodyTarget.subst0 argTarget) :=
    RawStep.parStar.mapStep
      (fun freshArg => bodyTarget.subst0 freshArg)
      (fun argStep =>
        RawStep.par.subst0_par (RawStep.par.refl bodyTarget) argStep)
      argChain
  RawStep.parStar.append leftHalf rightHalf

/-- Multi-position parallel-substitution lift for raw multi-step chains.

Generalizes `RawStep.parStar.subst0_par` from singleton β to arbitrary
substitutions: given

* a body-chain `bodySource ⟶* bodyTarget` (any length), and
* a single-step pointwise relation `firstSubst position ⟶ secondSubst
  position` for every position,

produce a chain `bodySource.subst firstSubst ⟶* bodyTarget.subst
secondSubst`.  The body's multi-step chain decouples from the
single-step nature of the per-position substitution update.

Proof composes via `RawStep.parStar.append`:
* lift body-chain at fixed `firstSubst` via `subst_compatible_same`
  (`bodySource.subst firstSubst ⟶* bodyTarget.subst firstSubst`).
* lift pointwise-related substs at fixed `bodyTarget` via the
  single-step `RawStep.par.subst_par` with reflexive body step,
  injected into `parStar` via `RawStep.par.toStar`.

K12.28 Geuvers β-η critical pair joinability and K13 NbE β-step
substitution-evolution consumers reach for this shape when a typed
substitution chain (e.g. through a parametric subst lift) needs to
fuse with a body chain. -/
theorem RawStep.parStar.subst_par {sourceScope targetScope : Nat}
    {firstSubst secondSubst : RawTermSubst sourceScope targetScope}
    (substsRelated : ∀ position,
      RawStep.par (firstSubst position) (secondSubst position))
    {bodySource bodyTarget : RawTerm sourceScope}
    (bodyChain : RawStep.parStar bodySource bodyTarget) :
    RawStep.parStar (bodySource.subst firstSubst)
                    (bodyTarget.subst secondSubst) :=
  let leftHalf :
      RawStep.parStar (bodySource.subst firstSubst)
                      (bodyTarget.subst firstSubst) :=
    RawStep.parStar.subst_compatible_same firstSubst bodyChain
  let rightHalfStep :
      RawStep.par (bodyTarget.subst firstSubst)
                  (bodyTarget.subst secondSubst) :=
    RawStep.par.subst_par substsRelated (RawStep.par.refl bodyTarget)
  let rightHalf :
      RawStep.parStar (bodyTarget.subst firstSubst)
                      (bodyTarget.subst secondSubst) :=
    RawStep.par.toStar rightHalfStep
  RawStep.parStar.append leftHalf rightHalf

private theorem RawStep.parStar.target_in_rename_image_aux
    {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (rhoInjective :
      ∀ leftPosition rightPosition,
        rho leftPosition = rho rightPosition → leftPosition = rightPosition)
    {source target : RawTerm targetScope}
    (parallelChain : RawStep.parStar source target) :
    ∀ {sourceTerm : RawTerm sourceScope},
      source = sourceTerm.rename rho →
      ∃ targetInner : RawTerm sourceScope,
        target = targetInner.rename rho := by
  induction parallelChain with
  | refl _ =>
      intro sourceTerm sourceEq
      exact ⟨sourceTerm, sourceEq⟩
  | trans firstStep _ restIH =>
      intro sourceTerm sourceEq
      cases sourceEq
      obtain ⟨middleInner, middleEq⟩ :=
        RawStep.par.target_in_rename_image rho rhoInjective firstStep
      exact restIH middleEq

/-- If a raw `parStar` chain starts from a term in the image of an injective
renaming, then its final target is also in that image.

This remains the target-image half of roadmap T5.  It does not reconstruct the
inner source-scope `RawStep.parStar` chain. -/
theorem RawStep.parStar.target_in_rename_image
    {sourceScope targetScope : Nat}
    (rho : RawRenaming sourceScope targetScope)
    (rhoInjective :
      ∀ leftPosition rightPosition,
        rho leftPosition = rho rightPosition → leftPosition = rightPosition)
    {sourceTerm : RawTerm sourceScope}
    {targetAfter : RawTerm targetScope}
    (parallelChain : RawStep.parStar (sourceTerm.rename rho) targetAfter) :
    ∃ targetInner : RawTerm sourceScope,
      targetAfter = targetInner.rename rho :=
  RawStep.parStar.target_in_rename_image_aux rho rhoInjective
    parallelChain rfl

/-- Source-equality wrapper for `RawStep.parStar.target_in_rename_image`.

This is the multi-step roadmap shape: the chain source is identified as a
rename image by an equality hypothesis instead of being definitionally a
renamed term. -/
theorem RawStep.parStar.target_in_rename_image_of_source_eq
    {sourceScope targetScope : Nat}
    {renamedSource targetAfter : RawTerm targetScope}
    {sourceTerm : RawTerm sourceScope}
    (rho : RawRenaming sourceScope targetScope)
    (rhoInjective :
      ∀ leftPosition rightPosition,
        rho leftPosition = rho rightPosition → leftPosition = rightPosition)
    (sourceEq : renamedSource = sourceTerm.rename rho)
    (parallelChain : RawStep.parStar renamedSource targetAfter) :
    ∃ targetInner : RawTerm sourceScope,
      targetAfter = targetInner.rename rho := by
  cases sourceEq
  exact RawStep.parStar.target_in_rename_image rho rhoInjective parallelChain

/-- Canonical-weaken instance of `RawStep.parStar.target_in_rename_image`. -/
theorem RawStep.parStar.target_in_weaken_image
    {scope : Nat}
    {sourceTerm : RawTerm scope}
    {targetAfter : RawTerm (scope + 1)}
    (parallelChain : RawStep.parStar sourceTerm.weaken targetAfter) :
    ∃ targetInner : RawTerm scope,
      targetAfter = targetInner.weaken :=
  RawStep.parStar.target_in_rename_image RawRenaming.weaken
    RawRenaming.weaken_injective parallelChain

/-- Historical canonical-weaken spelling for the multi-step target-image
inversion.  This remains target-image only; it does not reconstruct an inner
source-scope `parStar` chain. -/
theorem RawStep.parStar.weaken_inv
    {scope : Nat}
    {sourceTerm : RawTerm scope}
    {targetAfter : RawTerm (scope + 1)}
    (parallelChain : RawStep.parStar sourceTerm.weaken targetAfter) :
    ∃ targetInner : RawTerm scope,
      targetAfter = targetInner.weaken :=
  RawStep.parStar.target_in_weaken_image parallelChain

/-- Source-equality wrapper for the canonical-weaken `parStar` target image. -/
theorem RawStep.parStar.target_in_weaken_image_of_source_eq
    {scope : Nat}
    {weakenedSource targetAfter : RawTerm (scope + 1)}
    {sourceTerm : RawTerm scope}
    (sourceEq : weakenedSource = sourceTerm.weaken)
    (parallelChain : RawStep.parStar weakenedSource targetAfter) :
    ∃ targetInner : RawTerm scope,
      targetAfter = targetInner.weaken := by
  cases sourceEq
  exact RawStep.parStar.target_in_weaken_image parallelChain

/-- Source-equality wrapper for `RawStep.parStar.weaken_inv`. -/
theorem RawStep.parStar.weaken_inv_of_source_eq
    {scope : Nat}
    {weakenedSource targetAfter : RawTerm (scope + 1)}
    {sourceTerm : RawTerm scope}
    (sourceEq : weakenedSource = sourceTerm.weaken)
    (parallelChain : RawStep.parStar weakenedSource targetAfter) :
    ∃ targetInner : RawTerm scope,
      targetAfter = targetInner.weaken := by
  cases sourceEq
  exact RawStep.parStar.weaken_inv parallelChain

end LeanFX2

-/
