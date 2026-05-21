import LeanFX2.Confluence.RawDiamond
import LeanFX2.Reduction.RawParCompatible.NamedCompatibility

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

end LeanFX2
