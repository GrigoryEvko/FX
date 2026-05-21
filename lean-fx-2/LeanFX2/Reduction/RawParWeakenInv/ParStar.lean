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
