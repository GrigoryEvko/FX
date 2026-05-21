import LeanFX2.Reduction.RawParWeakenInv.Foundation
import LeanFX2.Reduction.RawParWeakenInv.HeadlineRenameInjInv

/-! # Reduction/RawParWeakenInv/Weaken — specialization to canonical weaken

The user-facing `RawStep.par.weaken_inv`: if `RawStep.par
sourceTerm.weaken targetAfter`, then `targetAfter = targetInner.weaken`
for some `targetInner`.  A direct specialization of
`rename_inj_inv` via `RawRenaming.weaken_injective`.

## Root status

Kernel `theorem` with body, zero-axiom. -/

namespace LeanFX2

/-- Specialization to the canonical weaken renaming. -/
theorem RawStep.par.weaken_inv {scope : Nat}
    {sourceTerm : RawTerm scope}
    {targetAfter : RawTerm (scope + 1)}
    (parStep : RawStep.par sourceTerm.weaken targetAfter) :
    ∃ targetInner : RawTerm scope, targetAfter = targetInner.weaken :=
  RawStep.par.rename_inj_inv sourceTerm RawRenaming.weaken
    RawRenaming.weaken_injective parStep

/-- Source-equality wrapper for the canonical one-step weaken inversion. -/
theorem RawStep.par.weaken_inv_of_source_eq {scope : Nat}
    {weakenedSource targetAfter : RawTerm (scope + 1)}
    {sourceTerm : RawTerm scope}
    (sourceEq : weakenedSource = sourceTerm.weaken)
    (parStep : RawStep.par weakenedSource targetAfter) :
    ∃ targetInner : RawTerm scope, targetAfter = targetInner.weaken := by
  cases sourceEq
  exact RawStep.par.weaken_inv parStep

/-- Canonical-weaken instance of `target_in_rename_image`. -/
theorem RawStep.par.target_in_weaken_image {scope : Nat}
    {sourceTerm : RawTerm scope}
    {targetAfter : RawTerm (scope + 1)}
    (parStep : RawStep.par sourceTerm.weaken targetAfter) :
    ∃ targetInner : RawTerm scope, targetAfter = targetInner.weaken :=
  RawStep.par.target_in_rename_image RawRenaming.weaken
    RawRenaming.weaken_injective parStep

/-- Source-equality wrapper for canonical-weaken one-step target image. -/
theorem RawStep.par.target_in_weaken_image_of_source_eq {scope : Nat}
    {weakenedSource targetAfter : RawTerm (scope + 1)}
    {sourceTerm : RawTerm scope}
    (sourceEq : weakenedSource = sourceTerm.weaken)
    (parStep : RawStep.par weakenedSource targetAfter) :
    ∃ targetInner : RawTerm scope, targetAfter = targetInner.weaken := by
  cases sourceEq
  exact RawStep.par.target_in_weaken_image parStep


end LeanFX2
