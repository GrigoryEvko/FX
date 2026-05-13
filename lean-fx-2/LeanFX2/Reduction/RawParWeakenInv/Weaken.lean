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


end LeanFX2
