import FX1Poly.Core.StepRenameReflectAssembly
import FX1Poly.Core.StepStarConfluence

/-! # FX1Poly/Core/StrongNormalizationRenameForwardGeneral
    — forward SN under ANY renaming, via arbitrary-renaming Step reflection

`isStronglyNormalizing_rename_of_leftInverse` transfers SN forward only
when a TOTAL left inverse exists — which fails for `RawRenaming.weaken`
at `scope = 0` (`Fin 1 → Fin 0` has no inhabitant), even though the
left-inverse property would be vacuous there.

The general forward direction needs neither injectivity nor an inverse:
`Step.reflectRename` pulls every step of `rename rho t` back to a source
step with a renamed reduct, so the source's accessibility transfers
forward directly.  In particular weakening preserves SN at EVERY scope,
including the closed scope.

## Zero-axiom verification

`Acc` induction + `Step.reflectRename` + `▸`.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- **Forward strong normalization under any renaming.**  Every step of
the renamed term reflects to a source step (`Step.reflectRename`, no
injectivity needed), so the source's accessibility transfers forward. -/
theorem isStronglyNormalizing_rename_forward {sourceScope targetScope : Nat}
    (forwardRenaming : RawRenaming sourceScope targetScope)
    {sourceTerm : RawTerm sourceScope}
    (sourceTerminates : IsStronglyNormalizing sourceTerm) :
    IsStronglyNormalizing (RawTerm.rename forwardRenaming sourceTerm) := by
  induction sourceTerminates with
  | intro currentSource _ inductiveHypothesis =>
      refine Acc.intro _ (fun renamedReduct renamedStep => ?_)
      obtain ⟨sourceReduct, sourceStep, renameEquation⟩ :=
        Step.reflectRename forwardRenaming renamedStep
      exact renameEquation ▸ inductiveHypothesis sourceReduct sourceStep

/-- **Weakening preserves strong normalization at every scope** — the
scope-0-safe forward form (no left inverse exists for `weaken` at the
closed scope, so this MUST route through reflection, not inversion). -/
theorem weaken_isStronglyNormalizing_forward {scope : Nat}
    {sourceTerm : RawTerm scope}
    (sourceTerminates : IsStronglyNormalizing sourceTerm) :
    IsStronglyNormalizing (RawTerm.weaken sourceTerm) := by
  rw [RawTerm.weaken_eq_rename]
  exact isStronglyNormalizing_rename_forward RawRenaming.weaken
    sourceTerminates

end FX1Poly.Core
