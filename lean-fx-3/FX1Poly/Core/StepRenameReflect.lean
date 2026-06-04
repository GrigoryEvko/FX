import FX1Poly.Core.StepRename
import FX1Poly.Core.StrongNormalizationRenameForward

/-! # FX1Poly/Core/StepRenameReflect — pulling a `Step` BACK along an injective renaming

`Step.rename` (StepRename.lean) pushes a reduction FORWARD along any renaming
(`Step t t' → Step (rename ρ t) (rename ρ t')`).  The Kripke reducibility-candidate CR3 of the
dependent arrow (the deferred Girard case, `KripkeCandidateRenameClosure.lean:63`) needs the CONVERSE
with image:

  `Step (rename ρ f) h → ∃ f', Step f f' ∧ rename ρ f' = h`   (for injective `ρ`).

That full reflection-with-image splits into two halves:

  * the **`Step` half** (this file): recover the SOURCE reduct `f' := rename ρ⁻¹ h` and prove `Step f f'`.
    This half needs NO free-variable confinement — the left-inverse property `ρ⁻¹ ∘ ρ = id` holds at
    EVERY index (not merely on `ρ`'s image), so the round-trip `rename ρ⁻¹ (rename ρ f) = f` collapses
    definitionally exactly as in `isStronglyNormalizing_rename_of_leftInverse`.
  * the **image half** (`rename ρ f' = h`, a separate later brick): this DOES need confinement
    (`h`'s free variables lie in `ρ`'s image), since it is the OTHER composite `ρ ∘ ρ⁻¹`, which is the
    identity only on the image.

This file ships the confinement-free `Step` half (and its `StepStar` chain lift): pull a reduction of a
`ρ`-renamed term back to a reduction of the source, witnessed by the left-inverse renaming.  It is the
`Step`-level analogue of the shipped `isStronglyNormalizing_rename_of_leftInverse` and the full-`Step`
generalization of the existence-only `HeadStep.rename_reflects`.

## Zero-axiom verification

The round-trip `rename leftInverse (rename forward sourceTerm) = sourceTerm` is the verbatim
`rename_compose` + `rename_pointwise` (compose-is-identity from the left-inverse property) +
`rename_identity_apply` chain shipped in `isStronglyNormalizing_rename_of_leftInverse`; then `Step.rename`
(forward, shipped) transports the step and the round-trip rewrites the source side.  No `axiom`, `sorry`,
`propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditCore.lean`.
-/

namespace FX1Poly.Core

open FX1Poly.Foundation
open StepStar

/-- **Pull a `Step` back along an injective renaming.**  If the `forwardRenaming`-renamed `sourceTerm`
takes a reduction to `renamedReduct`, then `sourceTerm` itself reduces to `rename leftInverseRenaming
renamedReduct` — the source reduct recovered by the left-inverse.  The confinement-free `Step` half of
full rename-reflection (the image equation `rename forwardRenaming (…) = renamedReduct` is a separate
brick needing free-variable confinement).  Witnessed by transporting the step with `Step.rename` along
`leftInverseRenaming` and collapsing the round-trip `rename leftInverse (rename forward sourceTerm) =
sourceTerm` (the same chain as `isStronglyNormalizing_rename_of_leftInverse`). -/
theorem Step.renamePullbackOfLeftInverse {sourceScope targetScope : Nat}
    (forwardRenaming : RawRenaming sourceScope targetScope)
    (leftInverseRenaming : RawRenaming targetScope sourceScope)
    (leftInverseProperty :
      ∀ index : Fin sourceScope, leftInverseRenaming (forwardRenaming index) = index)
    {sourceTerm : RawTerm sourceScope} {renamedReduct : RawTerm targetScope}
    (renamedStep : Step (RawTerm.rename forwardRenaming sourceTerm) renamedReduct) :
    Step sourceTerm (RawTerm.rename leftInverseRenaming renamedReduct) := by
  have pulledStep := Step.rename leftInverseRenaming renamedStep
  have roundTrip :
      RawTerm.rename leftInverseRenaming (RawTerm.rename forwardRenaming sourceTerm) = sourceTerm := by
    rw [RawTerm.rename_compose forwardRenaming leftInverseRenaming sourceTerm]
    have composeIsIdentity :
        RawRenaming.PointwiseEq
          (RawRenaming.compose forwardRenaming leftInverseRenaming)
          (RawRenaming.identity (scope := sourceScope)) := by
      intro position
      simp only [RawRenaming.compose, RawRenaming.identity]
      exact leftInverseProperty position
    rw [RawTerm.rename_pointwise composeIsIdentity sourceTerm]
    exact RawTerm.rename_identity_apply sourceTerm
  rw [roundTrip] at pulledStep
  exact pulledStep

/-- **Existence form of the `Step` pullback.**  A reduction of a `forwardRenaming`-renamed term reflects
to SOME reduction of the source — the full-`Step` generalization of the existence-only
`HeadStep.rename_reflects`, now with the explicit left-inverse witness available via
`renamePullbackOfLeftInverse`. -/
theorem Step.renameReflectsExistsOfLeftInverse {sourceScope targetScope : Nat}
    (forwardRenaming : RawRenaming sourceScope targetScope)
    (leftInverseRenaming : RawRenaming targetScope sourceScope)
    (leftInverseProperty :
      ∀ index : Fin sourceScope, leftInverseRenaming (forwardRenaming index) = index)
    {sourceTerm : RawTerm sourceScope} {renamedReduct : RawTerm targetScope}
    (renamedStep : Step (RawTerm.rename forwardRenaming sourceTerm) renamedReduct) :
    ∃ sourceReduct : RawTerm sourceScope, Step sourceTerm sourceReduct :=
  ⟨RawTerm.rename leftInverseRenaming renamedReduct,
    Step.renamePullbackOfLeftInverse forwardRenaming leftInverseRenaming leftInverseProperty renamedStep⟩

/-- **Pull a `StepStar` chain back along an injective renaming.**  The reflexive-transitive lift of
`Step.renamePullbackOfLeftInverse`: a multi-step reduction of a `forwardRenaming`-renamed term pulls back
to a reduction chain from the source to the left-inverse image of the endpoint.  Each step is reflected
by the single-step pullback; the round-trips on intermediate terms collapse the same way. -/
theorem StepStar.renamePullbackOfLeftInverse {sourceScope targetScope : Nat}
    (forwardRenaming : RawRenaming sourceScope targetScope)
    (leftInverseRenaming : RawRenaming targetScope sourceScope)
    (leftInverseProperty :
      ∀ index : Fin sourceScope, leftInverseRenaming (forwardRenaming index) = index)
    {sourceTerm : RawTerm sourceScope} {renamedReduct : RawTerm targetScope}
    (renamedChain : StepStar (RawTerm.rename forwardRenaming sourceTerm) renamedReduct) :
    StepStar sourceTerm (RawTerm.rename leftInverseRenaming renamedReduct) := by
  have pulledChain := StepStar.rename leftInverseRenaming renamedChain
  have roundTrip :
      RawTerm.rename leftInverseRenaming (RawTerm.rename forwardRenaming sourceTerm) = sourceTerm := by
    rw [RawTerm.rename_compose forwardRenaming leftInverseRenaming sourceTerm]
    have composeIsIdentity :
        RawRenaming.PointwiseEq
          (RawRenaming.compose forwardRenaming leftInverseRenaming)
          (RawRenaming.identity (scope := sourceScope)) := by
      intro position
      simp only [RawRenaming.compose, RawRenaming.identity]
      exact leftInverseProperty position
    rw [RawTerm.rename_pointwise composeIsIdentity sourceTerm]
    exact RawTerm.rename_identity_apply sourceTerm
  rw [roundTrip] at pulledChain
  exact pulledChain

end FX1Poly.Core
