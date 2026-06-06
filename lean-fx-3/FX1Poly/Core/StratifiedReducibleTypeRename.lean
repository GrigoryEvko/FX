import FX1Poly.Core.StratifiedReducibleType
import FX1Poly.Core.WeakHeadStepRenameReflect
import FX1Poly.Core.CandidateInterpretationRename
import FX1Poly.Core.StrongNormalizationRenameForward

/-! # Foundation/PolyCell/Core/StratifiedReducibleTypeRename
    — the stratified reducibility step-functor is closed under a left-invertible renaming, NEUTRAL leaf

Renaming-closure asks that the stratified reducibility relation `ReducibleTypeStep` / `ReducibleTypeAt` be closed
under renaming.  The structural arms (`neutral`, `whnfExpand`, `universeCode`, `ofPointwiseIff`) transport
along a left-invertible renaming via the renaming substrate shipped for the purpose
(`isStronglyNormalizing_rename_of_leftInverse`, `WeakHeadStep.rename`,
`WeakHeadStep.rename_preserves_weakHeadNormal_of_leftInverse`, `RawTerm.rename_rootGenerator`).  This file
lands the `neutral` LEAF: a weak-head-normal, non-Π, non-universe type renames to one, with the same
strong-normalization candidate.

## The `piType` arm is genuinely obstructed (Kripke requirement) — NOT shipped here

The dependent-arrow arm does NOT close under renaming in this NON-Kripke formulation, and the obstruction is
structural, not a matter of effort.  `ReducibleTypeStep.piType`'s candidate is

  `fun functionTerm => ∀ argument : RawTerm scope, domainCandidate argument →
      codomainCandidate argument (app functionTerm argument)`

quantifying over SAME-scope arguments.  Renaming `ρ : scope → scope'` ENLARGES the scope, so rebuilding the
arm at `scope'` via the `piType` constructor demands the codomain reducible under EVERY `scope'`-argument
`a'` of the renamed domain — including fresh-variable arguments outside the image of `rename ρ`.  The inner
induction hypothesis on the codomain only supplies reducibility under RENAMED arguments
(`subst0 (rename ρ.lift B) (rename ρ a)` for source arguments `a`), never the fresh ones.  Closing the gap
requires KRIPKE-indexing the arrow candidate (a `∀`-renaming quantifier `f ∈ Π A.B iff ∀ ρ a, f[ρ] a ∈ B[ρ,a]`,
per Abel/Adjedj NbE logical relations) — a foundational refactor of `ReducibleTypeStep`, not a downstream
lemma.  The FX dependent fundamental theorem sidesteps this entirely by placing the Kripke structure in the
ENVIRONMENT (`ReducibleEnvAtAllLevels`, all-level candidates), so standalone candidate rename-closure is OFF
the fundamental-theorem critical path; this neutral leaf is the cleanly-shippable fragment.

## Zero-axiom verification

One `ReducibleTypeStep.neutral` application; the three premises discharged by
`WeakHeadStep.rename_preserves_weakHeadNormal_of_leftInverse` and two `RawTerm.rename_rootGenerator`
rewrites.  No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Gated per
declaration in `FX1PolyAudit/AuditCoreSubstrate.lean`.
-/

namespace FX1Poly.Core
open FX1Poly.Foundation
open StepStar

/-- **Neutral-leaf rename-closure of the stratified reducibility step-functor.**  A weak-head-normal,
non-Π, non-universe type (the `neutral` arm's hypotheses) renames, along a left-invertible renaming, to a
type the step-functor again classifies via its `neutral` arm — at the strong-normalization candidate.
Weak-head normality transports by `rename_preserves_weakHeadNormal_of_leftInverse`; the non-Π / non-universe
root guards by `RawTerm.rename_rootGenerator` (renaming never changes the head generator).  The lower
relation is an arbitrary parameter at the target scope — the `neutral` arm does not consume it. -/
theorem ReducibleTypeStep.neutralRename_of_leftInverse {sourceScope targetScope : Nat}
    {lowerReducible : RawTerm targetScope → (RawTerm targetScope → Prop) → Prop}
    (forwardRenaming : RawRenaming sourceScope targetScope)
    (leftInverseRenaming : RawRenaming targetScope sourceScope)
    (leftInverseProperty :
      ∀ index : Fin sourceScope, leftInverseRenaming (forwardRenaming index) = index)
    {typeCode : RawTerm sourceScope}
    (noWeakHeadStep : ∀ reduct : RawTerm sourceScope, ¬ WeakHeadStep typeCode reduct)
    (notPiType : typeCode.rootGenerator ≠ Generator.gen_piTyCode)
    (notUniverse : typeCode.rootGenerator ≠ Generator.gen_universeCode) :
    ReducibleTypeStep lowerReducible (RawTerm.rename forwardRenaming typeCode) IsStronglyNormalizing := by
  apply ReducibleTypeStep.neutral
  · exact WeakHeadStep.rename_preserves_weakHeadNormal_of_leftInverse
      forwardRenaming leftInverseRenaming leftInverseProperty noWeakHeadStep
  · rw [RawTerm.rename_rootGenerator]; exact notPiType
  · rw [RawTerm.rename_rootGenerator]; exact notUniverse

/-- **Member transport for the neutral leaf.**  The `neutral` candidate is `IsStronglyNormalizing` both
before and after the renaming, so an old member transports to a member of the renamed type by forward
strong-normalization preservation (`isStronglyNormalizing_rename_of_leftInverse`).  This is the member-level
companion of `neutralRename_of_leftInverse`, completing the neutral leaf of the rename-closure. -/
theorem ReducibleTypeStep.neutralRenameMember_of_leftInverse {sourceScope targetScope : Nat}
    (forwardRenaming : RawRenaming sourceScope targetScope)
    (leftInverseRenaming : RawRenaming targetScope sourceScope)
    (leftInverseProperty :
      ∀ index : Fin sourceScope, leftInverseRenaming (forwardRenaming index) = index)
    {memberTerm : RawTerm sourceScope}
    (memberStronglyNormalizing : IsStronglyNormalizing memberTerm) :
    IsStronglyNormalizing (RawTerm.rename forwardRenaming memberTerm) :=
  isStronglyNormalizing_rename_of_leftInverse forwardRenaming leftInverseRenaming
    leftInverseProperty memberStronglyNormalizing

end FX1Poly.Core
