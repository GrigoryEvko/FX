import FX1Poly.Typed.FundamentalLevelIndexed
import FX1Poly.Core.RawTermRenameSubstCommute
import FX1Poly.Core.StrongNormalizationRename

/-! # FX1Poly/Typed/ClosedLevelIndexed
    — the closed-term reducibility + strong-normalization handoff from the level-indexed fundamental theorem

The decoupled-`subjectLevel` fundamental conclusion `FundamentalConclusionLevelIndexed` (Route 2, the
dependent FT — see `FundamentalLevelIndexed.lean`) is stated over an arbitrary per-variable-level reducible
closing environment `ReducibleEnvVec`.  At the EMPTY context that environment is vacuous, so a level-indexed
fundamental conclusion for a closed term specializes immediately to closed reducibility under any target
substitution, and from there (CR1, at a positive level) to closed strong normalization.

These are the downstream handoff lemmas (#497/#498) the semantic spine consumes — the level-indexed twins of
`HasTypeDescPi.closedSubjectReducibleUnderSubstFromFormation` /
`HasTypeDescPi.closedSubjectStronglyNormalizingFromFormation`.  They are stated CONDITIONAL on the level-
indexed fundamental conclusion for the closed term (an explicit hypothesis, exactly as the committed
`*FromFormation` handoffs are conditional on the formation-engine premise); they become UNCONDITIONAL the
moment the `HasTypeDescPi.rec` level-indexed assembly is finished and supplies that conclusion for every
closed derivation.  No proof is hidden — the fundamental conclusion is an argument.

## Zero-axiom verification

`ReducibleEnvVec.empty` + CR1 (`IsReducibleMemberAt.stronglyNormalizing`, positive level) + the unique-empty-
renaming SN reflection (`StepStar.isStronglyNormalizing_of_rename` through `RawTerm.rename_subst_commute`).
No `axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration gated
in `FX1PolyAudit/AuditTyped.lean`.
-/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation
open StepStar

/-- The empty per-variable level vector (`Fin 0 → Nat`, vacuous) — the level assignment the empty-context
environment carries. -/
def emptyLevelVector : Fin 0 → Nat := fun emptyIndex => emptyIndex.elim0

/-- **Closed reducibility under a closing substitution, from the level-indexed fundamental theorem.**
At the empty context the per-variable-level environment is vacuous (`ReducibleEnvVec.empty`), so a level-
indexed fundamental conclusion specializes immediately to a closed term under any target closing
substitution.  Level-indexed twin of `HasTypeDescPi.closedSubjectReducibleUnderSubstFromFormation`. -/
theorem closedSubjectReducibleFromLevelIndexed {profile : PolyProfile} (subjectLevel : Nat)
    {subject classifier : RawTerm 0}
    (levelIndexedFundamental :
      FundamentalConclusionLevelIndexed emptyLevelVector subjectLevel
        (TypingContext.empty : TypingContext profile 0) subject classifier)
    {targetScope : Nat} (substitution : RawTermSubst 0 (targetScope + 1)) :
    IsReducibleMemberAt subjectLevel
      (RawTerm.subst substitution classifier) (RawTerm.subst substitution subject) :=
  levelIndexedFundamental substitution (ReducibleEnvVec.empty emptyLevelVector substitution)

/-- **Closed strong normalization from the level-indexed fundamental theorem.**  CR1 (`stronglyNormalizing`,
at the positive level `predLevel+1`) on the closed reducibility under the unique empty closing substitution
into scope 1, then reflect strong normalization back along the unique empty renaming.  Level-indexed twin of
`HasTypeDescPi.closedSubjectStronglyNormalizingFromFormation`; becomes unconditional exactly when the level-
indexed fundamental theorem is assembled. -/
theorem closedSubjectStronglyNormalizingFromLevelIndexed {profile : PolyProfile} (predLevel : Nat)
    {subject classifier : RawTerm 0}
    (levelIndexedFundamental :
      FundamentalConclusionLevelIndexed emptyLevelVector (predLevel + 1)
        (TypingContext.empty : TypingContext profile 0) subject classifier) :
    IsStronglyNormalizing subject := by
  let emptyRenaming : RawRenaming 0 1 := fun emptyIndex => emptyIndex.elim0
  let emptySubstitution : RawTermSubst 0 1 :=
    RawRenaming.thenSubst emptyRenaming (RawTermSubst.identity : RawTermSubst 1 1)
  have subjectNormalizing :
      IsStronglyNormalizing (RawTerm.subst emptySubstitution subject) :=
    (closedSubjectReducibleFromLevelIndexed (predLevel + 1) levelIndexedFundamental
      emptySubstitution).stronglyNormalizing
  have renamedSubjectNormalizing :
      IsStronglyNormalizing (RawTerm.rename emptyRenaming subject) := by
    rw [← RawTerm.subst_identity_apply (RawTerm.rename emptyRenaming subject)]
    rwa [RawTerm.rename_subst_commute emptyRenaming
      (RawTermSubst.identity : RawTermSubst 1 1) subject]
  exact StepStar.isStronglyNormalizing_of_rename emptyRenaming renamedSubjectNormalizing

end FX1Poly.Typed
