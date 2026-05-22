import LeanFX2.Reduction.Conv
import LeanFX2.Reduction.StepStarToPar
import LeanFX2.Confluence.ParStarBridge

/-! # Confluence/ConvBridge — raw projection of typed Conv

Combines Phase 6.D's `Step.parStar.toRawConfluence` with Phase
6.E's `StepStar.toParStar` to give the headline corollary:

`Conv.toRawConfluence`: a typed `Conv sourceTerm targetTerm`
witnesses that the raw projections `sourceRaw` and `targetRaw`
converge to a common raw reduct.

This is the strongest typed Conv corollary available without
subject reduction (Phase 7).  Sufficient for elaborator
coherence and Layer 9 Algo's decidable conversion checks: the
raw form is canonical, so once two elaborated terms agree on
the raw projection, their types must be convertible (typing is
preserved by the elaborator).
-/

namespace LeanFX2

/-- **Raw-projection corollary** of typed `Conv`.

A typed convertibility witness directly produces a raw-side
join: the typed midpoint's raw projection IS the common reduct,
reachable from both endpoints' raw projections via single-step
StepStar-bridge composition.

Pipeline:
1. `Conv` unpacks to two `StepStar` chains converging at typed
   midTerm with raw projection midRaw.
2. `StepStar.toParStar` lifts each chain to `Step.parStar`.
3. `Step.parStar.toRawBridge` projects each to raw chains
   landing at midRaw — which IS the common reduct.

No `Step.parStar.toRawConfluence` needed because the typed Conv
already provides the join (unlike "given two chains FROM a
common source", here we have "two chains TO a common target"). -/
theorem Conv.toRawJoin
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar sourceRaw commonRaw ∧
      RawStep.parStar targetRaw commonRaw := by
  obtain ⟨_, midRaw, _, sourceChain, targetChain⟩ := convertibility
  exact ⟨midRaw,
    Step.parStar.toRawBridge sourceChain.toParStar,
    Step.parStar.toRawBridge targetChain.toParStar⟩

/-- Raw-join forward equivariance for `Conv` under typed renaming.

Given a typed `Conv sourceTerm targetTerm`, the renamed endpoints have a common
raw reduct: the raw projection of the renamed typed midpoint from the original
Conv witness.  This is the raw-output forward half of `Conv.rename_equivariant`;
it deliberately does not claim a typed `Conv` witness between the renamed
endpoints. -/
theorem Conv.rename_toRawJoin
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rawRenaming : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rawRenaming)
    {sourceType targetType : Ty level sourceScope}
    {sourceRaw targetRaw : RawTerm sourceScope}
    {sourceTerm : Term sourceCtx sourceType sourceRaw}
    {targetTerm : Term sourceCtx targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar
        (Term.toRaw (Term.rename termRenaming sourceTerm)) commonRaw ∧
      RawStep.parStar
        (Term.toRaw (Term.rename termRenaming targetTerm)) commonRaw := by
  obtain ⟨_, _, commonTerm, sourceChain, targetChain⟩ := convertibility
  exact ⟨Term.toRaw (Term.rename termRenaming commonTerm),
    StepStar.rename_toRawBridge termRenaming sourceChain,
    StepStar.rename_toRawBridge termRenaming targetChain⟩

/-- Canonical-weaken specialization of `Conv.rename_toRawJoin`. -/
theorem Conv.weaken_toRawJoin
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (newType : Ty level scope)
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar
        (Term.toRaw (Term.weaken newType sourceTerm)) commonRaw ∧
      RawStep.parStar
        (Term.toRaw (Term.weaken newType targetTerm)) commonRaw :=
  Conv.rename_toRawJoin (TermRenaming.weakenStep context newType)
    convertibility

/-- If the left endpoint of a `Conv` witness is a renamed term, then the
typed common reduct's raw projection is also in that raw renaming image.

This is a raw/index corollary on the path toward `Conv.rename_equivariant`, not
the full typed Conv equivariance theorem. -/
theorem Conv.renamed_left_commonRaw_in_rename_image
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rawRenaming : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rawRenaming)
    (rawRenamingInjective :
      ∀ leftPosition rightPosition,
        rawRenaming leftPosition = rawRenaming rightPosition →
          leftPosition = rightPosition)
    {sourceType : Ty level sourceScope}
    {targetType : Ty level targetScope}
    {sourceRaw : RawTerm sourceScope}
    {targetRaw : RawTerm targetScope}
    {sourceTerm : Term sourceCtx sourceType sourceRaw}
    {targetTerm : Term targetCtx targetType targetRaw}
    (convertibility : Conv (Term.rename termRenaming sourceTerm) targetTerm) :
    ∃ (commonType : Ty level targetScope) (commonRaw : RawTerm targetScope)
      (commonTerm : Term targetCtx commonType commonRaw),
      StepStar (Term.rename termRenaming sourceTerm) commonTerm ∧
      StepStar targetTerm commonTerm ∧
      ∃ commonInnerRaw : RawTerm sourceScope,
        commonRaw = commonInnerRaw.rename rawRenaming := by
  obtain ⟨commonType, commonRaw, commonTerm, sourceChain, targetChain⟩ :=
    convertibility
  exact ⟨commonType, commonRaw, commonTerm, sourceChain, targetChain,
    StepStar.renamed_source_targetRaw_in_rename_image
      termRenaming rawRenamingInjective sourceChain⟩

/-- Canonical-weaken specialization of
`Conv.renamed_left_commonRaw_in_rename_image`. -/
theorem Conv.weakened_left_commonRaw_in_weaken_image
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (newType : Ty level scope)
    {sourceType : Ty level scope}
    {targetType : Ty level (scope + 1)}
    {sourceRaw : RawTerm scope}
    {targetRaw : RawTerm (scope + 1)}
    {sourceTerm : Term sourceCtx sourceType sourceRaw}
    {targetTerm : Term (sourceCtx.cons newType) targetType targetRaw}
    (convertibility : Conv (Term.weaken newType sourceTerm) targetTerm) :
    ∃ (commonType : Ty level (scope + 1)) (commonRaw : RawTerm (scope + 1))
      (commonTerm : Term (sourceCtx.cons newType) commonType commonRaw),
      StepStar (Term.weaken newType sourceTerm) commonTerm ∧
      StepStar targetTerm commonTerm ∧
      ∃ commonInnerRaw : RawTerm scope,
        commonRaw = commonInnerRaw.weaken := by
  obtain ⟨commonType, commonRaw, commonTerm, sourceChain, targetChain⟩ :=
    convertibility
  exact ⟨commonType, commonRaw, commonTerm, sourceChain, targetChain,
    StepStar.weakened_source_targetRaw_in_weaken_image newType sourceChain⟩

/-- If the left endpoint raw projection of a `Conv` witness is in a raw
renaming image, then the typed common reduct's raw projection is also in that
image. -/
theorem Conv.left_commonRaw_in_rename_image_of_sourceRaw_eq
    {mode : Mode} {level sourceScope targetScope : Nat}
    {targetCtx : Ctx mode level targetScope}
    {rawRenaming : RawRenaming sourceScope targetScope}
    (rawRenamingInjective :
      ∀ leftPosition rightPosition,
        rawRenaming leftPosition = rawRenaming rightPosition →
          leftPosition = rightPosition)
    {sourceType targetType : Ty level targetScope}
    {sourceRaw targetRaw : RawTerm targetScope}
    {sourceInnerRaw : RawTerm sourceScope}
    {sourceTerm : Term targetCtx sourceType sourceRaw}
    {targetTerm : Term targetCtx targetType targetRaw}
    (sourceEq : sourceRaw = sourceInnerRaw.rename rawRenaming)
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ (commonType : Ty level targetScope) (commonRaw : RawTerm targetScope)
      (commonTerm : Term targetCtx commonType commonRaw),
      StepStar sourceTerm commonTerm ∧
      StepStar targetTerm commonTerm ∧
      ∃ commonInnerRaw : RawTerm sourceScope,
        commonRaw = commonInnerRaw.rename rawRenaming := by
  obtain ⟨commonType, commonRaw, commonTerm, sourceChain, targetChain⟩ :=
    convertibility
  exact ⟨commonType, commonRaw, commonTerm, sourceChain, targetChain,
    StepStar.sourceRaw_in_rename_image_targetRaw_in_rename_image
      rawRenamingInjective sourceEq sourceChain⟩

/-- Canonical-weaken specialization of
`Conv.left_commonRaw_in_rename_image_of_sourceRaw_eq`. -/
theorem Conv.left_commonRaw_in_weaken_image_of_sourceRaw_eq
    {mode : Mode} {level scope : Nat}
    {targetCtx : Ctx mode level (scope + 1)}
    {sourceType targetType : Ty level (scope + 1)}
    {sourceRaw targetRaw : RawTerm (scope + 1)}
    {sourceInnerRaw : RawTerm scope}
    {sourceTerm : Term targetCtx sourceType sourceRaw}
    {targetTerm : Term targetCtx targetType targetRaw}
    (sourceEq : sourceRaw = sourceInnerRaw.weaken)
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ (commonType : Ty level (scope + 1)) (commonRaw : RawTerm (scope + 1))
      (commonTerm : Term targetCtx commonType commonRaw),
      StepStar sourceTerm commonTerm ∧
      StepStar targetTerm commonTerm ∧
      ∃ commonInnerRaw : RawTerm scope,
        commonRaw = commonInnerRaw.weaken := by
  obtain ⟨commonType, commonRaw, commonTerm, sourceChain, targetChain⟩ :=
    convertibility
  exact ⟨commonType, commonRaw, commonTerm, sourceChain, targetChain,
    StepStar.sourceRaw_in_weaken_image_targetRaw_in_weaken_image
      sourceEq sourceChain⟩

/-- Right-endpoint variant of
`Conv.renamed_left_commonRaw_in_rename_image`. -/
theorem Conv.renamed_right_commonRaw_in_rename_image
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rawRenaming : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rawRenaming)
    (rawRenamingInjective :
      ∀ leftPosition rightPosition,
        rawRenaming leftPosition = rawRenaming rightPosition →
          leftPosition = rightPosition)
    {sourceType : Ty level targetScope}
    {targetType : Ty level sourceScope}
    {sourceRaw : RawTerm targetScope}
    {targetRaw : RawTerm sourceScope}
    {sourceTerm : Term targetCtx sourceType sourceRaw}
    {targetTerm : Term sourceCtx targetType targetRaw}
    (convertibility : Conv sourceTerm (Term.rename termRenaming targetTerm)) :
    ∃ (commonType : Ty level targetScope) (commonRaw : RawTerm targetScope)
      (commonTerm : Term targetCtx commonType commonRaw),
      StepStar sourceTerm commonTerm ∧
      StepStar (Term.rename termRenaming targetTerm) commonTerm ∧
      ∃ commonInnerRaw : RawTerm sourceScope,
        commonRaw = commonInnerRaw.rename rawRenaming := by
  obtain ⟨commonType, commonRaw, commonTerm, sourceChain, targetChain⟩ :=
    convertibility
  exact ⟨commonType, commonRaw, commonTerm, sourceChain, targetChain,
    StepStar.renamed_source_targetRaw_in_rename_image
      termRenaming rawRenamingInjective targetChain⟩

/-- Canonical-weaken right-endpoint variant. -/
theorem Conv.weakened_right_commonRaw_in_weaken_image
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (newType : Ty level scope)
    {sourceType : Ty level (scope + 1)}
    {targetType : Ty level scope}
    {sourceRaw : RawTerm (scope + 1)}
    {targetRaw : RawTerm scope}
    {sourceTerm : Term (sourceCtx.cons newType) sourceType sourceRaw}
    {targetTerm : Term sourceCtx targetType targetRaw}
    (convertibility : Conv sourceTerm (Term.weaken newType targetTerm)) :
    ∃ (commonType : Ty level (scope + 1)) (commonRaw : RawTerm (scope + 1))
      (commonTerm : Term (sourceCtx.cons newType) commonType commonRaw),
      StepStar sourceTerm commonTerm ∧
      StepStar (Term.weaken newType targetTerm) commonTerm ∧
      ∃ commonInnerRaw : RawTerm scope,
        commonRaw = commonInnerRaw.weaken := by
  obtain ⟨commonType, commonRaw, commonTerm, sourceChain, targetChain⟩ :=
    convertibility
  exact ⟨commonType, commonRaw, commonTerm, sourceChain, targetChain,
    StepStar.weakened_source_targetRaw_in_weaken_image newType targetChain⟩

/-- Right-endpoint variant of
`Conv.left_commonRaw_in_rename_image_of_sourceRaw_eq`. -/
theorem Conv.right_commonRaw_in_rename_image_of_targetRaw_eq
    {mode : Mode} {level sourceScope targetScope : Nat}
    {targetCtx : Ctx mode level targetScope}
    {rawRenaming : RawRenaming sourceScope targetScope}
    (rawRenamingInjective :
      ∀ leftPosition rightPosition,
        rawRenaming leftPosition = rawRenaming rightPosition →
          leftPosition = rightPosition)
    {sourceType targetType : Ty level targetScope}
    {sourceRaw targetRaw : RawTerm targetScope}
    {targetInnerRaw : RawTerm sourceScope}
    {sourceTerm : Term targetCtx sourceType sourceRaw}
    {targetTerm : Term targetCtx targetType targetRaw}
    (targetEq : targetRaw = targetInnerRaw.rename rawRenaming)
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ (commonType : Ty level targetScope) (commonRaw : RawTerm targetScope)
      (commonTerm : Term targetCtx commonType commonRaw),
      StepStar sourceTerm commonTerm ∧
      StepStar targetTerm commonTerm ∧
      ∃ commonInnerRaw : RawTerm sourceScope,
        commonRaw = commonInnerRaw.rename rawRenaming := by
  obtain ⟨commonType, commonRaw, commonTerm, sourceChain, targetChain⟩ :=
    convertibility
  exact ⟨commonType, commonRaw, commonTerm, sourceChain, targetChain,
    StepStar.sourceRaw_in_rename_image_targetRaw_in_rename_image
      rawRenamingInjective targetEq targetChain⟩

/-- Canonical-weaken right-endpoint source-equality variant. -/
theorem Conv.right_commonRaw_in_weaken_image_of_targetRaw_eq
    {mode : Mode} {level scope : Nat}
    {targetCtx : Ctx mode level (scope + 1)}
    {sourceType targetType : Ty level (scope + 1)}
    {sourceRaw targetRaw : RawTerm (scope + 1)}
    {targetInnerRaw : RawTerm scope}
    {sourceTerm : Term targetCtx sourceType sourceRaw}
    {targetTerm : Term targetCtx targetType targetRaw}
    (targetEq : targetRaw = targetInnerRaw.weaken)
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ (commonType : Ty level (scope + 1)) (commonRaw : RawTerm (scope + 1))
      (commonTerm : Term targetCtx commonType commonRaw),
      StepStar sourceTerm commonTerm ∧
      StepStar targetTerm commonTerm ∧
      ∃ commonInnerRaw : RawTerm scope,
        commonRaw = commonInnerRaw.weaken := by
  obtain ⟨commonType, commonRaw, commonTerm, sourceChain, targetChain⟩ :=
    convertibility
  exact ⟨commonType, commonRaw, commonTerm, sourceChain, targetChain,
    StepStar.sourceRaw_in_weaken_image_targetRaw_in_weaken_image
      targetEq targetChain⟩

/-! ## Direct raw-join packaging for rename-image Conv consumers -/

/-- If the left endpoint of a `Conv` witness is a renamed typed term, then
the raw join produced by `Conv` can be chosen inside the same raw renaming
image. -/
theorem Conv.renamed_left_toRawJoin_in_rename_image
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rawRenaming : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rawRenaming)
    (rawRenamingInjective :
      ∀ leftPosition rightPosition,
        rawRenaming leftPosition = rawRenaming rightPosition →
          leftPosition = rightPosition)
    {sourceType : Ty level sourceScope}
    {targetType : Ty level targetScope}
    {sourceRaw : RawTerm sourceScope}
    {targetRaw : RawTerm targetScope}
    {sourceTerm : Term sourceCtx sourceType sourceRaw}
    {targetTerm : Term targetCtx targetType targetRaw}
    (convertibility : Conv (Term.rename termRenaming sourceTerm) targetTerm) :
    ∃ commonInnerRaw : RawTerm sourceScope,
      RawStep.parStar
        (Term.toRaw (Term.rename termRenaming sourceTerm))
        (commonInnerRaw.rename rawRenaming) ∧
      RawStep.parStar targetRaw (commonInnerRaw.rename rawRenaming) := by
  obtain ⟨_commonType, _commonRaw, _commonTerm, sourceChain, targetChain,
      commonInnerRaw, commonEq⟩ :=
    Conv.renamed_left_commonRaw_in_rename_image
      termRenaming rawRenamingInjective convertibility
  cases commonEq
  exact ⟨commonInnerRaw,
    Step.parStar.toRawBridge sourceChain.toParStar,
    Step.parStar.toRawBridge targetChain.toParStar⟩

/-- Canonical-weaken specialization of
`Conv.renamed_left_toRawJoin_in_rename_image`. -/
theorem Conv.weakened_left_toRawJoin_in_weaken_image
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (newType : Ty level scope)
    {sourceType : Ty level scope}
    {targetType : Ty level (scope + 1)}
    {sourceRaw : RawTerm scope}
    {targetRaw : RawTerm (scope + 1)}
    {sourceTerm : Term sourceCtx sourceType sourceRaw}
    {targetTerm : Term (sourceCtx.cons newType) targetType targetRaw}
    (convertibility : Conv (Term.weaken newType sourceTerm) targetTerm) :
    ∃ commonInnerRaw : RawTerm scope,
      RawStep.parStar
        (Term.toRaw (Term.weaken newType sourceTerm))
        commonInnerRaw.weaken ∧
      RawStep.parStar targetRaw commonInnerRaw.weaken := by
  obtain ⟨_commonType, _commonRaw, _commonTerm, sourceChain, targetChain,
      commonInnerRaw, commonEq⟩ :=
    Conv.weakened_left_commonRaw_in_weaken_image newType convertibility
  cases commonEq
  exact ⟨commonInnerRaw,
    Step.parStar.toRawBridge sourceChain.toParStar,
    Step.parStar.toRawBridge targetChain.toParStar⟩

/-- If the right endpoint of a `Conv` witness is a renamed typed term, then
the raw join produced by `Conv` can be chosen inside the same raw renaming
image. -/
theorem Conv.renamed_right_toRawJoin_in_rename_image
    {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rawRenaming : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rawRenaming)
    (rawRenamingInjective :
      ∀ leftPosition rightPosition,
        rawRenaming leftPosition = rawRenaming rightPosition →
          leftPosition = rightPosition)
    {sourceType : Ty level targetScope}
    {targetType : Ty level sourceScope}
    {sourceRaw : RawTerm targetScope}
    {targetRaw : RawTerm sourceScope}
    {sourceTerm : Term targetCtx sourceType sourceRaw}
    {targetTerm : Term sourceCtx targetType targetRaw}
    (convertibility : Conv sourceTerm (Term.rename termRenaming targetTerm)) :
    ∃ commonInnerRaw : RawTerm sourceScope,
      RawStep.parStar sourceRaw (commonInnerRaw.rename rawRenaming) ∧
      RawStep.parStar
        (Term.toRaw (Term.rename termRenaming targetTerm))
        (commonInnerRaw.rename rawRenaming) := by
  obtain ⟨_commonType, _commonRaw, _commonTerm, sourceChain, targetChain,
      commonInnerRaw, commonEq⟩ :=
    Conv.renamed_right_commonRaw_in_rename_image
      termRenaming rawRenamingInjective convertibility
  cases commonEq
  exact ⟨commonInnerRaw,
    Step.parStar.toRawBridge sourceChain.toParStar,
    Step.parStar.toRawBridge targetChain.toParStar⟩

/-- Canonical-weaken specialization of
`Conv.renamed_right_toRawJoin_in_rename_image`. -/
theorem Conv.weakened_right_toRawJoin_in_weaken_image
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (newType : Ty level scope)
    {sourceType : Ty level (scope + 1)}
    {targetType : Ty level scope}
    {sourceRaw : RawTerm (scope + 1)}
    {targetRaw : RawTerm scope}
    {sourceTerm : Term (sourceCtx.cons newType) sourceType sourceRaw}
    {targetTerm : Term sourceCtx targetType targetRaw}
    (convertibility : Conv sourceTerm (Term.weaken newType targetTerm)) :
    ∃ commonInnerRaw : RawTerm scope,
      RawStep.parStar sourceRaw commonInnerRaw.weaken ∧
      RawStep.parStar
        (Term.toRaw (Term.weaken newType targetTerm))
        commonInnerRaw.weaken := by
  obtain ⟨_commonType, _commonRaw, _commonTerm, sourceChain, targetChain,
      commonInnerRaw, commonEq⟩ :=
    Conv.weakened_right_commonRaw_in_weaken_image newType convertibility
  cases commonEq
  exact ⟨commonInnerRaw,
    Step.parStar.toRawBridge sourceChain.toParStar,
    Step.parStar.toRawBridge targetChain.toParStar⟩

/-- If the left endpoint raw projection is in a raw renaming image,
then the raw join produced by `Conv` can be chosen inside that same
image. -/
theorem Conv.left_toRawJoin_in_rename_image_of_sourceRaw_eq
    {mode : Mode} {level sourceScope targetScope : Nat}
    {targetCtx : Ctx mode level targetScope}
    {rawRenaming : RawRenaming sourceScope targetScope}
    (rawRenamingInjective :
      ∀ leftPosition rightPosition,
        rawRenaming leftPosition = rawRenaming rightPosition →
          leftPosition = rightPosition)
    {sourceType targetType : Ty level targetScope}
    {sourceRaw targetRaw : RawTerm targetScope}
    {sourceInnerRaw : RawTerm sourceScope}
    {sourceTerm : Term targetCtx sourceType sourceRaw}
    {targetTerm : Term targetCtx targetType targetRaw}
    (sourceEq : sourceRaw = sourceInnerRaw.rename rawRenaming)
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ commonInnerRaw : RawTerm sourceScope,
      RawStep.parStar sourceRaw (commonInnerRaw.rename rawRenaming) ∧
      RawStep.parStar targetRaw (commonInnerRaw.rename rawRenaming) := by
  obtain ⟨_commonType, _commonRaw, _commonTerm, sourceChain, targetChain,
      commonInnerRaw, commonEq⟩ :=
    Conv.left_commonRaw_in_rename_image_of_sourceRaw_eq
      rawRenamingInjective sourceEq convertibility
  cases commonEq
  exact ⟨commonInnerRaw,
    Step.parStar.toRawBridge sourceChain.toParStar,
    Step.parStar.toRawBridge targetChain.toParStar⟩

/-- Canonical-weaken specialization of
`Conv.left_toRawJoin_in_rename_image_of_sourceRaw_eq`. -/
theorem Conv.left_toRawJoin_in_weaken_image_of_sourceRaw_eq
    {mode : Mode} {level scope : Nat}
    {targetCtx : Ctx mode level (scope + 1)}
    {sourceType targetType : Ty level (scope + 1)}
    {sourceRaw targetRaw : RawTerm (scope + 1)}
    {sourceInnerRaw : RawTerm scope}
    {sourceTerm : Term targetCtx sourceType sourceRaw}
    {targetTerm : Term targetCtx targetType targetRaw}
    (sourceEq : sourceRaw = sourceInnerRaw.weaken)
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ commonInnerRaw : RawTerm scope,
      RawStep.parStar sourceRaw commonInnerRaw.weaken ∧
      RawStep.parStar targetRaw commonInnerRaw.weaken := by
  obtain ⟨_commonType, _commonRaw, _commonTerm, sourceChain, targetChain,
      commonInnerRaw, commonEq⟩ :=
    Conv.left_commonRaw_in_weaken_image_of_sourceRaw_eq
      sourceEq convertibility
  cases commonEq
  exact ⟨commonInnerRaw,
    Step.parStar.toRawBridge sourceChain.toParStar,
    Step.parStar.toRawBridge targetChain.toParStar⟩

/-- If the right endpoint raw projection is in a raw renaming image,
then the raw join produced by `Conv` can be chosen inside that same
image. -/
theorem Conv.right_toRawJoin_in_rename_image_of_targetRaw_eq
    {mode : Mode} {level sourceScope targetScope : Nat}
    {targetCtx : Ctx mode level targetScope}
    {rawRenaming : RawRenaming sourceScope targetScope}
    (rawRenamingInjective :
      ∀ leftPosition rightPosition,
        rawRenaming leftPosition = rawRenaming rightPosition →
          leftPosition = rightPosition)
    {sourceType targetType : Ty level targetScope}
    {sourceRaw targetRaw : RawTerm targetScope}
    {targetInnerRaw : RawTerm sourceScope}
    {sourceTerm : Term targetCtx sourceType sourceRaw}
    {targetTerm : Term targetCtx targetType targetRaw}
    (targetEq : targetRaw = targetInnerRaw.rename rawRenaming)
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ commonInnerRaw : RawTerm sourceScope,
      RawStep.parStar sourceRaw (commonInnerRaw.rename rawRenaming) ∧
      RawStep.parStar targetRaw (commonInnerRaw.rename rawRenaming) := by
  obtain ⟨_commonType, _commonRaw, _commonTerm, sourceChain, targetChain,
      commonInnerRaw, commonEq⟩ :=
    Conv.right_commonRaw_in_rename_image_of_targetRaw_eq
      rawRenamingInjective targetEq convertibility
  cases commonEq
  exact ⟨commonInnerRaw,
    Step.parStar.toRawBridge sourceChain.toParStar,
    Step.parStar.toRawBridge targetChain.toParStar⟩

/-- Canonical-weaken specialization of
`Conv.right_toRawJoin_in_rename_image_of_targetRaw_eq`. -/
theorem Conv.right_toRawJoin_in_weaken_image_of_targetRaw_eq
    {mode : Mode} {level scope : Nat}
    {targetCtx : Ctx mode level (scope + 1)}
    {sourceType targetType : Ty level (scope + 1)}
    {sourceRaw targetRaw : RawTerm (scope + 1)}
    {targetInnerRaw : RawTerm scope}
    {sourceTerm : Term targetCtx sourceType sourceRaw}
    {targetTerm : Term targetCtx targetType targetRaw}
    (targetEq : targetRaw = targetInnerRaw.weaken)
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ commonInnerRaw : RawTerm scope,
      RawStep.parStar sourceRaw commonInnerRaw.weaken ∧
      RawStep.parStar targetRaw commonInnerRaw.weaken := by
  obtain ⟨_commonType, _commonRaw, _commonTerm, sourceChain, targetChain,
      commonInnerRaw, commonEq⟩ :=
    Conv.right_commonRaw_in_weaken_image_of_targetRaw_eq
      targetEq convertibility
  cases commonEq
  exact ⟨commonInnerRaw,
    Step.parStar.toRawBridge sourceChain.toParStar,
    Step.parStar.toRawBridge targetChain.toParStar⟩

/-- Raw-only renaming variant of `Conv.rename_toRawJoin`.

Given a typed convertibility witness `Conv sourceTerm targetTerm` and a raw
renaming `rawRenaming`, the renamed raw projections `sourceRaw.rename
rawRenaming` and `targetRaw.rename rawRenaming` share a common raw reduct.
Unlike `Conv.rename_toRawJoin`, this requires no typed `TermRenaming` —
useful when downstream consumers (Conv.trans backward inversion, K13 NbE
soundness) only need raw-level equivariance and prefer not to thread a
typing morphism through. -/
theorem Conv.rawRename_toRawJoin
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    {targetScope : Nat}
    (rawRenaming : RawRenaming scope targetScope)
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.rename rawRenaming) commonRaw ∧
      RawStep.parStar (targetRaw.rename rawRenaming) commonRaw := by
  obtain ⟨commonRaw, sourceChain, targetChain⟩ := Conv.toRawJoin convertibility
  exact ⟨commonRaw.rename rawRenaming,
    RawStep.parStar.rename_compatible rawRenaming sourceChain,
    RawStep.parStar.rename_compatible rawRenaming targetChain⟩

/-- Canonical-weaken specialization of `Conv.rawRename_toRawJoin`.

Surface form `sourceRaw.weaken` / `targetRaw.weaken` matches the shape K13
NbE β-step consumers reach for at call sites: lift a Conv witness through
the canonical weakening into the under-binder world without leaving the
raw layer. -/
theorem Conv.rawWeaken_toRawJoin
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar sourceRaw.weaken commonRaw ∧
      RawStep.parStar targetRaw.weaken commonRaw :=
  Conv.rawRename_toRawJoin RawRenaming.weaken convertibility

/-- Raw-only substitution variant of the typed-Conv → raw-join projection.

Given a typed `Conv sourceTerm targetTerm` and a raw substitution `rawSubst`,
the substituted raw projections `sourceRaw.subst rawSubst` and
`targetRaw.subst rawSubst` share a common raw reduct.  Useful for downstream
backward-inversion consumers (K12.28 Geuvers β-η critical pair, K13 NbE
β-step) that need substitution equivariance at the raw layer without
threading a typed substitution morphism. -/
theorem Conv.rawSubst_toRawJoin
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    {targetScope : Nat}
    (rawSubst : RawTermSubst scope targetScope)
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.subst rawSubst) commonRaw ∧
      RawStep.parStar (targetRaw.subst rawSubst) commonRaw := by
  obtain ⟨commonRaw, sourceChain, targetChain⟩ := Conv.toRawJoin convertibility
  exact ⟨commonRaw.subst rawSubst,
    RawStep.parStar.subst_compatible_same rawSubst sourceChain,
    RawStep.parStar.subst_compatible_same rawSubst targetChain⟩

/-- Singleton-substitution specialization of `Conv.rawSubst_toRawJoin`.

Surface form `sourceRaw.subst0 argRaw` / `targetRaw.subst0 argRaw` matches
the β-redex shape that K12.28 Geuvers 1992 critical-pair joinability and
K13.18 NbE β-step consumers reach for at the raw layer.  Pins the argument
across both endpoints; for heterogeneous arg-chains use
`RawStep.parStar.subst0_par` directly. -/
theorem Conv.rawSubst0_toRawJoin
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level (scope + 1)}
    {sourceType targetType : Ty level (scope + 1)}
    {sourceRaw targetRaw : RawTerm (scope + 1)}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (argRaw : RawTerm scope)
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar (sourceRaw.subst0 argRaw) commonRaw ∧
      RawStep.parStar (targetRaw.subst0 argRaw) commonRaw :=
  Conv.rawSubst_toRawJoin (RawTermSubst.singleton argRaw) convertibility

/-- Heterogeneous β-redex raw join.

Given two typed Conv witnesses — one for the body (under-binder), one for
the argument — produce a raw join of the β-redex shapes
`bodySourceRaw.subst0 argSourceRaw` and `bodyTargetRaw.subst0 argTargetRaw`.
Both endpoints evolve through their own chain, meeting at the substituted
midpoints.

This matches the shape K12.28 Geuvers 1992 β-η critical-pair joinability
and K13.18 NbE β-step soundness need: a β-redex where neither the body nor
the argument is pinned across the Conv. -/
theorem Conv.rawSubst0_par_toRawJoin
    {mode : Mode} {level scope : Nat}
    {bodyContext : Ctx mode level (scope + 1)}
    {argContext : Ctx mode level scope}
    {bodySourceType bodyTargetType : Ty level (scope + 1)}
    {argSourceType argTargetType : Ty level scope}
    {bodySourceRaw bodyTargetRaw : RawTerm (scope + 1)}
    {argSourceRaw argTargetRaw : RawTerm scope}
    {bodySource : Term bodyContext bodySourceType bodySourceRaw}
    {bodyTarget : Term bodyContext bodyTargetType bodyTargetRaw}
    {argSource : Term argContext argSourceType argSourceRaw}
    {argTarget : Term argContext argTargetType argTargetRaw}
    (bodyConvertibility : Conv bodySource bodyTarget)
    (argConvertibility : Conv argSource argTarget) :
    ∃ commonRaw,
      RawStep.parStar (bodySourceRaw.subst0 argSourceRaw) commonRaw ∧
      RawStep.parStar (bodyTargetRaw.subst0 argTargetRaw) commonRaw := by
  obtain ⟨bodyMidRaw, bodySourceChain, bodyTargetChain⟩ :=
    Conv.toRawJoin bodyConvertibility
  obtain ⟨argMidRaw, argSourceChain, argTargetChain⟩ :=
    Conv.toRawJoin argConvertibility
  exact ⟨bodyMidRaw.subst0 argMidRaw,
    RawStep.parStar.subst0_par bodySourceChain argSourceChain,
    RawStep.parStar.subst0_par bodyTargetChain argTargetChain⟩

/-- Argument-only β-redex raw join.

Dual to `Conv.rawSubst0_toRawJoin` (which pins the argument and varies the
body): here the body raw form is pinned, and a Conv witness governs the
argument.  Useful when an external β-step manipulates only the argument
side while the body has already canonicalized. -/
theorem Conv.rawSubst0_arg_toRawJoin
    {mode : Mode} {level scope : Nat}
    {argContext : Ctx mode level scope}
    {argSourceType argTargetType : Ty level scope}
    {argSourceRaw argTargetRaw : RawTerm scope}
    {argSource : Term argContext argSourceType argSourceRaw}
    {argTarget : Term argContext argTargetType argTargetRaw}
    (bodyRaw : RawTerm (scope + 1))
    (argConvertibility : Conv argSource argTarget) :
    ∃ commonRaw,
      RawStep.parStar (bodyRaw.subst0 argSourceRaw) commonRaw ∧
      RawStep.parStar (bodyRaw.subst0 argTargetRaw) commonRaw := by
  obtain ⟨argMidRaw, argSourceChain, argTargetChain⟩ :=
    Conv.toRawJoin argConvertibility
  exact ⟨bodyRaw.subst0 argMidRaw,
    RawStep.parStar.subst0_par (RawStep.parStar.refl bodyRaw) argSourceChain,
    RawStep.parStar.subst0_par (RawStep.parStar.refl bodyRaw) argTargetChain⟩

end LeanFX2
