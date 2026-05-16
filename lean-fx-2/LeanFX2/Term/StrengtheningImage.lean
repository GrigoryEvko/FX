import LeanFX2.Term.TypedInversion
import LeanFX2.Term.HEqCongr

/-! # Term/StrengtheningImage — soundness of typed strengthening.

`StrengtheningResult` records the index-level content of a successful
typed partial strengthening: the recovered target type/raw and the
forward-renaming equations for those indices.  This module adds the
term-level semantic content as a parallel certificate: successful
strengthening re-renames the recovered target term back to the original
source term.

The parallel record keeps the existing computational dispatcher stable.
Recursive constructor soundness lemmas can be added incrementally without
forcing every `StrengtheningResult` producer to grow a new field at once.
-/

namespace LeanFX2

namespace Term

universe u v

/-- Term-level semantic soundness for a typed strengthening result.

The target term, renamed through the strengthening's forward morphism, is
heterogeneously equal to the source term.  Heterogeneous equality is the
right equality here because `StrengtheningResult.renamedTarget` carries
the renamed target indices, while the source term carries the original
indices; the record's `typeRenames` and `rawRenames` fields explain that
these indices are propositionally equal. -/
structure StrengtheningSoundness {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {sourceType : Ty level sourceScope}
    {sourceRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {sourceTerm : Term sourceCtx sourceType sourceRaw}
    (result : StrengtheningResult strengthening sourceTerm) where
  termRenames : HEq sourceTerm result.renamedTarget

/-- Heterogeneous equality between a value and a cast of that same value
on the right.  This isolates the `Eq.rec` bookkeeping used by the variable
case of `Term.rename`. -/
theorem heq_cast_right {indexType : Sort u} {motive : indexType → Sort v}
    {firstIndex secondIndex : indexType}
    (indexEq : firstIndex = secondIndex)
    (value : motive secondIndex) :
    HEq value (indexEq ▸ value) := by
  cases indexEq
  rfl

/-- Renaming a variable is heterogeneously equal to the variable at the
renamed position.  `Term.rename` casts this variable across the
`TermRenaming` proof; this lemma packages the cast proof once for
strengthening soundness. -/
theorem rename_var_heq {mode : Mode} {level sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming sourceScope targetScope}
    (termRenaming : TermRenaming sourceCtx targetCtx rho)
    (position : Fin sourceScope) :
    HEq (Term.var (context := targetCtx) (rho position))
      (Term.rename termRenaming (Term.var (context := sourceCtx) position)) := by
  change HEq (Term.var (context := targetCtx) (rho position))
    ((termRenaming position).symm ▸
      Term.var (context := targetCtx) (rho position))
  exact heq_cast_right
    (motive := fun variableType =>
      Term targetCtx variableType (RawTerm.var (rho position)))
    (termRenaming position).symm
    (Term.var (context := targetCtx) (rho position))

/-- Soundness for the surviving-variable strengthening producer. -/
theorem partialStrengthenTypedVarOfSurvives_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (sourcePosition : Fin sourceScope)
    (targetPosition : Fin targetScope)
    (survives : strengthening.back sourcePosition = some targetPosition) :
    StrengtheningSoundness
      (partialStrengthenTypedVarOfSurvives strengthening sourcePosition
        targetPosition survives) := by
  refine ⟨?_⟩
  unfold StrengtheningResult.renamedTarget
  dsimp [partialStrengthenTypedVarOfSurvives]
  have positionEq : sourcePosition = strengthening.forward targetPosition :=
    strengthening.injectsBack sourcePosition targetPosition survives
  cases positionEq
  exact rename_var_heq strengthening.toTermRenaming targetPosition

/-- Soundness for closed unit strengthening. -/
theorem partialStrengthenTypedUnit_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx) :
    StrengtheningSoundness (partialStrengthenTypedUnit strengthening) := by
  exact ⟨HEq.rfl⟩

/-- Soundness for closed boolean-true strengthening. -/
theorem partialStrengthenTypedBoolTrue_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx) :
    StrengtheningSoundness (partialStrengthenTypedBoolTrue strengthening) := by
  exact ⟨HEq.rfl⟩

/-- Soundness for closed boolean-false strengthening. -/
theorem partialStrengthenTypedBoolFalse_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx) :
    StrengtheningSoundness (partialStrengthenTypedBoolFalse strengthening) := by
  exact ⟨HEq.rfl⟩

/-- Soundness for closed natural-zero strengthening. -/
theorem partialStrengthenTypedNatZero_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx) :
    StrengtheningSoundness (partialStrengthenTypedNatZero strengthening) := by
  exact ⟨HEq.rfl⟩

/-- Soundness for closed interval-zero strengthening. -/
theorem partialStrengthenTypedInterval0_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx) :
    StrengtheningSoundness (partialStrengthenTypedInterval0 strengthening) := by
  exact ⟨HEq.rfl⟩

/-- Soundness for closed interval-one strengthening. -/
theorem partialStrengthenTypedInterval1_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx) :
    StrengtheningSoundness (partialStrengthenTypedInterval1 strengthening) := by
  exact ⟨HEq.rfl⟩

/-- Soundness for list-nil strengthening at a strengthened element type. -/
theorem partialStrengthenTypedListNilOfType_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (elementType : Ty level sourceScope)
    (targetElementType : Ty level targetScope)
    (elementTypeStrengthens :
      elementType.partialStrengthen? strengthening.back =
        some targetElementType) :
    StrengtheningSoundness
      (partialStrengthenTypedListNilOfType strengthening elementType
        targetElementType elementTypeStrengthens) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedListNilOfType,
    StrengtheningResult.renamedTarget]
  have elementTypeRenames :
      elementType = targetElementType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename elementType strengthening.forward
      strengthening.back strengthening.injectsBack targetElementType
      elementTypeStrengthens
  exact Term.listNil_HEq_congr elementTypeRenames

/-- Soundness for option-none strengthening at a strengthened element type. -/
theorem partialStrengthenTypedOptionNoneOfType_sound {mode : Mode}
    {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (elementType : Ty level sourceScope)
    (targetElementType : Ty level targetScope)
    (elementTypeStrengthens :
      elementType.partialStrengthen? strengthening.back =
        some targetElementType) :
    StrengtheningSoundness
      (partialStrengthenTypedOptionNoneOfType strengthening elementType
        targetElementType elementTypeStrengthens) := by
  refine ⟨?_⟩
  dsimp [partialStrengthenTypedOptionNoneOfType,
    StrengtheningResult.renamedTarget]
  have elementTypeRenames :
      elementType = targetElementType.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename elementType strengthening.forward
      strengthening.back strengthening.injectsBack targetElementType
      elementTypeStrengthens
  exact Term.optionNone_HEq_congr elementTypeRenames

/-- Soundness for natural-successor strengthening. -/
theorem partialStrengthenTypedNatSucc_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {predecessorRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {predecessor : Term sourceCtx Ty.nat predecessorRaw}
    {predecessorResult : StrengtheningResult strengthening predecessor}
    (predecessorSound : StrengtheningSoundness predecessorResult) :
    StrengtheningSoundness
      (partialStrengthenTypedNatSucc predecessorResult) := by
  cases predecessorResult with
  | mk targetType targetRaw targetTerm typeStrengthens rawStrengthens
      typeRenames rawRenames =>
      cases typeStrengthens
      refine ⟨?_⟩
      dsimp [partialStrengthenTypedNatSucc, StrengtheningResult.renamedTarget]
        at predecessorSound ⊢
      exact Term.natSucc_HEq_congr rawRenames
        predecessorSound.termRenames

/-- Soundness for option-some strengthening. -/
theorem partialStrengthenTypedOptionSome_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {elementType : Ty level sourceScope}
    {valueRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {valueTerm : Term sourceCtx elementType valueRaw}
    {valueResult : StrengtheningResult strengthening valueTerm}
    (valueSound : StrengtheningSoundness valueResult) :
    StrengtheningSoundness
      (partialStrengthenTypedOptionSome valueResult) := by
  cases valueResult with
  | mk targetType targetRaw targetTerm typeStrengthens rawStrengthens
      typeRenames rawRenames =>
      refine ⟨?_⟩
      dsimp [partialStrengthenTypedOptionSome,
          StrengtheningResult.renamedTarget] at valueSound ⊢
      exact Term.optionSome_HEq_congr typeRenames rawRenames
        valueSound.termRenames

/-- Soundness for natural-number eliminator strengthening. -/
theorem partialStrengthenTypedNatElim_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {motiveType : Ty level sourceScope}
    {scrutineeRaw zeroRaw succRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {scrutinee : Term sourceCtx Ty.nat scrutineeRaw}
    {zeroBranch : Term sourceCtx motiveType zeroRaw}
    {succBranch : Term sourceCtx (Ty.arrow Ty.nat motiveType) succRaw}
    {scrutineeResult : StrengtheningResult strengthening scrutinee}
    {zeroResult : StrengtheningResult strengthening zeroBranch}
    {succResult : StrengtheningResult strengthening succBranch}
    (scrutineeSound : StrengtheningSoundness scrutineeResult)
    (zeroSound : StrengtheningSoundness zeroResult)
    (succSound : StrengtheningSoundness succResult) :
    StrengtheningSoundness
      (partialStrengthenTypedNatElim scrutineeResult zeroResult
        succResult) := by
  cases scrutineeResult with
  | mk targetScrutineeType targetScrutineeRaw targetScrutineeTerm
      scrutineeTypeStrengthens scrutineeRawStrengthens
      scrutineeTypeRenames scrutineeRawRenames =>
      cases scrutineeTypeStrengthens
      cases zeroResult with
      | mk targetMotiveType targetZeroRaw targetZeroTerm
          zeroTypeStrengthens zeroRawStrengthens zeroTypeRenames
          zeroRawRenames =>
          cases succResult with
          | mk targetSuccType targetSuccRaw targetSuccTerm
              succTypeStrengthens succRawStrengthens succTypeRenames
              succRawRenames =>
              change
                Option.mapTwo
                  (Ty.nat.partialStrengthen? strengthening.back)
                  (motiveType.partialStrengthen? strengthening.back)
                  Ty.arrow = some targetSuccType at succTypeStrengthens
              rw [zeroTypeStrengthens] at succTypeStrengthens
              cases succTypeStrengthens
              refine ⟨?_⟩
              dsimp [partialStrengthenTypedNatElim,
                  StrengtheningResult.renamedTarget]
                at scrutineeSound zeroSound succSound ⊢
              exact Term.natElim_HEq_congr zeroTypeRenames
                scrutineeRawRenames zeroRawRenames succRawRenames
                scrutineeSound.termRenames zeroSound.termRenames
                succSound.termRenames

/-- Soundness for natural-number recursor strengthening. -/
theorem partialStrengthenTypedNatRec_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {motiveType : Ty level sourceScope}
    {scrutineeRaw zeroRaw succRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {scrutinee : Term sourceCtx Ty.nat scrutineeRaw}
    {zeroBranch : Term sourceCtx motiveType zeroRaw}
    {succBranch :
      Term sourceCtx (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType))
        succRaw}
    {scrutineeResult : StrengtheningResult strengthening scrutinee}
    {zeroResult : StrengtheningResult strengthening zeroBranch}
    {succResult : StrengtheningResult strengthening succBranch}
    (scrutineeSound : StrengtheningSoundness scrutineeResult)
    (zeroSound : StrengtheningSoundness zeroResult)
    (succSound : StrengtheningSoundness succResult) :
    StrengtheningSoundness
      (partialStrengthenTypedNatRec scrutineeResult zeroResult
        succResult) := by
  cases scrutineeResult with
  | mk targetScrutineeType targetScrutineeRaw targetScrutineeTerm
      scrutineeTypeStrengthens scrutineeRawStrengthens
      scrutineeTypeRenames scrutineeRawRenames =>
      cases scrutineeTypeStrengthens
      cases zeroResult with
      | mk targetMotiveType targetZeroRaw targetZeroTerm
          zeroTypeStrengthens zeroRawStrengthens zeroTypeRenames
          zeroRawRenames =>
          cases succResult with
          | mk targetSuccType targetSuccRaw targetSuccTerm
              succTypeStrengthens succRawStrengthens succTypeRenames
              succRawRenames =>
              change
                Option.mapTwo
                  (Ty.nat.partialStrengthen? strengthening.back)
                  (Option.mapTwo
                    (motiveType.partialStrengthen? strengthening.back)
                    (motiveType.partialStrengthen? strengthening.back)
                    Ty.arrow)
                  Ty.arrow = some targetSuccType at succTypeStrengthens
              rw [zeroTypeStrengthens] at succTypeStrengthens
              cases succTypeStrengthens
              refine ⟨?_⟩
              dsimp [partialStrengthenTypedNatRec,
                  StrengtheningResult.renamedTarget]
                at scrutineeSound zeroSound succSound ⊢
              exact Term.natRec_HEq_congr zeroTypeRenames
                scrutineeRawRenames zeroRawRenames succRawRenames
                scrutineeSound.termRenames zeroSound.termRenames
                succSound.termRenames

/-- Soundness for modal-introduction strengthening. -/
theorem partialStrengthenTypedModIntro_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {innerType : Ty level sourceScope}
    {innerRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {innerTerm : Term sourceCtx innerType innerRaw}
    {innerResult : StrengtheningResult strengthening innerTerm}
    (innerSound : StrengtheningSoundness innerResult) :
    StrengtheningSoundness
      (partialStrengthenTypedModIntro innerResult) := by
  cases innerResult with
  | mk targetType targetRaw targetTerm typeStrengthens rawStrengthens
      typeRenames rawRenames =>
      refine ⟨?_⟩
      dsimp [partialStrengthenTypedModIntro,
          StrengtheningResult.renamedTarget] at innerSound ⊢
      exact Term.modIntro_HEq_congr typeRenames rawRenames
        innerSound.termRenames

/-- Soundness for modal-elimination strengthening. -/
theorem partialStrengthenTypedModElim_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {innerType : Ty level sourceScope}
    {innerRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {innerTerm : Term sourceCtx innerType innerRaw}
    {innerResult : StrengtheningResult strengthening innerTerm}
    (innerSound : StrengtheningSoundness innerResult) :
    StrengtheningSoundness
      (partialStrengthenTypedModElim innerResult) := by
  cases innerResult with
  | mk targetType targetRaw targetTerm typeStrengthens rawStrengthens
      typeRenames rawRenames =>
      refine ⟨?_⟩
      dsimp [partialStrengthenTypedModElim,
          StrengtheningResult.renamedTarget] at innerSound ⊢
      exact Term.modElim_HEq_congr typeRenames rawRenames
        innerSound.termRenames

/-- Soundness for modal-subsumption strengthening. -/
theorem partialStrengthenTypedSubsume_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {innerType : Ty level sourceScope}
    {innerRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {innerTerm : Term sourceCtx innerType innerRaw}
    {innerResult : StrengtheningResult strengthening innerTerm}
    (innerSound : StrengtheningSoundness innerResult) :
    StrengtheningSoundness
      (partialStrengthenTypedSubsume innerResult) := by
  cases innerResult with
  | mk targetType targetRaw targetTerm typeStrengthens rawStrengthens
      typeRenames rawRenames =>
      refine ⟨?_⟩
      dsimp [partialStrengthenTypedSubsume,
          StrengtheningResult.renamedTarget] at innerSound ⊢
      exact Term.subsume_HEq_congr typeRenames rawRenames
        innerSound.termRenames

/-- Soundness for list-cons strengthening. -/
theorem partialStrengthenTypedListCons_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {elementType : Ty level sourceScope}
    {headRaw tailRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {headTerm : Term sourceCtx elementType headRaw}
    {tailTerm : Term sourceCtx (Ty.listType elementType) tailRaw}
    {headResult : StrengtheningResult strengthening headTerm}
    {tailResult : StrengtheningResult strengthening tailTerm}
    (headSound : StrengtheningSoundness headResult)
    (tailSound : StrengtheningSoundness tailResult) :
    StrengtheningSoundness
      (partialStrengthenTypedListCons headResult tailResult) := by
  cases headResult with
  | mk targetElementType targetHeadRaw targetHeadTerm headTypeStrengthens
      headRawStrengthens headTypeRenames headRawRenames =>
      cases tailResult with
      | mk targetTailType targetTailRaw targetTailTerm tailTypeStrengthens
          tailRawStrengthens tailTypeRenames tailRawRenames =>
          change
            (match elementType.partialStrengthen? strengthening.back with
            | some strengthenedElement => some (Ty.listType strengthenedElement)
            | none => none) = some targetTailType at tailTypeStrengthens
          rw [headTypeStrengthens] at tailTypeStrengthens
          cases tailTypeStrengthens
          refine ⟨?_⟩
          dsimp [partialStrengthenTypedListCons,
              StrengtheningResult.renamedTarget] at headSound tailSound ⊢
          exact Term.listCons_HEq_congr headTypeRenames headRawRenames
            tailRawRenames headSound.termRenames tailSound.termRenames

/-- Soundness for interval-negation strengthening. -/
theorem partialStrengthenTypedIntervalOpp_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {innerRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {innerValue : Term sourceCtx Ty.interval innerRaw}
    {innerResult : StrengtheningResult strengthening innerValue}
    (innerSound : StrengtheningSoundness innerResult) :
    StrengtheningSoundness
      (partialStrengthenTypedIntervalOpp innerResult) := by
  cases innerResult with
  | mk targetType targetRaw targetTerm typeStrengthens rawStrengthens
      typeRenames rawRenames =>
      cases typeStrengthens
      refine ⟨?_⟩
      dsimp [partialStrengthenTypedIntervalOpp, StrengtheningResult.renamedTarget]
        at innerSound ⊢
      exact Term.intervalOpp_HEq_congr rawRenames
        innerSound.termRenames

/-- Soundness for interval-meet strengthening. -/
theorem partialStrengthenTypedIntervalMeet_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {leftRaw rightRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {leftValue : Term sourceCtx Ty.interval leftRaw}
    {rightValue : Term sourceCtx Ty.interval rightRaw}
    {leftResult : StrengtheningResult strengthening leftValue}
    {rightResult : StrengtheningResult strengthening rightValue}
    (leftSound : StrengtheningSoundness leftResult)
    (rightSound : StrengtheningSoundness rightResult) :
    StrengtheningSoundness
      (partialStrengthenTypedIntervalMeet leftResult rightResult) := by
  cases leftResult with
  | mk leftTargetType leftTargetRaw leftTargetTerm leftTypeStrengthens
      leftRawStrengthens leftTypeRenames leftRawRenames =>
      cases rightResult with
      | mk rightTargetType rightTargetRaw rightTargetTerm rightTypeStrengthens
          rightRawStrengthens rightTypeRenames rightRawRenames =>
          cases leftTypeStrengthens
          cases rightTypeStrengthens
          refine ⟨?_⟩
          dsimp [partialStrengthenTypedIntervalMeet,
              StrengtheningResult.renamedTarget] at leftSound rightSound ⊢
          exact Term.intervalMeet_HEq_congr leftRawRenames rightRawRenames
            leftSound.termRenames rightSound.termRenames

/-- Soundness for interval-join strengthening. -/
theorem partialStrengthenTypedIntervalJoin_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {leftRaw rightRaw : RawTerm sourceScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {leftValue : Term sourceCtx Ty.interval leftRaw}
    {rightValue : Term sourceCtx Ty.interval rightRaw}
    {leftResult : StrengtheningResult strengthening leftValue}
    {rightResult : StrengtheningResult strengthening rightValue}
    (leftSound : StrengtheningSoundness leftResult)
    (rightSound : StrengtheningSoundness rightResult) :
    StrengtheningSoundness
      (partialStrengthenTypedIntervalJoin leftResult rightResult) := by
  cases leftResult with
  | mk leftTargetType leftTargetRaw leftTargetTerm leftTypeStrengthens
      leftRawStrengthens leftTypeRenames leftRawRenames =>
      cases rightResult with
      | mk rightTargetType rightTargetRaw rightTargetTerm rightTypeStrengthens
          rightRawStrengthens rightTypeRenames rightRawRenames =>
          cases leftTypeStrengthens
          cases rightTypeStrengthens
          refine ⟨?_⟩
          dsimp [partialStrengthenTypedIntervalJoin,
              StrengtheningResult.renamedTarget] at leftSound rightSound ⊢
          exact Term.intervalJoin_HEq_congr leftRawRenames rightRawRenames
            leftSound.termRenames rightSound.termRenames

end Term

end LeanFX2
