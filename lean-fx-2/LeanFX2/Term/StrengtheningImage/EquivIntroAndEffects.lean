import LeanFX2.Term.StrengtheningImage.Core

/-! # Term/StrengtheningImage/EquivIntroAndEffects

Soundness lemmas for heterogeneous equivalence introduction and effect performance producers.
-/

namespace LeanFX2

namespace Term

/-- Soundness of `partialStrengthenTypedEquivIntroHetOfSuccess`: the
result's renamed target term is heterogeneously equal to the original
typed heterogeneous-equivalence introduction.  Note: the leftInv and
rightInv raw rename equations are taken as direct inputs since the
typed proof children carry independent raw forms not derivable from
`forwardRaw` / `backwardRaw` alone. -/
theorem partialStrengthenTypedEquivIntroHetOfSuccess_sound
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {carrierA carrierB : Ty level sourceScope}
    {targetCarrierA targetCarrierB : Ty level targetScope}
    {forwardRaw backwardRaw leftInvRaw rightInvRaw : RawTerm sourceScope}
    {targetForwardRaw targetBackwardRaw : RawTerm targetScope}
    {targetLeftInvRaw targetRightInvRaw : RawTerm targetScope}
    {forward :
      Term sourceCtx (Ty.arrow carrierA carrierB) forwardRaw}
    {backward :
      Term sourceCtx (Ty.arrow carrierB carrierA) backwardRaw}
    {leftInv :
      Term sourceCtx
        (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
        leftInvRaw}
    {rightInv :
      Term sourceCtx
        (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
        rightInvRaw}
    {targetForward :
      Term targetCtx (Ty.arrow targetCarrierA targetCarrierB)
        targetForwardRaw}
    {targetBackward :
      Term targetCtx (Ty.arrow targetCarrierB targetCarrierA)
        targetBackwardRaw}
    {targetLeftInv :
      Term targetCtx
        (equivIntroHetLeftInverseType targetCarrierA targetForwardRaw
          targetBackwardRaw)
        targetLeftInvRaw}
    {targetRightInv :
      Term targetCtx
        (equivIntroHetRightInverseType targetCarrierB targetForwardRaw
          targetBackwardRaw)
        targetRightInvRaw}
    (carrierASuccess :
      carrierA.partialStrengthen? strengthening.back =
        some targetCarrierA)
    (carrierBSuccess :
      carrierB.partialStrengthen? strengthening.back =
        some targetCarrierB)
    (forwardRawStrengthens :
      forwardRaw.partialStrengthen? strengthening.back =
        some targetForwardRaw)
    (backwardRawStrengthens :
      backwardRaw.partialStrengthen? strengthening.back =
        some targetBackwardRaw)
    (forwardRawRenames :
      forwardRaw = targetForwardRaw.rename strengthening.forward)
    (backwardRawRenames :
      backwardRaw = targetBackwardRaw.rename strengthening.forward)
    (leftInvRawRenames :
      leftInvRaw = targetLeftInvRaw.rename strengthening.forward)
    (rightInvRawRenames :
      rightInvRaw = targetRightInvRaw.rename strengthening.forward)
    (forwardSound :
      HEq forward
        (Term.rename strengthening.toTermRenaming targetForward))
    (backwardSound :
      HEq backward
        (Term.rename strengthening.toTermRenaming targetBackward))
    (leftInvSound :
      HEq leftInv
        (Term.rename strengthening.toTermRenaming targetLeftInv))
    (rightInvSound :
      HEq rightInv
        (Term.rename strengthening.toTermRenaming targetRightInv)) :
    StrengtheningSoundness
      (partialStrengthenTypedEquivIntroHetOfSuccess
        (forward := forward) (backward := backward)
        (leftInv := leftInv) (rightInv := rightInv)
        targetForward targetBackward targetLeftInv targetRightInv
        carrierASuccess carrierBSuccess forwardRawStrengthens
        backwardRawStrengthens forwardRawRenames backwardRawRenames) := by
  refine ⟨?_⟩
  unfold StrengtheningResult.renamedTarget
  dsimp [partialStrengthenTypedEquivIntroHetOfSuccess]
  have carrierARenames :
      carrierA = targetCarrierA.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename carrierA
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCarrierA carrierASuccess
  have carrierBRenames :
      carrierB = targetCarrierB.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename carrierB
      strengthening.forward strengthening.back strengthening.injectsBack
      targetCarrierB carrierBSuccess
  have castedLeftInvSound :
      HEq leftInv
        (equivIntroHetLeftInverseType_rename strengthening.forward
            targetCarrierA targetForwardRaw targetBackwardRaw ▸
          Term.rename strengthening.toTermRenaming targetLeftInv) :=
    HEq.trans leftInvSound
      (Term.type_eq_cast_heq
        (equivIntroHetLeftInverseType_rename strengthening.forward
          targetCarrierA targetForwardRaw targetBackwardRaw)
        (Term.rename strengthening.toTermRenaming targetLeftInv)).symm
  have castedRightInvSound :
      HEq rightInv
        (equivIntroHetRightInverseType_rename strengthening.forward
            targetCarrierB targetForwardRaw targetBackwardRaw ▸
          Term.rename strengthening.toTermRenaming targetRightInv) :=
    HEq.trans rightInvSound
      (Term.type_eq_cast_heq
        (equivIntroHetRightInverseType_rename strengthening.forward
          targetCarrierB targetForwardRaw targetBackwardRaw)
        (Term.rename strengthening.toTermRenaming targetRightInv)).symm
  exact Term.equivIntroHet_HEq_congr carrierARenames carrierBRenames
    forwardRawRenames backwardRawRenames leftInvRawRenames
    rightInvRawRenames forwardSound backwardSound castedLeftInvSound
    castedRightInvSound

/-- Soundness of `partialStrengthenTypedEffectPerformOfSuccess`: the
result's renamed target term is heterogeneously equal to the original
typed effect-performance application.  The proof leans on
proof-irrelevance for `Effects.CanPerform` (a `Prop`-valued inductive)
to align the source's `canPerformOperation` with the renamed target
`CanPerform.map ... targetCanPerform` after operation-signature
carriers are identified via `Ty.partialStrengthen?_imp_rename`. -/
theorem partialStrengthenTypedEffectPerformOfSuccess_sound
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {effectTag : RawTerm sourceScope}
    {targetEffectTag : RawTerm targetScope}
    (effectRow : Effects.EffectRow)
    (operationSignature :
      Effects.OperationSignature (Ty level sourceScope))
    {targetArgumentCarrier targetResultCarrier :
      Ty level targetScope}
    (canPerformOperation :
      Effects.CanPerform effectRow operationSignature)
    {operationRaw argumentsRaw : RawTerm sourceScope}
    {targetOperationRaw targetArgumentsRaw : RawTerm targetScope}
    {operationTag :
      Term sourceCtx
        (Ty.effect operationSignature.argumentCarrier effectTag)
        operationRaw}
    {arguments :
      Term sourceCtx operationSignature.argumentCarrier argumentsRaw}
    {targetOperationTag :
      Term targetCtx
        (Ty.effect targetArgumentCarrier targetEffectTag)
        targetOperationRaw}
    {targetArguments :
      Term targetCtx targetArgumentCarrier targetArgumentsRaw}
    (effectTagStrengthens :
      effectTag.partialStrengthen? strengthening.back =
        some targetEffectTag)
    (argumentCarrierStrengthens :
      operationSignature.argumentCarrier.partialStrengthen?
          strengthening.back =
        some targetArgumentCarrier)
    (resultCarrierStrengthens :
      operationSignature.resultCarrier.partialStrengthen?
          strengthening.back =
        some targetResultCarrier)
    (operationRawStrengthens :
      operationRaw.partialStrengthen? strengthening.back =
        some targetOperationRaw)
    (argumentsRawStrengthens :
      argumentsRaw.partialStrengthen? strengthening.back =
        some targetArgumentsRaw)
    (effectTagRenames :
      effectTag = targetEffectTag.rename strengthening.forward)
    (operationRawRenames :
      operationRaw = targetOperationRaw.rename strengthening.forward)
    (argumentsRawRenames :
      argumentsRaw = targetArgumentsRaw.rename strengthening.forward)
    (operationTagSound :
      HEq operationTag
        (Term.rename strengthening.toTermRenaming targetOperationTag))
    (argumentsSound :
      HEq arguments
        (Term.rename strengthening.toTermRenaming targetArguments)) :
    StrengtheningSoundness
      (partialStrengthenTypedEffectPerformOfSuccess
        (effectTag := effectTag) (targetEffectTag := targetEffectTag)
        (operationTag := operationTag) (arguments := arguments)
        effectRow operationSignature
        (targetArgumentCarrier := targetArgumentCarrier)
        (targetResultCarrier := targetResultCarrier)
        canPerformOperation targetOperationTag targetArguments
        effectTagStrengthens argumentCarrierStrengthens
        resultCarrierStrengthens operationRawStrengthens
        argumentsRawStrengthens effectTagRenames operationRawRenames
        argumentsRawRenames) := by
  refine ⟨?_⟩
  have argumentCarrierRenames :
      operationSignature.argumentCarrier =
        targetArgumentCarrier.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename operationSignature.argumentCarrier
      strengthening.forward strengthening.back strengthening.injectsBack
      targetArgumentCarrier argumentCarrierStrengthens
  have resultCarrierRenames :
      operationSignature.resultCarrier =
        targetResultCarrier.rename strengthening.forward :=
    Ty.partialStrengthen?_imp_rename operationSignature.resultCarrier
      strengthening.forward strengthening.back strengthening.injectsBack
      targetResultCarrier resultCarrierStrengthens
  obtain ⟨opLabel, opArgCarrier, opResCarrier⟩ := operationSignature
  simp only at argumentCarrierRenames resultCarrierRenames
  subst argumentCarrierRenames
  subst resultCarrierRenames
  unfold StrengtheningResult.renamedTarget
  dsimp [partialStrengthenTypedEffectPerformOfSuccess]
  cases canPerformOperation with
  | direct rowMember =>
      exact Term.effectPerform_HEq_congr effectRow
        { effectLabel := opLabel
          argumentCarrier :=
            targetArgumentCarrier.rename strengthening.forward
          resultCarrier :=
            targetResultCarrier.rename strengthening.forward }
        (Effects.CanPerform.direct rowMember)
        effectTagRenames operationRawRenames argumentsRawRenames
        operationTagSound argumentsSound
  | readViaWrite _ _ rowMember =>
      exact Term.effectPerform_HEq_congr effectRow
        { effectLabel := Effects.EffectLabel.read
          argumentCarrier :=
            targetArgumentCarrier.rename strengthening.forward
          resultCarrier :=
            targetResultCarrier.rename strengthening.forward }
        (Effects.CanPerform.readViaWrite
          (targetArgumentCarrier.rename strengthening.forward)
          (targetResultCarrier.rename strengthening.forward)
          rowMember)
        effectTagRenames operationRawRenames argumentsRawRenames
        operationTagSound argumentsSound

/-- Soundness for the typed effect-performance wrapper.

Mirrors `partialStrengthenTypedEffectPerform`'s structure:
destructures both child `StrengtheningResult` records, aligns the
`Ty.effect`-shaped operation-tag type and the operation-signature
argument-carrier for the arguments-term type, then delegates the
final `HEq` reconstruction to
`partialStrengthenTypedEffectPerformOfSuccess_sound`.  The wrapper
takes `effectTagStrengthens` + `argumentCarrierStrengthens` +
`resultCarrierStrengthens` as explicit parameters; the soundness
theorem threads them straight through. -/
theorem partialStrengthenTypedEffectPerform_sound
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (effectTag : RawTerm sourceScope)
    (targetEffectTag : RawTerm targetScope)
    (effectRow : Effects.EffectRow)
    (operationSignature :
      Effects.OperationSignature (Ty level sourceScope))
    (targetArgumentCarrier targetResultCarrier :
      Ty level targetScope)
    (canPerformOperation :
      Effects.CanPerform effectRow operationSignature)
    {operationRaw argumentsRaw : RawTerm sourceScope}
    {operationTag :
      Term sourceCtx
        (Ty.effect operationSignature.argumentCarrier effectTag)
        operationRaw}
    {arguments :
      Term sourceCtx operationSignature.argumentCarrier argumentsRaw}
    (effectTagStrengthens :
      effectTag.partialStrengthen? strengthening.back =
        some targetEffectTag)
    (argumentCarrierStrengthens :
      operationSignature.argumentCarrier.partialStrengthen?
          strengthening.back =
        some targetArgumentCarrier)
    (resultCarrierStrengthens :
      operationSignature.resultCarrier.partialStrengthen?
          strengthening.back =
        some targetResultCarrier)
    {operationTagResult : StrengtheningResult strengthening operationTag}
    {argumentsResult : StrengtheningResult strengthening arguments}
    (operationTagSound : StrengtheningSoundness operationTagResult)
    (argumentsSound : StrengtheningSoundness argumentsResult)
    (effectTagRenames :
      effectTag = targetEffectTag.rename strengthening.forward) :
    StrengtheningSoundness
      (partialStrengthenTypedEffectPerform effectTag targetEffectTag
        effectRow operationSignature targetArgumentCarrier
        targetResultCarrier canPerformOperation effectTagStrengthens
        argumentCarrierStrengthens resultCarrierStrengthens
        operationTagResult argumentsResult) := by
  cases operationTagResult with
  | mk targetOperationTagType targetOperationRaw targetOperationTag
      operationTagTypeStrengthens operationRawStrengthens
      operationTagTypeRenames operationRawRenames =>
      have expectedOperationTagTypeStrengthens :
          (Ty.effect operationSignature.argumentCarrier
              effectTag).partialStrengthen? strengthening.back =
            some (Ty.effect targetArgumentCarrier targetEffectTag) := by
        change
          Option.mapTwo
            (operationSignature.argumentCarrier.partialStrengthen?
              strengthening.back)
            (effectTag.partialStrengthen? strengthening.back)
            Ty.effect =
              some (Ty.effect targetArgumentCarrier targetEffectTag)
        rw [argumentCarrierStrengthens, effectTagStrengthens]
        rfl
      rw [expectedOperationTagTypeStrengthens]
        at operationTagTypeStrengthens
      cases operationTagTypeStrengthens
      cases argumentsResult with
      | mk targetArgumentsType targetArgumentsRaw targetArguments
          argumentsTypeStrengthens argumentsRawStrengthens
          argumentsTypeRenames argumentsRawRenames =>
          rw [argumentCarrierStrengthens] at argumentsTypeStrengthens
          cases argumentsTypeStrengthens
          exact partialStrengthenTypedEffectPerformOfSuccess_sound
            effectRow operationSignature canPerformOperation
            (targetOperationTag := targetOperationTag)
            (targetArguments := targetArguments)
            effectTagStrengthens argumentCarrierStrengthens
            resultCarrierStrengthens operationRawStrengthens
            argumentsRawStrengthens effectTagRenames
            operationRawRenames argumentsRawRenames
            operationTagSound.termRenames
            argumentsSound.termRenames

end Term

end LeanFX2
