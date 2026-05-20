import LeanFX2.Term.PartialStrengthen.Constructors.Cubical

/-! # Term/PartialStrengthen/Constructors/Effects

Typed partial-strengthening producers for effect-performance terms.
-/

namespace LeanFX2

namespace Term

/-- Pre-witnessed effect-performance strengthening.

Replaces the wrapper's nested `cases operationTagResult` and
`cases argumentsResult` plus their `expectedOperationTagTypeStrengthens`
rewrites with explicit strengthening witnesses for both raw operands.
The `targetCanPerform` evidence is built structurally via
`CanPerform.map`-style dispatch on `canPerformOperation`, and the
target operation-signature carries the same `effectLabel` so its
`map`-renamed form composes definitionally with the source signature
after carrier renames are recovered. -/
def partialStrengthenTypedEffectPerformOfSuccess
    {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    {effectTag : RawTerm sourceScope}
    {targetEffectTag : RawTerm targetScope}
    (effectRow : Effects.EffectRow)
    (operationSignature : Effects.OperationSignature (Ty level sourceScope))
    {targetArgumentCarrier targetResultCarrier : Ty level targetScope}
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
    (targetOperationTag :
      Term targetCtx
        (Ty.effect targetArgumentCarrier targetEffectTag)
        targetOperationRaw)
    (targetArguments :
      Term targetCtx targetArgumentCarrier targetArgumentsRaw)
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
    (_effectTagRenames :
      effectTag = targetEffectTag.rename strengthening.forward)
    (operationRawRenames :
      operationRaw = targetOperationRaw.rename strengthening.forward)
    (argumentsRawRenames :
      argumentsRaw = targetArgumentsRaw.rename strengthening.forward) :
    StrengtheningResult strengthening
      (Term.effectPerform (context := sourceCtx) effectTag effectRow
        operationSignature canPerformOperation operationTag arguments) := by
  let targetOperationSignature : Effects.OperationSignature
      (Ty level targetScope) :=
    { effectLabel := operationSignature.effectLabel
      argumentCarrier := targetArgumentCarrier
      resultCarrier := targetResultCarrier }
  have targetCanPerform :
      Effects.CanPerform effectRow targetOperationSignature := by
    cases canPerformOperation with
    | direct rowMember =>
        exact Effects.CanPerform.direct rowMember
    | readViaWrite argumentCarrier resultCarrier rowMember =>
        exact Effects.CanPerform.readViaWrite targetArgumentCarrier
          targetResultCarrier rowMember
  exact {
    targetType := Ty.effect targetResultCarrier targetEffectTag
    targetRaw :=
      RawTerm.effectPerform targetOperationRaw targetArgumentsRaw
    targetTerm :=
      Term.effectPerform (context := targetCtx) targetEffectTag
        effectRow targetOperationSignature targetCanPerform
        targetOperationTag targetArguments
    typeStrengthens := by
      change
        Option.mapTwo
          (operationSignature.resultCarrier.partialStrengthen?
            strengthening.back)
          (effectTag.partialStrengthen? strengthening.back)
          Ty.effect =
            some (Ty.effect targetResultCarrier targetEffectTag)
      rw [resultCarrierStrengthens, effectTagStrengthens]
      rfl
    rawStrengthens := by
      change
        Option.mapTwo
          (operationRaw.partialStrengthen? strengthening.back)
          (argumentsRaw.partialStrengthen? strengthening.back)
          RawTerm.effectPerform =
            some (RawTerm.effectPerform targetOperationRaw
              targetArgumentsRaw)
      rw [operationRawStrengthens, argumentsRawStrengthens]
      rfl
    typeRenames :=
      Ty.partialStrengthen?_imp_rename
        (Ty.effect operationSignature.resultCarrier effectTag)
        strengthening.forward strengthening.back
        strengthening.injectsBack
        (Ty.effect targetResultCarrier targetEffectTag)
        (by
          change
            Option.mapTwo
              (operationSignature.resultCarrier.partialStrengthen?
                strengthening.back)
              (effectTag.partialStrengthen? strengthening.back)
              Ty.effect =
                some (Ty.effect targetResultCarrier targetEffectTag)
          rw [resultCarrierStrengthens, effectTagStrengthens]
          rfl)
    rawRenames := by
      cases operationRawRenames
      cases argumentsRawRenames
      rfl
  }

/-- Effect performance strengthens by strengthening the operation tag,
argument term, effect tag, and the operation signature's argument/result
carriers.  `CanPerform` evidence is rebuilt structurally because it
depends only on the effect label and row membership, not on carrier
internals. -/
def partialStrengthenTypedEffectPerform {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    {strengthening : ContextStrengthening sourceCtx targetCtx}
    (effectTag : RawTerm sourceScope)
    (targetEffectTag : RawTerm targetScope)
    (effectRow : Effects.EffectRow)
    (operationSignature : Effects.OperationSignature (Ty level sourceScope))
    (targetArgumentCarrier targetResultCarrier : Ty level targetScope)
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
    (operationTagResult : StrengtheningResult strengthening operationTag)
    (argumentsResult : StrengtheningResult strengthening arguments) :
    StrengtheningResult strengthening
      (Term.effectPerform (context := sourceCtx) effectTag effectRow
        operationSignature canPerformOperation operationTag arguments) := by
  let targetOperationSignature : Effects.OperationSignature
      (Ty level targetScope) :=
    { effectLabel := operationSignature.effectLabel
      argumentCarrier := targetArgumentCarrier
      resultCarrier := targetResultCarrier }
  have targetCanPerform :
      Effects.CanPerform effectRow targetOperationSignature := by
    cases canPerformOperation with
    | direct rowMember =>
        exact Effects.CanPerform.direct rowMember
    | readViaWrite argumentCarrier resultCarrier rowMember =>
        exact Effects.CanPerform.readViaWrite targetArgumentCarrier
          targetResultCarrier rowMember
  cases operationTagResult with
  | mk targetOperationTagType targetOperationRaw targetOperationTag
      operationTagTypeStrengthens operationRawStrengthens
      operationTagTypeRenames operationRawRenames =>
      have expectedOperationTagTypeStrengthens :
          (Ty.effect operationSignature.argumentCarrier effectTag).partialStrengthen?
              strengthening.back =
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
      rw [expectedOperationTagTypeStrengthens] at operationTagTypeStrengthens
      cases operationTagTypeStrengthens
      cases argumentsResult with
      | mk targetArgumentsType targetArgumentsRaw targetArguments
          argumentsTypeStrengthens argumentsRawStrengthens
          argumentsTypeRenames argumentsRawRenames =>
          rw [argumentCarrierStrengthens] at argumentsTypeStrengthens
          cases argumentsTypeStrengthens
          exact {
            targetType := Ty.effect targetResultCarrier targetEffectTag
            targetRaw :=
              RawTerm.effectPerform targetOperationRaw targetArgumentsRaw
            targetTerm :=
              Term.effectPerform (context := targetCtx) targetEffectTag
                effectRow targetOperationSignature targetCanPerform
                targetOperationTag targetArguments
            typeStrengthens := by
              change
                Option.mapTwo
                  (operationSignature.resultCarrier.partialStrengthen?
                    strengthening.back)
                  (effectTag.partialStrengthen? strengthening.back)
                  Ty.effect =
                    some (Ty.effect targetResultCarrier targetEffectTag)
              rw [resultCarrierStrengthens, effectTagStrengthens]
              rfl
            rawStrengthens := by
              change
                Option.mapTwo
                  (operationRaw.partialStrengthen? strengthening.back)
                  (argumentsRaw.partialStrengthen? strengthening.back)
                  RawTerm.effectPerform =
                    some (RawTerm.effectPerform targetOperationRaw
                      targetArgumentsRaw)
              rw [operationRawStrengthens, argumentsRawStrengthens]
              rfl
            typeRenames := by
              exact
                Ty.partialStrengthen?_imp_rename
                  (Ty.effect operationSignature.resultCarrier effectTag)
                  strengthening.forward strengthening.back
                  strengthening.injectsBack
                  (Ty.effect targetResultCarrier targetEffectTag)
                  (by
                    change
                      Option.mapTwo
                        (operationSignature.resultCarrier.partialStrengthen?
                          strengthening.back)
                        (effectTag.partialStrengthen? strengthening.back)
                        Ty.effect =
                          some (Ty.effect targetResultCarrier
                            targetEffectTag)
                    rw [resultCarrierStrengthens, effectTagStrengthens]
                    rfl)
            rawRenames := by
              cases operationRawRenames
              cases argumentsRawRenames
              rfl
          }

end Term

end LeanFX2
