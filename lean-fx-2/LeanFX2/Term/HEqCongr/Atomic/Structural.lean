import LeanFX2.Term

/-! # Term/HEqCongr/Atomic/Structural

Record, refinement, codata, session, effect, and structural HEq congruences. -/

namespace LeanFX2

/-- HEq congruence for single-field record introduction. -/
theorem Term.recordIntro_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {singleFieldType1 singleFieldType2 : Ty level scope}
    {firstRaw1 firstRaw2 : RawTerm scope}
    (singleFieldTypeEq : singleFieldType1 = singleFieldType2)
    (firstRawEq : firstRaw1 = firstRaw2)
    {firstField1 : Term context singleFieldType1 firstRaw1}
    {firstField2 : Term context singleFieldType2 firstRaw2}
    (firstFieldHEq : HEq firstField1 firstField2) :
    HEq (Term.recordIntro firstField1) (Term.recordIntro firstField2) := by
  subst singleFieldTypeEq
  subst firstRawEq
  cases firstFieldHEq
  rfl

/-- HEq congruence for single-field record projection. -/
theorem Term.recordProj_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {singleFieldType1 singleFieldType2 : Ty level scope}
    {recordRaw1 recordRaw2 : RawTerm scope}
    (singleFieldTypeEq : singleFieldType1 = singleFieldType2)
    (recordRawEq : recordRaw1 = recordRaw2)
    {recordValue1 : Term context (Ty.record singleFieldType1) recordRaw1}
    {recordValue2 : Term context (Ty.record singleFieldType2) recordRaw2}
    (recordValueHEq : HEq recordValue1 recordValue2) :
    HEq (Term.recordProj recordValue1) (Term.recordProj recordValue2) := by
  subst singleFieldTypeEq
  subst recordRawEq
  cases recordValueHEq
  rfl

/-- HEq congruence for refinement elimination. -/
theorem Term.refineElim_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {baseType1 baseType2 : Ty level scope}
    {predicate1 predicate2 : RawTerm (scope + 1)}
    {refinedRaw1 refinedRaw2 : RawTerm scope}
    (baseTypeEq : baseType1 = baseType2)
    (predicateEq : predicate1 = predicate2)
    (refinedRawEq : refinedRaw1 = refinedRaw2)
    {refinedValue1 : Term context (Ty.refine baseType1 predicate1) refinedRaw1}
    {refinedValue2 : Term context (Ty.refine baseType2 predicate2) refinedRaw2}
    (refinedValueHEq : HEq refinedValue1 refinedValue2) :
    HEq (Term.refineElim refinedValue1) (Term.refineElim refinedValue2) := by
  subst baseTypeEq
  subst predicateEq
  subst refinedRawEq
  cases refinedValueHEq
  rfl

/-- HEq congruence for codata destruction. -/
theorem Term.codataDest_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {stateType1 stateType2 outputType1 outputType2 : Ty level scope}
    {codataRaw1 codataRaw2 : RawTerm scope}
    (stateTypeEq : stateType1 = stateType2)
    (outputTypeEq : outputType1 = outputType2)
    (codataRawEq : codataRaw1 = codataRaw2)
    {codataValue1 : Term context (Ty.codata stateType1 outputType1) codataRaw1}
    {codataValue2 : Term context (Ty.codata stateType2 outputType2) codataRaw2}
    (codataValueHEq : HEq codataValue1 codataValue2) :
    HEq (Term.codataDest codataValue1) (Term.codataDest codataValue2) := by
  subst stateTypeEq
  subst outputTypeEq
  subst codataRawEq
  cases codataValueHEq
  rfl

/-- HEq congruence for session receive. -/
theorem Term.sessionRecv_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {protocolStep1 protocolStep2 channelRaw1 channelRaw2 : RawTerm scope}
    (protocolStepEq : protocolStep1 = protocolStep2)
    (channelRawEq : channelRaw1 = channelRaw2)
    {channel1 : Term context (Ty.session protocolStep1) channelRaw1}
    {channel2 : Term context (Ty.session protocolStep2) channelRaw2}
    (channelHEq : HEq channel1 channel2) :
    HEq (Term.sessionRecv channel1) (Term.sessionRecv channel2) := by
  subst protocolStepEq
  subst channelRawEq
  cases channelHEq
  rfl

/-- HEq congruence for equivalence application. -/
theorem Term.equivApp_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {carrierA1 carrierA2 carrierB1 carrierB2 : Ty level scope}
    {equivRaw1 equivRaw2 argumentRaw1 argumentRaw2 : RawTerm scope}
    (carrierAEq : carrierA1 = carrierA2)
    (carrierBEq : carrierB1 = carrierB2)
    (equivRawEq : equivRaw1 = equivRaw2)
    (argumentRawEq : argumentRaw1 = argumentRaw2)
    {equivTerm1 : Term context (Ty.equiv carrierA1 carrierB1) equivRaw1}
    {equivTerm2 : Term context (Ty.equiv carrierA2 carrierB2) equivRaw2}
    (equivHEq : HEq equivTerm1 equivTerm2)
    {argumentTerm1 : Term context carrierA1 argumentRaw1}
    {argumentTerm2 : Term context carrierA2 argumentRaw2}
    (argumentHEq : HEq argumentTerm1 argumentTerm2) :
    HEq (Term.equivApp equivTerm1 argumentTerm1)
      (Term.equivApp equivTerm2 argumentTerm2) := by
  subst carrierAEq
  subst carrierBEq
  subst equivRawEq
  subst argumentRawEq
  cases equivHEq
  cases argumentHEq
  rfl

/-- HEq congruence for refinement introduction. -/
theorem Term.refineIntro_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {baseType1 baseType2 : Ty level scope}
    {predicate1 predicate2 : RawTerm (scope + 1)}
    {valueRaw1 valueRaw2 proofRaw1 proofRaw2 : RawTerm scope}
    (baseTypeEq : baseType1 = baseType2)
    (predicateEq : predicate1 = predicate2)
    (valueRawEq : valueRaw1 = valueRaw2)
    (proofRawEq : proofRaw1 = proofRaw2)
    {baseValue1 : Term context baseType1 valueRaw1}
    {baseValue2 : Term context baseType2 valueRaw2}
    (baseValueHEq : HEq baseValue1 baseValue2)
    {predicateProof1 : Term context Ty.unit proofRaw1}
    {predicateProof2 : Term context Ty.unit proofRaw2}
    (predicateProofHEq : HEq predicateProof1 predicateProof2) :
    HEq (Term.refineIntro predicate1 baseValue1 predicateProof1)
      (Term.refineIntro predicate2 baseValue2 predicateProof2) := by
  subst baseTypeEq
  subst predicateEq
  subst valueRawEq
  subst proofRawEq
  cases baseValueHEq
  cases predicateProofHEq
  rfl

/-- HEq congruence for codata unfold. -/
theorem Term.codataUnfold_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {stateType1 stateType2 outputType1 outputType2 : Ty level scope}
    {stateRaw1 stateRaw2 transitionRaw1 transitionRaw2 : RawTerm scope}
    (stateTypeEq : stateType1 = stateType2)
    (outputTypeEq : outputType1 = outputType2)
    (stateRawEq : stateRaw1 = stateRaw2)
    (transitionRawEq : transitionRaw1 = transitionRaw2)
    {initialState1 : Term context stateType1 stateRaw1}
    {initialState2 : Term context stateType2 stateRaw2}
    (initialStateHEq : HEq initialState1 initialState2)
    {transition1 : Term context (Ty.arrow stateType1 outputType1) transitionRaw1}
    {transition2 : Term context (Ty.arrow stateType2 outputType2) transitionRaw2}
    (transitionHEq : HEq transition1 transition2) :
    HEq (Term.codataUnfold initialState1 transition1)
      (Term.codataUnfold initialState2 transition2) := by
  subst stateTypeEq
  subst outputTypeEq
  subst stateRawEq
  subst transitionRawEq
  cases initialStateHEq
  cases transitionHEq
  rfl

/-- HEq congruence for session send. -/
theorem Term.sessionSend_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {protocolStep1 protocolStep2 : RawTerm scope}
    {payloadType1 payloadType2 : Ty level scope}
    {channelRaw1 channelRaw2 payloadRaw1 payloadRaw2 : RawTerm scope}
    (protocolStepEq : protocolStep1 = protocolStep2)
    (payloadTypeEq : payloadType1 = payloadType2)
    (channelRawEq : channelRaw1 = channelRaw2)
    (payloadRawEq : payloadRaw1 = payloadRaw2)
    {channel1 : Term context (Ty.session protocolStep1) channelRaw1}
    {channel2 : Term context (Ty.session protocolStep2) channelRaw2}
    (channelHEq : HEq channel1 channel2)
    {payload1 : Term context payloadType1 payloadRaw1}
    {payload2 : Term context payloadType2 payloadRaw2}
    (payloadHEq : HEq payload1 payload2) :
    HEq (Term.sessionSend protocolStep1 channel1 payload1)
      (Term.sessionSend protocolStep2 channel2 payload2) := by
  subst protocolStepEq
  subst payloadTypeEq
  subst channelRawEq
  subst payloadRawEq
  cases channelHEq
  cases payloadHEq
  rfl

/-- HEq congruence for effect performance with shared row evidence. -/
theorem Term.effectPerform_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {effectTag1 effectTag2 : RawTerm scope}
    (effectRow : Effects.EffectRow)
    (operationSignature : Effects.OperationSignature (Ty level scope))
    (canPerformOperation :
      Effects.CanPerform effectRow operationSignature)
    {operationRaw1 operationRaw2 argumentsRaw1 argumentsRaw2 : RawTerm scope}
    (effectTagEq : effectTag1 = effectTag2)
    (operationRawEq : operationRaw1 = operationRaw2)
    (argumentsRawEq : argumentsRaw1 = argumentsRaw2)
    {operationTag1 :
      Term context
        (Ty.effect operationSignature.argumentCarrier effectTag1)
        operationRaw1}
    {operationTag2 :
      Term context
        (Ty.effect operationSignature.argumentCarrier effectTag2)
        operationRaw2}
    (operationTagHEq : HEq operationTag1 operationTag2)
    {arguments1 :
      Term context operationSignature.argumentCarrier argumentsRaw1}
    {arguments2 :
      Term context operationSignature.argumentCarrier argumentsRaw2}
    (argumentsHEq : HEq arguments1 arguments2) :
    HEq
      (Term.effectPerform effectTag1 effectRow operationSignature
        canPerformOperation operationTag1 arguments1)
      (Term.effectPerform effectTag2 effectRow operationSignature
        canPerformOperation operationTag2 arguments2) := by
  subst effectTagEq
  subst operationRawEq
  subst argumentsRawEq
  cases operationTagHEq
  cases argumentsHEq
  rfl

end LeanFX2
