import LeanFX2.Term.Pointwise.IdentitySubst.IdentityEquality
import LeanFX2.Term.HEqCongr.Compound.IdentityModalHoTT
import LeanFX2.Term.HEqCongr.Atomic.Cubical
import LeanFX2.Term.HEqCongr.Atomic.Structural

/-! # LeanFX2.Term.Pointwise.IdentitySubst.IdentityStructural

Semantic slice of typed identity-substitution erasure helpers. -/

namespace LeanFX2

/-! ## Structural advanced cases -/

/-- Path application case for ordinary identity substitution. -/
theorem Term.subst_identity_pathApp_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {pathRaw intervalRaw : RawTerm scope}
    (pathTerm :
      Term context (Ty.path carrierType leftEndpoint rightEndpoint) pathRaw)
    (intervalTerm : Term context Ty.interval intervalRaw)
    (pathHEq :
      HEq (Term.subst (TermSubst.identity context) pathTerm)
        pathTerm)
    (intervalHEq :
      HEq (Term.subst (TermSubst.identity context) intervalTerm)
        intervalTerm) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.pathApp modeIsUnivalent pathTerm intervalTerm))
      (Term.pathApp modeIsUnivalent pathTerm intervalTerm) := by
  simp only [Term.subst]
  exact Term.pathApp_HEq_congr
    modeIsUnivalent
    (Ty.subst_identity carrierType)
    (RawTerm.subst_identity leftEndpoint)
    (RawTerm.subst_identity rightEndpoint)
    (RawTerm.subst_identity pathRaw)
    (RawTerm.subst_identity intervalRaw)
    pathHEq intervalHEq

/-- Glue introduction case for ordinary identity substitution. -/
theorem Term.subst_identity_glueIntro_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (baseType : Ty level scope)
    (boundaryWitness : RawTerm scope)
    {baseRaw partialRaw : RawTerm scope}
    (baseValue : Term context baseType baseRaw)
    (partialValue : Term context baseType partialRaw)
    (baseHEq :
      HEq (Term.subst (TermSubst.identity context) baseValue)
        baseValue)
    (partialHEq :
      HEq (Term.subst (TermSubst.identity context) partialValue)
        partialValue) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.glueIntro modeIsUnivalent baseType boundaryWitness
          baseValue partialValue))
      (Term.glueIntro modeIsUnivalent baseType boundaryWitness
        baseValue partialValue) := by
  simp only [Term.subst]
  exact Term.glueIntro_HEq_congr
    modeIsUnivalent
    (Ty.subst_identity baseType)
    (RawTerm.subst_identity boundaryWitness)
    (RawTerm.subst_identity baseRaw)
    (RawTerm.subst_identity partialRaw)
    baseHEq partialHEq

/-- Glue elimination case for ordinary identity substitution. -/
theorem Term.subst_identity_glueElim_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {baseType : Ty level scope}
    {boundaryWitness gluedRaw : RawTerm scope}
    (gluedValue : Term context (Ty.glue baseType boundaryWitness) gluedRaw)
    (gluedHEq :
      HEq (Term.subst (TermSubst.identity context) gluedValue)
        gluedValue) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.glueElim modeIsUnivalent gluedValue))
      (Term.glueElim modeIsUnivalent gluedValue) := by
  simp only [Term.subst]
  exact Term.glueElim_HEq_congr
    modeIsUnivalent
    (Ty.subst_identity baseType)
    (RawTerm.subst_identity boundaryWitness)
    (RawTerm.subst_identity gluedRaw)
    gluedHEq

/-- Homogeneous composition case for ordinary identity substitution. -/
theorem Term.subst_identity_hcomp_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {sidesRaw capRaw : RawTerm scope}
    (sidesValue : Term context carrierType sidesRaw)
    (capValue : Term context carrierType capRaw)
    (sidesHEq :
      HEq (Term.subst (TermSubst.identity context) sidesValue)
        sidesValue)
    (capHEq :
      HEq (Term.subst (TermSubst.identity context) capValue)
        capValue) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.hcomp modeIsUnivalent sidesValue capValue))
      (Term.hcomp modeIsUnivalent sidesValue capValue) := by
  simp only [Term.subst]
  exact Term.hcomp_HEq_congr
    modeIsUnivalent
    (Ty.subst_identity carrierType)
    (RawTerm.subst_identity sidesRaw)
    (RawTerm.subst_identity capRaw)
    sidesHEq capHEq

/-- Record introduction case for ordinary identity substitution. -/
theorem Term.subst_identity_recordIntro_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {firstRaw : RawTerm scope}
    (firstField : Term context singleFieldType firstRaw)
    (firstFieldHEq :
      HEq (Term.subst (TermSubst.identity context) firstField)
        firstField) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.recordIntro firstField))
      (Term.recordIntro firstField) := by
  simp only [Term.subst]
  exact Term.recordIntro_HEq_congr
    (Ty.subst_identity singleFieldType)
    (RawTerm.subst_identity firstRaw)
    firstFieldHEq

/-- Record projection case for ordinary identity substitution. -/
theorem Term.subst_identity_recordProj_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {recordRaw : RawTerm scope}
    (recordValue : Term context (Ty.record singleFieldType) recordRaw)
    (recordHEq :
      HEq (Term.subst (TermSubst.identity context) recordValue)
        recordValue) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.recordProj recordValue))
      (Term.recordProj recordValue) := by
  simp only [Term.subst]
  exact Term.recordProj_HEq_congr
    (Ty.subst_identity singleFieldType)
    (RawTerm.subst_identity recordRaw)
    recordHEq

/-- Refinement elimination case for ordinary identity substitution. -/
theorem Term.subst_identity_refineElim_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {refinedRaw : RawTerm scope}
    (refinedValue : Term context (Ty.refine baseType predicate) refinedRaw)
    (refinedHEq :
      HEq (Term.subst (TermSubst.identity context) refinedValue)
        refinedValue) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.refineElim refinedValue))
      (Term.refineElim refinedValue) := by
  simp only [Term.subst]
  exact Term.refineElim_HEq_congr
    (Ty.subst_identity baseType)
    (by
      rw [RawTerm.subst_pointwise
        (@Subst.identity_lift_forRaw_pointwise level scope) predicate]
      exact RawTerm.subst_identity predicate)
    (RawTerm.subst_identity refinedRaw)
    refinedHEq

/-- Codata unfold case for ordinary identity substitution. -/
theorem Term.subst_identity_codataUnfold_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {stateRaw transitionRaw : RawTerm scope}
    (initialState : Term context stateType stateRaw)
    (transition : Term context (Ty.arrow stateType outputType) transitionRaw)
    (initialStateHEq :
      HEq (Term.subst (TermSubst.identity context) initialState)
        initialState)
    (transitionHEq :
      HEq (Term.subst (TermSubst.identity context) transition)
        transition) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.codataUnfold initialState transition))
      (Term.codataUnfold initialState transition) := by
  simp only [Term.subst]
  exact Term.codataUnfold_HEq_congr
    (Ty.subst_identity stateType)
    (Ty.subst_identity outputType)
    (RawTerm.subst_identity stateRaw)
    (RawTerm.subst_identity transitionRaw)
    initialStateHEq transitionHEq

/-- Codata destructor case for ordinary identity substitution. -/
theorem Term.subst_identity_codataDest_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {codataRaw : RawTerm scope}
    (codataValue : Term context (Ty.codata stateType outputType) codataRaw)
    (codataHEq :
      HEq (Term.subst (TermSubst.identity context) codataValue)
        codataValue) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.codataDest codataValue))
      (Term.codataDest codataValue) := by
  simp only [Term.subst]
  exact Term.codataDest_HEq_congr
    (Ty.subst_identity stateType)
    (Ty.subst_identity outputType)
    (RawTerm.subst_identity codataRaw)
    codataHEq

/-- Session send case for ordinary identity substitution. -/
theorem Term.subst_identity_sessionSend_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (protocolStep : RawTerm scope)
    {payloadType : Ty level scope}
    {channelRaw payloadRaw : RawTerm scope}
    (channel : Term context (Ty.session protocolStep) channelRaw)
    (payload : Term context payloadType payloadRaw)
    (channelHEq :
      HEq (Term.subst (TermSubst.identity context) channel)
        channel)
    (payloadHEq :
      HEq (Term.subst (TermSubst.identity context) payload)
        payload) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.sessionSend protocolStep channel payload))
      (Term.sessionSend protocolStep channel payload) := by
  simp only [Term.subst]
  exact Term.sessionSend_HEq_congr
    (RawTerm.subst_identity protocolStep)
    (Ty.subst_identity payloadType)
    (RawTerm.subst_identity channelRaw)
    (RawTerm.subst_identity payloadRaw)
    channelHEq payloadHEq

/-- Session receive case for ordinary identity substitution. -/
theorem Term.subst_identity_sessionRecv_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {protocolStep : RawTerm scope}
    {channelRaw : RawTerm scope}
    (channel : Term context (Ty.session protocolStep) channelRaw)
    (channelHEq :
      HEq (Term.subst (TermSubst.identity context) channel)
        channel) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.sessionRecv channel))
      (Term.sessionRecv channel) := by
  simp only [Term.subst]
  exact Term.sessionRecv_HEq_congr
    (RawTerm.subst_identity protocolStep)
    (RawTerm.subst_identity channelRaw)
    channelHEq

/-- Direct effect-performance congruence with propositionally equal
operation carriers, scoped to ordinary identity-substitution erasure. -/
private theorem Term.effectPerform_direct_identity_carrier_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {effectTag1 effectTag2 : RawTerm scope}
    (effectRow : Effects.EffectRow)
    (effectLabel : Effects.EffectLabel)
    (rowMember : Effects.EffectRow.Member effectLabel effectRow)
    {argumentCarrier1 argumentCarrier2 resultCarrier1 resultCarrier2 :
      Ty level scope}
    {operationRaw1 operationRaw2 argumentsRaw1 argumentsRaw2 :
      RawTerm scope}
    (effectTagEq : effectTag1 = effectTag2)
    (argumentCarrierEq : argumentCarrier1 = argumentCarrier2)
    (resultCarrierEq : resultCarrier1 = resultCarrier2)
    (operationRawEq : operationRaw1 = operationRaw2)
    (argumentsRawEq : argumentsRaw1 = argumentsRaw2)
    {operationTag1 :
      Term context (Ty.effect argumentCarrier1 effectTag1)
        operationRaw1}
    {operationTag2 :
      Term context (Ty.effect argumentCarrier2 effectTag2)
        operationRaw2}
    (operationTagHEq : HEq operationTag1 operationTag2)
    {arguments1 : Term context argumentCarrier1 argumentsRaw1}
    {arguments2 : Term context argumentCarrier2 argumentsRaw2}
    (argumentsHEq : HEq arguments1 arguments2) :
    HEq
      (Term.effectPerform effectTag1 effectRow
        { effectLabel := effectLabel
          argumentCarrier := argumentCarrier1
          resultCarrier := resultCarrier1 }
        (Effects.CanPerform.direct rowMember) operationTag1 arguments1)
      (Term.effectPerform effectTag2 effectRow
        { effectLabel := effectLabel
          argumentCarrier := argumentCarrier2
          resultCarrier := resultCarrier2 }
        (Effects.CanPerform.direct rowMember) operationTag2 arguments2) := by
  subst effectTagEq
  subst argumentCarrierEq
  subst resultCarrierEq
  subst operationRawEq
  subst argumentsRawEq
  cases operationTagHEq
  cases argumentsHEq
  rfl

/-- Read-via-write effect-performance congruence with propositionally equal
operation carriers, scoped to ordinary identity-substitution erasure. -/
private theorem Term.effectPerform_readViaWrite_identity_carrier_HEq_congr
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {effectTag1 effectTag2 : RawTerm scope}
    (effectRow : Effects.EffectRow)
    (rowMember : Effects.EffectRow.Member Effects.EffectLabel.write
      effectRow)
    {argumentCarrier1 argumentCarrier2 resultCarrier1 resultCarrier2 :
      Ty level scope}
    {operationRaw1 operationRaw2 argumentsRaw1 argumentsRaw2 :
      RawTerm scope}
    (effectTagEq : effectTag1 = effectTag2)
    (argumentCarrierEq : argumentCarrier1 = argumentCarrier2)
    (resultCarrierEq : resultCarrier1 = resultCarrier2)
    (operationRawEq : operationRaw1 = operationRaw2)
    (argumentsRawEq : argumentsRaw1 = argumentsRaw2)
    {operationTag1 :
      Term context (Ty.effect argumentCarrier1 effectTag1)
        operationRaw1}
    {operationTag2 :
      Term context (Ty.effect argumentCarrier2 effectTag2)
        operationRaw2}
    (operationTagHEq : HEq operationTag1 operationTag2)
    {arguments1 : Term context argumentCarrier1 argumentsRaw1}
    {arguments2 : Term context argumentCarrier2 argumentsRaw2}
    (argumentsHEq : HEq arguments1 arguments2) :
    HEq
      (Term.effectPerform effectTag1 effectRow
        { effectLabel := Effects.EffectLabel.read
          argumentCarrier := argumentCarrier1
          resultCarrier := resultCarrier1 }
        (Effects.CanPerform.readViaWrite argumentCarrier1
          resultCarrier1 rowMember)
        operationTag1 arguments1)
      (Term.effectPerform effectTag2 effectRow
        { effectLabel := Effects.EffectLabel.read
          argumentCarrier := argumentCarrier2
          resultCarrier := resultCarrier2 }
        (Effects.CanPerform.readViaWrite argumentCarrier2
          resultCarrier2 rowMember)
        operationTag2 arguments2) := by
  subst effectTagEq
  subst argumentCarrierEq
  subst resultCarrierEq
  subst operationRawEq
  subst argumentsRawEq
  cases operationTagHEq
  cases argumentsHEq
  rfl

/-- Effect-performance case for ordinary identity substitution. -/
theorem Term.subst_identity_effectPerform_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {effectTag : RawTerm scope}
    {effectRow : Effects.EffectRow}
    {operationSignature : Effects.OperationSignature (Ty level scope)}
    {canPerformOperation :
      Effects.CanPerform effectRow operationSignature}
    {operationRaw argumentsRaw : RawTerm scope}
    (operationTag :
      Term context
        (Ty.effect operationSignature.argumentCarrier effectTag)
        operationRaw)
    (arguments :
      Term context operationSignature.argumentCarrier argumentsRaw)
    (operationTagHEq :
      HEq (Term.subst (TermSubst.identity context) operationTag)
        operationTag)
    (argumentsHEq :
      HEq (Term.subst (TermSubst.identity context) arguments)
        arguments) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.effectPerform effectTag effectRow operationSignature
          canPerformOperation operationTag arguments))
      (Term.effectPerform effectTag effectRow operationSignature
        canPerformOperation operationTag arguments) := by
  simp only [Term.subst]
  cases operationSignature with
  | mk effectLabel argumentCarrier resultCarrier =>
    cases canPerformOperation with
    | direct rowMember =>
      simp only [Effects.OperationSignature.map]
      exact Term.effectPerform_direct_identity_carrier_HEq_congr
        effectRow effectLabel rowMember
        (RawTerm.subst_identity effectTag)
        (Ty.subst_identity argumentCarrier)
        (Ty.subst_identity resultCarrier)
        (RawTerm.subst_identity operationRaw)
        (RawTerm.subst_identity argumentsRaw)
        operationTagHEq
        argumentsHEq
    | readViaWrite argumentCarrier resultCarrier rowMember =>
      simp only [Effects.OperationSignature.map]
      exact Term.effectPerform_readViaWrite_identity_carrier_HEq_congr
        effectRow rowMember
        (RawTerm.subst_identity effectTag)
        (Ty.subst_identity argumentCarrier)
        (Ty.subst_identity resultCarrier)
        (RawTerm.subst_identity operationRaw)
        (RawTerm.subst_identity argumentsRaw)
        operationTagHEq
        argumentsHEq

/-- Universe cumulativity marker case for ordinary identity substitution. -/
theorem Term.subst_identity_cumulUp_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {codeRaw : RawTerm scope}
    (typeCode : Term context (Ty.universe lowerLevel levelLeLow) codeRaw)
    (typeCodeHEq :
      HEq (Term.subst (TermSubst.identity context) typeCode)
        typeCode) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.cumulUp lowerLevel higherLevel cumulMonotone
          levelLeLow levelLeHigh typeCode))
      (Term.cumulUp lowerLevel higherLevel cumulMonotone
        levelLeLow levelLeHigh typeCode) := by
  simp only [Term.subst]
  exact Term.cumulUp_HEq_congr
    (RawTerm.subst_identity codeRaw)
    typeCodeHEq

/-- Equivalence application case for ordinary identity substitution. -/
theorem Term.subst_identity_equivApp_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {equivRaw argumentRaw : RawTerm scope}
    (equivTerm : Term context (Ty.equiv carrierA carrierB) equivRaw)
    (argumentTerm : Term context carrierA argumentRaw)
    (equivHEq :
      HEq (Term.subst (TermSubst.identity context) equivTerm)
        equivTerm)
    (argumentHEq :
      HEq (Term.subst (TermSubst.identity context) argumentTerm)
        argumentTerm) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.equivApp equivTerm argumentTerm))
      (Term.equivApp equivTerm argumentTerm) := by
  simp only [Term.subst]
  exact Term.equivApp_HEq_congr
    (Ty.subst_identity carrierA)
    (Ty.subst_identity carrierB)
    (RawTerm.subst_identity equivRaw)
    (RawTerm.subst_identity argumentRaw)
    equivHEq argumentHEq

/-- Univalence beta application case for ordinary identity substitution. -/
theorem Term.subst_identity_equivApply_HEq
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {equivRaw argumentRaw : RawTerm scope}
    (equivTerm : Term context (Ty.equiv carrierA carrierB) equivRaw)
    (argumentTerm : Term context carrierA argumentRaw)
    (equivHEq :
      HEq (Term.subst (TermSubst.identity context) equivTerm)
        equivTerm)
    (argumentHEq :
      HEq (Term.subst (TermSubst.identity context) argumentTerm)
        argumentTerm) :
    HEq
      (Term.subst (TermSubst.identity context)
        (Term.equivApply equivTerm argumentTerm))
      (Term.equivApply equivTerm argumentTerm) := by
  simp only [Term.subst]
  exact Term.equivApply_HEq_congr
    (Ty.subst_identity carrierA)
    (Ty.subst_identity carrierB)
    (RawTerm.subst_identity equivRaw)
    (RawTerm.subst_identity argumentRaw)
    equivHEq argumentHEq

end LeanFX2
