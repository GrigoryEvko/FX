import LeanFX2.Reducibility.Kripke.Fundamental.StructuralSN

/-! # LeanFX2.Reducibility.Kripke.Fundamental.HoTTCodesAndEffects

SN-preservation wrappers for HoTT, type-code, cubical, heterogeneous,
and effect constructors.
-/

namespace LeanFX2

/-- equivReflId always SN (closed term). -/
theorem ReducibleK.fundamental_equivReflId_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (carrier : Ty level scope) :
    Term.isStronglyNormalizing
      (Term.equivReflId (context := sourceCtx) carrier) :=
  Term.equivReflId_isStronglyNormalizing carrier

/-- uaToEquiv preserves SN: proof SN → uaToEquiv SN. -/
theorem ReducibleK.fundamental_uaToEquiv_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (leftTy rightTy : Ty level scope)
    (leftTyRaw rightTyRaw : RawTerm scope)
    {proofRaw : RawTerm scope}
    {proof :
        Term sourceCtx
          (Ty.id (Ty.universe innerLevel innerLevelLt)
            leftTyRaw rightTyRaw)
          proofRaw}
    (proofIsSN : Term.isStronglyNormalizing proof) :
    Term.isStronglyNormalizing
      (Term.uaToEquiv innerLevel innerLevelLt
        leftTy rightTy leftTyRaw rightTyRaw proof) :=
  Term.uaToEquiv_isStronglyNormalizing innerLevel innerLevelLt
    leftTy rightTy leftTyRaw rightTyRaw proofIsSN

/-- arrowCode preserves SN: both domain/codomain SN → arrowCode SN. -/
theorem ReducibleK.fundamental_arrowCode_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {domainCodeRaw codomainCodeRaw : RawTerm scope}
    (domainCodeIsSN : RawTerm.isStronglyNormalizing domainCodeRaw)
    (codomainCodeIsSN : RawTerm.isStronglyNormalizing codomainCodeRaw) :
    Term.isStronglyNormalizing
      (Term.arrowCode (context := sourceCtx)
        outerLevel levelLe domainCodeRaw codomainCodeRaw) :=
  Term.arrowCode_isStronglyNormalizing outerLevel levelLe
    domainCodeIsSN codomainCodeIsSN

/-- eitherCode preserves SN: left/right SN → eitherCode SN. -/
theorem ReducibleK.fundamental_eitherCode_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftCodeRaw rightCodeRaw : RawTerm scope}
    (leftCodeIsSN : RawTerm.isStronglyNormalizing leftCodeRaw)
    (rightCodeIsSN : RawTerm.isStronglyNormalizing rightCodeRaw) :
    Term.isStronglyNormalizing
      (Term.eitherCode (context := sourceCtx)
        outerLevel levelLe leftCodeRaw rightCodeRaw) :=
  Term.eitherCode_isStronglyNormalizing outerLevel levelLe
    leftCodeIsSN rightCodeIsSN

/-- equivCode preserves SN: left/right SN → equivCode SN. -/
theorem ReducibleK.fundamental_equivCode_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftTypeCodeRaw rightTypeCodeRaw : RawTerm scope}
    (leftTypeCodeIsSN : RawTerm.isStronglyNormalizing leftTypeCodeRaw)
    (rightTypeCodeIsSN : RawTerm.isStronglyNormalizing rightTypeCodeRaw) :
    Term.isStronglyNormalizing
      (Term.equivCode (context := sourceCtx)
        outerLevel levelLe leftTypeCodeRaw rightTypeCodeRaw) :=
  Term.equivCode_isStronglyNormalizing outerLevel levelLe
    leftTypeCodeIsSN rightTypeCodeIsSN

/-- listCode preserves SN: element SN → listCode SN. -/
theorem ReducibleK.fundamental_listCode_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {elementCodeRaw : RawTerm scope}
    (elementCodeIsSN : RawTerm.isStronglyNormalizing elementCodeRaw) :
    Term.isStronglyNormalizing
      (Term.listCode (context := sourceCtx)
        outerLevel levelLe elementCodeRaw) :=
  Term.listCode_isStronglyNormalizing outerLevel levelLe elementCodeIsSN

/-- optionCode preserves SN: element SN → optionCode SN. -/
theorem ReducibleK.fundamental_optionCode_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {elementCodeRaw : RawTerm scope}
    (elementCodeIsSN : RawTerm.isStronglyNormalizing elementCodeRaw) :
    Term.isStronglyNormalizing
      (Term.optionCode (context := sourceCtx)
        outerLevel levelLe elementCodeRaw) :=
  Term.optionCode_isStronglyNormalizing outerLevel levelLe elementCodeIsSN

/-- idCode preserves SN: typeCode + left + right SN → idCode SN. -/
theorem ReducibleK.fundamental_idCode_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {typeCodeRaw leftRaw rightRaw : RawTerm scope}
    (typeCodeIsSN : RawTerm.isStronglyNormalizing typeCodeRaw)
    (leftIsSN : RawTerm.isStronglyNormalizing leftRaw)
    (rightIsSN : RawTerm.isStronglyNormalizing rightRaw) :
    Term.isStronglyNormalizing
      (Term.idCode (context := sourceCtx)
        outerLevel levelLe typeCodeRaw leftRaw rightRaw) :=
  Term.idCode_isStronglyNormalizing outerLevel levelLe
    typeCodeIsSN leftIsSN rightIsSN

/-- recordIntro preserves SN: field SN → recordIntro SN. -/
theorem ReducibleK.fundamental_recordIntro_sn
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {firstRaw : RawTerm scope}
    {firstField : Term context singleFieldType firstRaw}
    (firstFieldIsSN : Term.isStronglyNormalizing firstField) :
    Term.isStronglyNormalizing (Term.recordIntro firstField) :=
  Term.recordIntro_isStronglyNormalizing firstFieldIsSN

/-- recordProj preserves SN: record SN → recordProj SN. -/
theorem ReducibleK.fundamental_recordProj_sn
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {recordRaw : RawTerm scope}
    {recordValue : Term context (Ty.record singleFieldType) recordRaw}
    (recordIsSN : Term.isStronglyNormalizing recordValue) :
    Term.isStronglyNormalizing (Term.recordProj recordValue) :=
  Term.recordProj_isStronglyNormalizing recordIsSN

/-- refineIntro preserves SN: base + proof SN → refineIntro SN. -/
theorem ReducibleK.fundamental_refineIntro_sn
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {valueRaw proofRaw : RawTerm scope}
    {baseValue : Term context baseType valueRaw}
    {predicateProof : Term context Ty.unit proofRaw}
    (valueIsSN : Term.isStronglyNormalizing baseValue)
    (proofIsSN : Term.isStronglyNormalizing predicateProof) :
    Term.isStronglyNormalizing
      (Term.refineIntro (predicate := predicate) baseValue predicateProof) :=
  Term.refineIntro_isStronglyNormalizing valueIsSN proofIsSN

/-- refineElim preserves SN: refined SN → refineElim SN. -/
theorem ReducibleK.fundamental_refineElim_sn
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {refinedRaw : RawTerm scope}
    {refinedValue : Term context (Ty.refine baseType predicate) refinedRaw}
    (refinedIsSN : Term.isStronglyNormalizing refinedValue) :
    Term.isStronglyNormalizing (Term.refineElim refinedValue) :=
  Term.refineElim_isStronglyNormalizing refinedIsSN

/-- codataUnfold preserves SN: state + transition SN → codataUnfold SN. -/
theorem ReducibleK.fundamental_codataUnfold_sn
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {stateRaw transitionRaw : RawTerm scope}
    {initialState : Term context stateType stateRaw}
    {transition :
        Term context (Ty.arrow stateType outputType) transitionRaw}
    (stateIsSN : Term.isStronglyNormalizing initialState)
    (transitionIsSN : Term.isStronglyNormalizing transition) :
    Term.isStronglyNormalizing
      (Term.codataUnfold initialState transition) :=
  Term.codataUnfold_isStronglyNormalizing stateIsSN transitionIsSN

/-- lam preserves SN: body SN → lam SN. -/
theorem ReducibleK.fundamental_lam_sn
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
        Term (context.cons domainType) codomainType.weaken bodyRaw}
    (bodyIsSN : Term.isStronglyNormalizing bodyTerm) :
    Term.isStronglyNormalizing
      (Term.lam (codomainType := codomainType) bodyTerm) :=
  Term.lam_isStronglyNormalizing bodyIsSN

/-- lamPi preserves SN: body SN → lamPi SN. -/
theorem ReducibleK.fundamental_lamPi_sn
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm : Term (context.cons domainType) codomainType bodyRaw}
    (bodyIsSN : Term.isStronglyNormalizing bodyTerm) :
    Term.isStronglyNormalizing (Term.lamPi bodyTerm) :=
  Term.lamPi_isStronglyNormalizing bodyIsSN

/-- pathLam preserves SN at univalent mode: body SN → pathLam SN. -/
theorem ReducibleK.fundamental_pathLam_sn
    {level scope : Nat}
    {context : Ctx Mode.univalent level scope}
    (carrierType : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope)
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm :
        Term (context.cons Ty.interval) carrierType.weaken bodyRaw}
    (bodyIsSN : Term.isStronglyNormalizing bodyTerm) :
    Term.isStronglyNormalizing
      (Term.pathLam rfl carrierType leftEndpoint rightEndpoint bodyTerm) :=
  Term.pathLam_isStronglyNormalizing rfl carrierType
    leftEndpoint rightEndpoint bodyIsSN

/-- glueIntro preserves SN at univalent mode: base + partial SN → SN. -/
theorem ReducibleK.fundamental_glueIntro_sn
    {level scope : Nat}
    {context : Ctx Mode.univalent level scope}
    (baseType : Ty level scope)
    (boundaryWitness : RawTerm scope)
    {baseRaw partialRaw : RawTerm scope}
    {baseValue : Term context baseType baseRaw}
    {partialValue : Term context baseType partialRaw}
    (baseIsSN : Term.isStronglyNormalizing baseValue)
    (partialIsSN : Term.isStronglyNormalizing partialValue) :
    Term.isStronglyNormalizing
      (Term.glueIntro rfl baseType boundaryWitness baseValue partialValue) :=
  Term.glueIntro_isStronglyNormalizing rfl baseType boundaryWitness
    baseIsSN partialIsSN

/-- glueElim preserves SN at univalent mode: glued SN → SN. -/
theorem ReducibleK.fundamental_glueElim_sn
    {level scope : Nat}
    {context : Ctx Mode.univalent level scope}
    {baseType : Ty level scope}
    {boundaryWitness gluedRaw : RawTerm scope}
    {gluedValue :
        Term context (Ty.glue baseType boundaryWitness) gluedRaw}
    (gluedIsSN : Term.isStronglyNormalizing gluedValue) :
    Term.isStronglyNormalizing (Term.glueElim rfl gluedValue) :=
  Term.glueElim_isStronglyNormalizing rfl gluedIsSN

/-- equivIntroHet preserves SN: forward + backward SN → SN. -/
theorem ReducibleK.fundamental_equivIntroHet_sn
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {forwardRaw backwardRaw leftInvRaw rightInvRaw : RawTerm scope}
    {forward :
        Term context (Ty.arrow carrierA carrierB) forwardRaw}
    {backward :
        Term context (Ty.arrow carrierB carrierA) backwardRaw}
    {leftInv :
        Term context
          (equivIntroHetLeftInverseType carrierA forwardRaw backwardRaw)
          leftInvRaw}
    {rightInv :
        Term context
          (equivIntroHetRightInverseType carrierB forwardRaw backwardRaw)
          rightInvRaw}
    (forwardIsSN : Term.isStronglyNormalizing forward)
    (backwardIsSN : Term.isStronglyNormalizing backward) :
    Term.isStronglyNormalizing
      (Term.equivIntroHet forward backward leftInv rightInv) :=
  Term.equivIntroHet_isStronglyNormalizing forwardIsSN backwardIsSN

/-- funextRefl preserves SN: raw apply SN → funextRefl SN. -/
theorem ReducibleK.fundamental_funextRefl_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    {applyRaw : RawTerm (scope + 1)}
    (applyIsSN : RawTerm.isStronglyNormalizing applyRaw) :
    Term.isStronglyNormalizing
      (Term.funextRefl (context := sourceCtx)
        domainType codomainType applyRaw) :=
  Term.funextRefl_isStronglyNormalizing_of_apply
    domainType codomainType applyIsSN

/-- funextReflAtId preserves SN: raw apply SN → funextReflAtId SN. -/
theorem ReducibleK.fundamental_funextReflAtId_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    {applyRaw : RawTerm (scope + 1)}
    (applyIsSN : RawTerm.isStronglyNormalizing applyRaw) :
    Term.isStronglyNormalizing
      (Term.funextReflAtId (context := sourceCtx)
        domainType codomainType applyRaw) :=
  Term.funextReflAtId_isStronglyNormalizing_of_apply
    domainType codomainType applyIsSN

/-- oeqFunext preserves SN: pointwise SN → oeqFunext SN. -/
theorem ReducibleK.fundamental_oeqFunext_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    (leftFunctionRaw rightFunctionRaw : RawTerm scope)
    {pointwiseRaw : RawTerm scope}
    {pointwiseProof :
        Term sourceCtx
          (oeqFunextPointwiseType domainType codomainType
            leftFunctionRaw rightFunctionRaw)
          pointwiseRaw}
    (pointwiseIsSN : Term.isStronglyNormalizing pointwiseProof) :
    Term.isStronglyNormalizing
      (Term.oeqFunext domainType codomainType
        leftFunctionRaw rightFunctionRaw pointwiseProof) :=
  Term.oeqFunext_isStronglyNormalizing
    domainType codomainType leftFunctionRaw rightFunctionRaw pointwiseIsSN

/-- effectPerform preserves SN: operation + arguments SN → SN. -/
theorem ReducibleK.fundamental_effectPerform_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (effectTag : RawTerm scope)
    (effectRow : Effects.EffectRow)
    (operationSignature : Effects.OperationSignature (Ty level scope))
    (canPerformOperation :
        Effects.CanPerform effectRow operationSignature)
    {operationRaw argumentsRaw : RawTerm scope}
    {operationTag :
        Term sourceCtx
          (Ty.effect operationSignature.argumentCarrier effectTag)
          operationRaw}
    {arguments :
        Term sourceCtx operationSignature.argumentCarrier argumentsRaw}
    (operationIsSN : Term.isStronglyNormalizing operationTag)
    (argumentsAreSN : Term.isStronglyNormalizing arguments) :
    Term.isStronglyNormalizing
      (Term.effectPerform effectTag effectRow operationSignature
        canPerformOperation operationTag arguments) :=
  Term.effectPerform_isStronglyNormalizing effectTag effectRow
    operationSignature canPerformOperation operationIsSN argumentsAreSN

/-- uaIntroHet preserves SN: equiv witness SN → uaIntroHet SN. -/
theorem ReducibleK.fundamental_uaIntroHet_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    {carrierA carrierB : Ty level scope}
    (carrierARaw carrierBRaw : RawTerm scope)
    {forwardRaw backwardRaw : RawTerm scope}
    {equivWitness :
        Term sourceCtx (Ty.equiv carrierA carrierB)
          (RawTerm.equivIntro forwardRaw backwardRaw)}
    (equivWitnessIsSN : Term.isStronglyNormalizing equivWitness) :
    Term.isStronglyNormalizing
      (Term.uaIntroHet innerLevel innerLevelLt
        carrierARaw carrierBRaw equivWitness) :=
  Term.uaIntroHet_isStronglyNormalizing innerLevel innerLevelLt
    carrierARaw carrierBRaw equivWitnessIsSN

/-- equivReflIdAtId always SN (closed term). -/
theorem ReducibleK.fundamental_equivReflIdAtId_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level scope)
    (carrierRaw : RawTerm scope) :
    Term.isStronglyNormalizing
      (Term.equivReflIdAtId (context := sourceCtx)
        innerLevel innerLevelLt carrier carrierRaw) :=
  Term.equivReflIdAtId_isStronglyNormalizing
    innerLevel innerLevelLt carrier carrierRaw

end LeanFX2
