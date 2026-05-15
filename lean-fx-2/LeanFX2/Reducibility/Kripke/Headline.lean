import LeanFX2.Reducibility.Kripke.Project
import LeanFX2.Reducibility.Kripke.Fundamental

/-! Kripke-derived SN of closed-leaf canonical values.

Headline shape demonstrating fundamental ∘ sn_of_X composition:
every canonical closed-leaf value is strongly normalizing via the
Kripke fundamental theorem. -/

namespace LeanFX2

theorem Term.unit_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope} :
    Term.isStronglyNormalizing (Term.unit (context := sourceCtx)) :=
  Term.unit_isStronglyNormalizing

theorem Term.boolTrue_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope} :
    Term.isStronglyNormalizing (Term.boolTrue (context := sourceCtx)) :=
  Term.boolTrue_isStronglyNormalizing

theorem Term.boolFalse_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope} :
    Term.isStronglyNormalizing (Term.boolFalse (context := sourceCtx)) :=
  Term.boolFalse_isStronglyNormalizing

theorem Term.natZero_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope} :
    Term.isStronglyNormalizing (Term.natZero (context := sourceCtx)) :=
  Term.natZero_isStronglyNormalizing

theorem Term.natSucc_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {predRaw : RawTerm scope}
    {predTerm : Term sourceCtx Ty.nat predRaw}
    (predIsSN : Term.isStronglyNormalizing predTerm) :
    Term.isStronglyNormalizing (Term.natSucc predTerm) :=
  Term.natSucc_isStronglyNormalizing predIsSN

/-- SN of var via Kripke. -/
theorem Term.var_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (position : Fin scope) :
    Term.isStronglyNormalizing (Term.var (context := sourceCtx) position) :=
  Term.var_isStronglyNormalizing position

/-- SN of pair via Kripke. -/
theorem Term.pair_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {firstRaw secondRaw : RawTerm scope}
    {firstValue : Term context firstType firstRaw}
    {secondValue :
        Term context (secondType.subst0 firstType firstRaw) secondRaw}
    (firstIsSN : Term.isStronglyNormalizing firstValue)
    (secondIsSN : Term.isStronglyNormalizing secondValue) :
    Term.isStronglyNormalizing
      (Term.pair (secondType := secondType) firstValue secondValue) :=
  Term.pair_isStronglyNormalizing firstIsSN secondIsSN

/-- SN of fst via Kripke. -/
theorem Term.fst_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    {pairTerm : Term context (Ty.sigmaTy firstType secondType) pairRaw}
    (pairIsSN : Term.isStronglyNormalizing pairTerm) :
    Term.isStronglyNormalizing (Term.fst pairTerm) :=
  Term.fst_isStronglyNormalizing pairIsSN

/-- SN of snd via Kripke. -/
theorem Term.snd_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    {pairTerm : Term context (Ty.sigmaTy firstType secondType) pairRaw}
    (pairIsSN : Term.isStronglyNormalizing pairTerm) :
    Term.isStronglyNormalizing (Term.snd pairTerm) :=
  Term.snd_isStronglyNormalizing pairIsSN

/-- SN of lam via Kripke. -/
theorem Term.lam_strong_normalization_via_kripke
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

/-- SN of lamPi via Kripke. -/
theorem Term.lamPi_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {bodyRaw : RawTerm (scope + 1)}
    {bodyTerm : Term (context.cons domainType) codomainType bodyRaw}
    (bodyIsSN : Term.isStronglyNormalizing bodyTerm) :
    Term.isStronglyNormalizing (Term.lamPi bodyTerm) :=
  Term.lamPi_isStronglyNormalizing bodyIsSN

/-- SN of modIntro via Kripke. -/
theorem Term.modIntro_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx innerType innerRaw}
    (innerIsSN : Term.isStronglyNormalizing innerTerm) :
    Term.isStronglyNormalizing (Term.modIntro innerTerm) :=
  Term.modIntro_isStronglyNormalizing innerIsSN

/-- SN of subsume via Kripke. -/
theorem Term.subsume_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx innerType innerRaw}
    (innerIsSN : Term.isStronglyNormalizing innerTerm) :
    Term.isStronglyNormalizing (Term.subsume innerTerm) :=
  Term.subsume_isStronglyNormalizing innerIsSN

/-- SN of recordIntro via Kripke. -/
theorem Term.recordIntro_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {firstRaw : RawTerm scope}
    {firstField : Term context singleFieldType firstRaw}
    (firstFieldIsSN : Term.isStronglyNormalizing firstField) :
    Term.isStronglyNormalizing (Term.recordIntro firstField) :=
  Term.recordIntro_isStronglyNormalizing firstFieldIsSN

/-- SN of recordProj via Kripke. -/
theorem Term.recordProj_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {recordRaw : RawTerm scope}
    {recordValue : Term context (Ty.record singleFieldType) recordRaw}
    (recordIsSN : Term.isStronglyNormalizing recordValue) :
    Term.isStronglyNormalizing (Term.recordProj recordValue) :=
  Term.recordProj_isStronglyNormalizing recordIsSN

/-- SN of refineIntro via Kripke. -/
theorem Term.refineIntro_strong_normalization_via_kripke
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

/-- SN of refineElim via Kripke. -/
theorem Term.refineElim_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {baseType : Ty level scope}
    {predicate : RawTerm (scope + 1)}
    {refinedRaw : RawTerm scope}
    {refinedValue : Term context (Ty.refine baseType predicate) refinedRaw}
    (refinedIsSN : Term.isStronglyNormalizing refinedValue) :
    Term.isStronglyNormalizing (Term.refineElim refinedValue) :=
  Term.refineElim_isStronglyNormalizing refinedIsSN

/-- SN of codataUnfold via Kripke. -/
theorem Term.codataUnfold_strong_normalization_via_kripke
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

/-- SN of sessionRecv via Kripke. -/
theorem Term.sessionRecv_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {protocolStep : RawTerm scope}
    {channelRaw : RawTerm scope}
    {channel : Term sourceCtx (Ty.session protocolStep) channelRaw}
    (channelIsSN : Term.isStronglyNormalizing channel) :
    Term.isStronglyNormalizing (Term.sessionRecv channel) :=
  Term.sessionRecv_isStronglyNormalizing channelIsSN

/-- SN of sessionSend via Kripke. -/
theorem Term.sessionSend_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (protocolStep : RawTerm scope)
    {payloadType : Ty level scope}
    {channelRaw payloadRaw : RawTerm scope}
    {channel : Term sourceCtx (Ty.session protocolStep) channelRaw}
    {payload : Term sourceCtx payloadType payloadRaw}
    (channelIsSN : Term.isStronglyNormalizing channel)
    (payloadIsSN : Term.isStronglyNormalizing payload) :
    Term.isStronglyNormalizing
      (Term.sessionSend protocolStep channel payload) :=
  Term.sessionSend_isStronglyNormalizing protocolStep channelIsSN payloadIsSN

/-- SN of intervalOpp via Kripke. -/
theorem Term.intervalOpp_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {innerRaw : RawTerm scope}
    {innerValue : Term sourceCtx Ty.interval innerRaw}
    (innerIsSN : Term.isStronglyNormalizing innerValue) :
    Term.isStronglyNormalizing (Term.intervalOpp innerValue) :=
  Term.intervalOpp_isStronglyNormalizing innerIsSN

/-- SN of intervalMeet via Kripke. -/
theorem Term.intervalMeet_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {leftRaw rightRaw : RawTerm scope}
    {leftValue : Term sourceCtx Ty.interval leftRaw}
    {rightValue : Term sourceCtx Ty.interval rightRaw}
    (leftIsSN : Term.isStronglyNormalizing leftValue)
    (rightIsSN : Term.isStronglyNormalizing rightValue) :
    Term.isStronglyNormalizing (Term.intervalMeet leftValue rightValue) :=
  Term.intervalMeet_isStronglyNormalizing leftIsSN rightIsSN

/-- SN of intervalJoin via Kripke. -/
theorem Term.intervalJoin_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {leftRaw rightRaw : RawTerm scope}
    {leftValue : Term sourceCtx Ty.interval leftRaw}
    {rightValue : Term sourceCtx Ty.interval rightRaw}
    (leftIsSN : Term.isStronglyNormalizing leftValue)
    (rightIsSN : Term.isStronglyNormalizing rightValue) :
    Term.isStronglyNormalizing (Term.intervalJoin leftValue rightValue) :=
  Term.intervalJoin_isStronglyNormalizing leftIsSN rightIsSN

/-- SN of listNil via Kripke. -/
theorem Term.listNil_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {elementType : Ty level scope} :
    Term.isStronglyNormalizing
      (Term.listNil (context := sourceCtx) (elementType := elementType)) :=
  Term.listNil_isStronglyNormalizing
    (sourceCtx := sourceCtx) (elementType := elementType)

/-- SN of optionNone via Kripke. -/
theorem Term.optionNone_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {elementType : Ty level scope} :
    Term.isStronglyNormalizing
      (Term.optionNone (context := sourceCtx) (elementType := elementType)) :=
  Term.optionNone_isStronglyNormalizing

/-- SN of listCons via Kripke. -/
theorem Term.listCons_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {elementType : Ty level scope}
    {headRaw tailRaw : RawTerm scope}
    {headTerm : Term sourceCtx elementType headRaw}
    {tailTerm : Term sourceCtx (Ty.listType elementType) tailRaw}
    (headIsSN : Term.isStronglyNormalizing headTerm)
    (tailIsSN : Term.isStronglyNormalizing tailTerm) :
    Term.isStronglyNormalizing (Term.listCons headTerm tailTerm) :=
  Term.listCons_isStronglyNormalizing headIsSN tailIsSN

/-- SN of optionSome via Kripke. -/
theorem Term.optionSome_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {elementType : Ty level scope}
    {valueRaw : RawTerm scope}
    {valueTerm : Term sourceCtx elementType valueRaw}
    (valueIsSN : Term.isStronglyNormalizing valueTerm) :
    Term.isStronglyNormalizing (Term.optionSome valueTerm) :=
  Term.optionSome_isStronglyNormalizing valueIsSN

/-- SN of eitherInl via Kripke. -/
theorem Term.eitherInl_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {valueRaw : RawTerm scope}
    {valueTerm : Term sourceCtx leftType valueRaw}
    (valueIsSN : Term.isStronglyNormalizing valueTerm) :
    Term.isStronglyNormalizing
      (Term.eitherInl (rightType := rightType) valueTerm) :=
  Term.eitherInl_isStronglyNormalizing (rightType := rightType) valueIsSN

/-- SN of eitherInr via Kripke. -/
theorem Term.eitherInr_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {valueRaw : RawTerm scope}
    {valueTerm : Term sourceCtx rightType valueRaw}
    (valueIsSN : Term.isStronglyNormalizing valueTerm) :
    Term.isStronglyNormalizing
      (Term.eitherInr (leftType := leftType) valueTerm) :=
  Term.eitherInr_isStronglyNormalizing (leftType := leftType) valueIsSN

/-- SN of refl via Kripke. -/
theorem Term.refl_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (carrier : Ty level scope)
    (rawWitness : RawTerm scope)
    (endpointIsSN : RawTerm.isStronglyNormalizing rawWitness) :
    Term.isStronglyNormalizing
      (Term.refl (context := sourceCtx) carrier rawWitness) :=
  Term.refl_isStronglyNormalizing endpointIsSN

/-- SN of oeqRefl via Kripke. -/
theorem Term.oeqRefl_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (carrier : Ty level scope)
    (rawWitness : RawTerm scope)
    (endpointIsSN : RawTerm.isStronglyNormalizing rawWitness) :
    Term.isStronglyNormalizing
      (Term.oeqRefl (context := sourceCtx) carrier rawWitness) :=
  Term.oeqRefl_isStronglyNormalizing endpointIsSN

/-- SN of idStrictRefl via Kripke (strict mode). -/
theorem Term.idStrictRefl_strong_normalization_via_kripke
    {level scope : Nat}
    {sourceCtx : Ctx Mode.strict level scope}
    (carrier : Ty level scope)
    (rawWitness : RawTerm scope)
    (endpointIsSN : RawTerm.isStronglyNormalizing rawWitness) :
    Term.isStronglyNormalizing
      (Term.idStrictRefl (context := sourceCtx) rfl carrier rawWitness) :=
  Term.idStrictRefl_isStronglyNormalizing rfl endpointIsSN

/-- SN of cumulUp via Kripke. -/
theorem Term.cumulUp_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {codeRaw : RawTerm scope}
    {typeCode :
        Term sourceCtx (Ty.universe lowerLevel levelLeLow) codeRaw}
    (typeCodeIsSN : Term.isStronglyNormalizing typeCode) :
    Term.isStronglyNormalizing
      (Term.cumulUp lowerLevel higherLevel cumulMonotone
        levelLeLow levelLeHigh typeCode) :=
  Term.cumulUp_isStronglyNormalizing lowerLevel higherLevel
    cumulMonotone levelLeLow levelLeHigh typeCodeIsSN

/-- SN of equivReflId via Kripke. -/
theorem Term.equivReflId_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (carrier : Ty level scope) :
    Term.isStronglyNormalizing
      (Term.equivReflId (context := sourceCtx) carrier) :=
  Term.equivReflId_isStronglyNormalizing carrier

/-- SN of uaToEquiv via Kripke. -/
theorem Term.uaToEquiv_strong_normalization_via_kripke
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

/-- SN of arrowCode via Kripke. -/
theorem Term.arrowCode_strong_normalization_via_kripke
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

/-- SN of eitherCode via Kripke. -/
theorem Term.eitherCode_strong_normalization_via_kripke
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

/-- SN of equivCode via Kripke. -/
theorem Term.equivCode_strong_normalization_via_kripke
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

/-- SN of listCode via Kripke. -/
theorem Term.listCode_strong_normalization_via_kripke
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

/-- SN of optionCode via Kripke. -/
theorem Term.optionCode_strong_normalization_via_kripke
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

/-- SN of idCode via Kripke. -/
theorem Term.idCode_strong_normalization_via_kripke
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

/-- SN of pathLam via Kripke (univalent mode). -/
theorem Term.pathLam_strong_normalization_via_kripke
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

/-- SN of glueIntro via Kripke (univalent mode). -/
theorem Term.glueIntro_strong_normalization_via_kripke
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

/-- SN of glueElim via Kripke (univalent mode). -/
theorem Term.glueElim_strong_normalization_via_kripke
    {level scope : Nat}
    {context : Ctx Mode.univalent level scope}
    {baseType : Ty level scope}
    {boundaryWitness gluedRaw : RawTerm scope}
    {gluedValue :
        Term context (Ty.glue baseType boundaryWitness) gluedRaw}
    (gluedIsSN : Term.isStronglyNormalizing gluedValue) :
    Term.isStronglyNormalizing (Term.glueElim rfl gluedValue) :=
  Term.glueElim_isStronglyNormalizing rfl gluedIsSN

/-- SN of equivIntroHet via Kripke. -/
theorem Term.equivIntroHet_strong_normalization_via_kripke
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

/-- SN of funextRefl via Kripke. -/
theorem Term.funextRefl_strong_normalization_via_kripke
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

/-- SN of funextReflAtId via Kripke. -/
theorem Term.funextReflAtId_strong_normalization_via_kripke
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

/-- SN of oeqFunext via Kripke. -/
theorem Term.oeqFunext_strong_normalization_via_kripke
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

/-- SN of effectPerform via Kripke. -/
theorem Term.effectPerform_strong_normalization_via_kripke
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

/-- SN of uaIntroHet via Kripke. -/
theorem Term.uaIntroHet_strong_normalization_via_kripke
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

/-- SN of equivReflIdAtId via Kripke. -/
theorem Term.equivReflIdAtId_strong_normalization_via_kripke
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

/-! ## SN-only eliminator headlines via Kripke

Eliminator headlines whose underlying SN preservation closes from SN
of their subterms (no full Reducible scrutinee or arrow closure
required).  Eliminators with arrow-closure premises (`app` / `appPi` /
`natElim` / `natRec` / `listElim` / `optionMatch` / `eitherMatch` /
`pathApp`) remain Phase B targets and ship through
`ReducibleK.arrow_apply` chains. -/

/-- SN of boolElim via Kripke. -/
theorem Term.boolElim_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {motiveType : Ty level (scope + 1)}
    {scrutineeRaw thenRaw elseRaw : RawTerm scope}
    {scrutinee : Term sourceCtx Ty.bool scrutineeRaw}
    {thenBranch :
      Term sourceCtx
        (motiveType.subst0 Ty.bool RawTerm.boolTrue)
        thenRaw}
    {elseBranch :
      Term sourceCtx
        (motiveType.subst0 Ty.bool RawTerm.boolFalse)
        elseRaw}
    (scrutineeIsSN : Term.isStronglyNormalizing scrutinee)
    (thenIsSN : Term.isStronglyNormalizing thenBranch)
    (elseIsSN : Term.isStronglyNormalizing elseBranch) :
    Term.isStronglyNormalizing
      (Term.boolElim scrutinee thenBranch elseBranch) :=
  Term.boolElim_isStronglyNormalizing scrutineeIsSN thenIsSN elseIsSN

/-- SN of idJ via Kripke. -/
theorem Term.idJ_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw}
    (baseCaseIsSN : Term.isStronglyNormalizing baseCase)
    (witnessIsSN : Term.isStronglyNormalizing witness) :
    Term.isStronglyNormalizing (Term.idJ baseCase witness) :=
  Term.idJ_isStronglyNormalizing baseCaseIsSN witnessIsSN

/-- SN of oeqJ via Kripke. -/
theorem Term.oeqJ_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx (Ty.oeq carrier leftEndpoint rightEndpoint) witnessRaw}
    (baseCaseIsSN : Term.isStronglyNormalizing baseCase)
    (witnessIsSN : Term.isStronglyNormalizing witness) :
    Term.isStronglyNormalizing (Term.oeqJ baseCase witness) :=
  Term.oeqJ_isStronglyNormalizing baseCaseIsSN witnessIsSN

/-- SN of idStrictRec via Kripke. -/
theorem Term.idStrictRec_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (modeIsStrict : mode = Mode.strict)
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {motiveType : Ty level scope}
    {baseRaw witnessRaw : RawTerm scope}
    {baseCase : Term sourceCtx motiveType baseRaw}
    {witness :
      Term sourceCtx
        (Ty.idStrict carrier leftEndpoint rightEndpoint)
        witnessRaw}
    (baseCaseIsSN : Term.isStronglyNormalizing baseCase)
    (witnessIsSN : Term.isStronglyNormalizing witness) :
    Term.isStronglyNormalizing
      (Term.idStrictRec modeIsStrict baseCase witness) :=
  Term.idStrictRec_isStronglyNormalizing modeIsStrict
    baseCaseIsSN witnessIsSN

/-- SN of equivApp via Kripke. -/
theorem Term.equivApp_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {equivRaw argumentRaw : RawTerm scope}
    {equivTerm : Term context (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term context carrierA argumentRaw}
    (equivIsSN : Term.isStronglyNormalizing equivTerm)
    (argumentIsSN : Term.isStronglyNormalizing argumentTerm) :
    Term.isStronglyNormalizing
      (Term.equivApp equivTerm argumentTerm) :=
  Term.equivApp_isStronglyNormalizing equivIsSN argumentIsSN

/-- SN of equivApply via Kripke. -/
theorem Term.equivApply_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {carrierA carrierB : Ty level scope}
    {equivRaw argumentRaw : RawTerm scope}
    {equivTerm : Term context (Ty.equiv carrierA carrierB) equivRaw}
    {argumentTerm : Term context carrierA argumentRaw}
    (equivIsSN : Term.isStronglyNormalizing equivTerm)
    (argumentIsSN : Term.isStronglyNormalizing argumentTerm) :
    Term.isStronglyNormalizing
      (Term.equivApply equivTerm argumentTerm) :=
  Term.equivApply_isStronglyNormalizing equivIsSN argumentIsSN

/-- SN of modElim via Kripke. -/
theorem Term.modElim_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term context innerType innerRaw}
    (innerIsSN : Term.isStronglyNormalizing innerTerm) :
    Term.isStronglyNormalizing (Term.modElim innerTerm) :=
  Term.modElim_isStronglyNormalizing innerIsSN

/-- SN of natElim via Kripke.  Premise `succAppIsSN` is the raw
arrow-application closure for `succRaw` — exactly what
`ReducibleK.arrow_apply` would supply when the full Kripke arrow
closure for `succBranch` lands in Phase B. -/
theorem Term.natElim_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    {scrutinee : Term context Ty.nat scrutineeRaw}
    {zeroBranch : Term context motiveType zeroRaw}
    {succBranch : Term context (Ty.arrow Ty.nat motiveType) succRaw}
    (scrutineeIsSN : Term.isStronglyNormalizing scrutinee)
    (zeroIsSN : Term.isStronglyNormalizing zeroBranch)
    (succIsSN : Term.isStronglyNormalizing succBranch)
    (succAppIsSN :
      ∀ {predecessorRaw : RawTerm scope},
        RawTerm.isStronglyNormalizing predecessorRaw →
        RawTerm.isStronglyNormalizing
          (RawTerm.app succRaw predecessorRaw)) :
    Term.isStronglyNormalizing
      (Term.natElim scrutinee zeroBranch succBranch) :=
  Term.natElim_isStronglyNormalizing
    scrutineeIsSN zeroIsSN succIsSN succAppIsSN

/-- SN of natRec via Kripke.  Same shape as `natElim` plus the
nested-app closure for the recursor contractum. -/
theorem Term.natRec_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {motiveType : Ty level scope}
    {scrutineeRaw zeroRaw succRaw : RawTerm scope}
    {scrutinee : Term context Ty.nat scrutineeRaw}
    {zeroBranch : Term context motiveType zeroRaw}
    {succBranch :
      Term context (Ty.arrow Ty.nat (Ty.arrow motiveType motiveType))
        succRaw}
    (scrutineeIsSN : Term.isStronglyNormalizing scrutinee)
    (zeroIsSN : Term.isStronglyNormalizing zeroBranch)
    (succIsSN : Term.isStronglyNormalizing succBranch)
    (contractumIsSN :
      ∀ {predecessorRaw zeroTargetRaw succTargetRaw : RawTerm scope},
        RawTerm.isStronglyNormalizing predecessorRaw →
        RawTerm.isStronglyNormalizing zeroTargetRaw →
        RawTerm.isStronglyNormalizing succTargetRaw →
        RawTerm.isStronglyNormalizing
          (RawTerm.app (RawTerm.app succTargetRaw predecessorRaw)
            (RawTerm.natRec
              predecessorRaw zeroTargetRaw succTargetRaw))) :
    Term.isStronglyNormalizing
      (Term.natRec scrutinee zeroBranch succBranch) :=
  Term.natRec_isStronglyNormalizing
    scrutineeIsSN zeroIsSN succIsSN contractumIsSN

/-- SN of `Term.interval0` via Kripke.  Closed leaf — no premises. -/
theorem Term.interval0_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    Term.isStronglyNormalizing (Term.interval0 (context := context)) :=
  Term.interval0_isStronglyNormalizing

/-- SN of `Term.interval1` via Kripke.  Closed leaf — no premises. -/
theorem Term.interval1_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope} :
    Term.isStronglyNormalizing (Term.interval1 (context := context)) :=
  Term.interval1_isStronglyNormalizing

/-- SN of `Term.universeCode` via Kripke.  Closed type-code former. -/
theorem Term.universeCode_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    Term.isStronglyNormalizing
      (Term.universeCode (context := context)
        innerLevel outerLevel cumulOk levelLe) :=
  Term.universeCode_isStronglyNormalizing
    innerLevel outerLevel cumulOk levelLe

/-- SN of `Term.piTyCode` via Kripke. -/
theorem Term.piTyCode_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {domainCodeRaw : RawTerm scope}
    {codomainCodeRaw : RawTerm (scope + 1)}
    (domainCodeIsSN : RawTerm.isStronglyNormalizing domainCodeRaw)
    (codomainCodeIsSN : RawTerm.isStronglyNormalizing codomainCodeRaw) :
    Term.isStronglyNormalizing
      (Term.piTyCode (context := context)
        outerLevel levelLe domainCodeRaw codomainCodeRaw) :=
  Term.piTyCode_isStronglyNormalizing outerLevel levelLe
    domainCodeIsSN codomainCodeIsSN

/-- SN of `Term.sigmaTyCode` via Kripke. -/
theorem Term.sigmaTyCode_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {domainCodeRaw : RawTerm scope}
    {codomainCodeRaw : RawTerm (scope + 1)}
    (domainCodeIsSN : RawTerm.isStronglyNormalizing domainCodeRaw)
    (codomainCodeIsSN : RawTerm.isStronglyNormalizing codomainCodeRaw) :
    Term.isStronglyNormalizing
      (Term.sigmaTyCode (context := context)
        outerLevel levelLe domainCodeRaw codomainCodeRaw) :=
  Term.sigmaTyCode_isStronglyNormalizing outerLevel levelLe
    domainCodeIsSN codomainCodeIsSN

/-- SN of `Term.productCode` via Kripke. -/
theorem Term.productCode_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {firstCodeRaw secondCodeRaw : RawTerm scope}
    (firstCodeIsSN : RawTerm.isStronglyNormalizing firstCodeRaw)
    (secondCodeIsSN : RawTerm.isStronglyNormalizing secondCodeRaw) :
    Term.isStronglyNormalizing
      (Term.productCode (context := context)
        outerLevel levelLe firstCodeRaw secondCodeRaw) :=
  Term.productCode_isStronglyNormalizing outerLevel levelLe
    firstCodeIsSN secondCodeIsSN

/-- SN of `Term.sumCode` via Kripke. -/
theorem Term.sumCode_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftCodeRaw rightCodeRaw : RawTerm scope}
    (leftCodeIsSN : RawTerm.isStronglyNormalizing leftCodeRaw)
    (rightCodeIsSN : RawTerm.isStronglyNormalizing rightCodeRaw) :
    Term.isStronglyNormalizing
      (Term.sumCode (context := context)
        outerLevel levelLe leftCodeRaw rightCodeRaw) :=
  Term.sumCode_isStronglyNormalizing outerLevel levelLe
    leftCodeIsSN rightCodeIsSN

/-- SN of `Term.funextIntroHet` via Kripke. -/
theorem Term.funextIntroHet_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    {applyARaw applyBRaw : RawTerm (scope + 1)}
    (applyAIsSN : RawTerm.isStronglyNormalizing applyARaw) :
    Term.isStronglyNormalizing
      (Term.funextIntroHet (context := context)
        domainType codomainType applyARaw applyBRaw) :=
  Term.funextIntroHet_isStronglyNormalizing
    domainType codomainType applyAIsSN

/-- SN of `Term.codataDest` via Kripke.  Requires the contractum-SN
closure for the β-fire `codataDest (codataUnfold s t) → app t s`. -/
theorem Term.codataDest_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {codataRaw : RawTerm scope}
    {codataValue :
      Term context (Ty.codata stateType outputType) codataRaw}
    (codataIsSN : Term.isStronglyNormalizing codataValue)
    (contractumIsSN :
      ∀ {stateRaw transitionRaw : RawTerm scope},
        RawTerm.isStronglyNormalizing stateRaw →
        RawTerm.isStronglyNormalizing transitionRaw →
        RawTerm.isStronglyNormalizing
          (RawTerm.app transitionRaw stateRaw)) :
    Term.isStronglyNormalizing (Term.codataDest codataValue) :=
  Term.codataDest_isStronglyNormalizing codataIsSN contractumIsSN

/-- SN of `Term.listElim` via Kripke.  Requires the contractum-SN
closure for the cons-ι fire `listElim (listCons h t) n c →
app (app c h) t`. -/
theorem Term.listElim_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw nilRaw consRaw : RawTerm scope}
    {scrutinee : Term context (Ty.listType elementType) scrutineeRaw}
    {nilBranch : Term context motiveType nilRaw}
    {consBranch : Term context (Ty.arrow elementType
                                  (Ty.arrow (Ty.listType elementType)
                                    motiveType)) consRaw}
    (scrutineeIsSN : Term.isStronglyNormalizing scrutinee)
    (nilIsSN : Term.isStronglyNormalizing nilBranch)
    (consIsSN : Term.isStronglyNormalizing consBranch)
    (contractumIsSN :
      ∀ {headRaw tailRaw consTargetRaw : RawTerm scope},
        RawTerm.isStronglyNormalizing headRaw →
        RawTerm.isStronglyNormalizing tailRaw →
        RawTerm.isStronglyNormalizing consTargetRaw →
        RawTerm.isStronglyNormalizing
          (RawTerm.app (RawTerm.app consTargetRaw headRaw) tailRaw)) :
    Term.isStronglyNormalizing
      (Term.listElim scrutinee nilBranch consBranch) :=
  Term.listElim_isStronglyNormalizing
    scrutineeIsSN nilIsSN consIsSN contractumIsSN

/-- SN of `Term.optionMatch` via Kripke.  Requires the contractum-SN
closure for the some-ι fire `optionMatch (optionSome v) n s →
app s v`. -/
theorem Term.optionMatch_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw noneRaw someRaw : RawTerm scope}
    {scrutinee : Term context (Ty.optionType elementType) scrutineeRaw}
    {noneBranch : Term context motiveType noneRaw}
    {someBranch : Term context (Ty.arrow elementType motiveType) someRaw}
    (scrutineeIsSN : Term.isStronglyNormalizing scrutinee)
    (noneIsSN : Term.isStronglyNormalizing noneBranch)
    (someIsSN : Term.isStronglyNormalizing someBranch)
    (contractumIsSN :
      ∀ {valueRaw someTargetRaw : RawTerm scope},
        RawTerm.isStronglyNormalizing valueRaw →
        RawTerm.isStronglyNormalizing someTargetRaw →
        RawTerm.isStronglyNormalizing
          (RawTerm.app someTargetRaw valueRaw)) :
    Term.isStronglyNormalizing
      (Term.optionMatch scrutinee noneBranch someBranch) :=
  Term.optionMatch_isStronglyNormalizing
    scrutineeIsSN noneIsSN someIsSN contractumIsSN

/-- SN of `Term.eitherMatch` via Kripke.  Requires a pair of
contractum-SN closures for the two ι fires:
`eitherMatch (eitherInl v) l r → app l v` and the inr-symmetric arm. -/
theorem Term.eitherMatch_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftType rightType motiveType : Ty level scope}
    {scrutineeRaw leftRaw rightRaw : RawTerm scope}
    {scrutinee :
      Term context (Ty.eitherType leftType rightType) scrutineeRaw}
    {leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw}
    {rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw}
    (scrutineeIsSN : Term.isStronglyNormalizing scrutinee)
    (leftIsSN : Term.isStronglyNormalizing leftBranch)
    (rightIsSN : Term.isStronglyNormalizing rightBranch)
    (inlContractumIsSN :
      ∀ {valueRaw leftTargetRaw : RawTerm scope},
        RawTerm.isStronglyNormalizing valueRaw →
        RawTerm.isStronglyNormalizing leftTargetRaw →
        RawTerm.isStronglyNormalizing
          (RawTerm.app leftTargetRaw valueRaw))
    (inrContractumIsSN :
      ∀ {valueRaw rightTargetRaw : RawTerm scope},
        RawTerm.isStronglyNormalizing valueRaw →
        RawTerm.isStronglyNormalizing rightTargetRaw →
        RawTerm.isStronglyNormalizing
          (RawTerm.app rightTargetRaw valueRaw)) :
    Term.isStronglyNormalizing
      (Term.eitherMatch scrutinee leftBranch rightBranch) :=
  Term.eitherMatch_isStronglyNormalizing
    scrutineeIsSN leftIsSN rightIsSN inlContractumIsSN inrContractumIsSN

/-- SN of `Term.app` via Kripke.  Requires the contractum-SN closure
for the β arm `app (lam body) arg → body[arg/0]`. -/
theorem Term.app_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {functionRaw argumentRaw : RawTerm scope}
    {functionTerm :
      Term context (Ty.arrow domainType codomainType) functionRaw}
    {argumentTerm : Term context domainType argumentRaw}
    (functionIsSN : Term.isStronglyNormalizing functionTerm)
    (argumentIsSN : Term.isStronglyNormalizing argumentTerm)
    (contractumIsSN :
      ∀ {bodyTargetRaw : RawTerm (scope + 1)}
          {argumentTargetRaw : RawTerm scope},
        RawTerm.isStronglyNormalizing bodyTargetRaw →
        RawTerm.isStronglyNormalizing argumentTargetRaw →
        RawTerm.isStronglyNormalizing
          (bodyTargetRaw.subst0 argumentTargetRaw)) :
    Term.isStronglyNormalizing (Term.app functionTerm argumentTerm) :=
  Term.app_isStronglyNormalizing
    functionIsSN argumentIsSN contractumIsSN

/-- SN of `Term.appPi` via Kripke.  Dependent-Π elimination sharing
raw β with `Term.app`. -/
theorem Term.appPi_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {functionRaw argumentRaw : RawTerm scope}
    {functionTerm :
      Term context (Ty.piTy domainType codomainType) functionRaw}
    {argumentTerm : Term context domainType argumentRaw}
    (functionIsSN : Term.isStronglyNormalizing functionTerm)
    (argumentIsSN : Term.isStronglyNormalizing argumentTerm)
    (contractumIsSN :
      ∀ {bodyTargetRaw : RawTerm (scope + 1)}
          {argumentTargetRaw : RawTerm scope},
        RawTerm.isStronglyNormalizing bodyTargetRaw →
        RawTerm.isStronglyNormalizing argumentTargetRaw →
        RawTerm.isStronglyNormalizing
          (bodyTargetRaw.subst0 argumentTargetRaw)) :
    Term.isStronglyNormalizing (Term.appPi functionTerm argumentTerm) :=
  Term.appPi_isStronglyNormalizing
    functionIsSN argumentIsSN contractumIsSN

/-- **K12.24 Kripke SN headline for pathApp** — cubical-mode path
application via Kripke step-indexed reducibility.  Delegates to the
fundamental theorem; the contractum closure handles the β arm
`pathApp (pathLam body) interval ⇒ body.subst0 interval`. -/
theorem Term.pathApp_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {pathRaw intervalRaw : RawTerm scope}
    {pathTerm :
      Term context (Ty.path carrierType leftEndpoint rightEndpoint) pathRaw}
    {intervalTerm : Term context Ty.interval intervalRaw}
    (pathIsSN : Term.isStronglyNormalizing pathTerm)
    (intervalIsSN : Term.isStronglyNormalizing intervalTerm)
    (contractumIsSN :
      ∀ {bodyTargetRaw : RawTerm (scope + 1)}
          {intervalTargetRaw : RawTerm scope},
        RawTerm.isStronglyNormalizing bodyTargetRaw →
        RawTerm.isStronglyNormalizing intervalTargetRaw →
        RawTerm.isStronglyNormalizing
          (bodyTargetRaw.subst0 intervalTargetRaw)) :
    Term.isStronglyNormalizing
      (Term.pathApp modeIsUnivalent pathTerm intervalTerm) :=
  Term.pathApp_isStronglyNormalizing modeIsUnivalent
    pathIsSN intervalIsSN contractumIsSN

/-- **K12.24 Kripke SN headline for transp**.  Requires contractum-SN
closures for univalence transport and path-composition transport; the
constant-path computational arm returns the transported source directly. -/
theorem Term.transp_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    (universeLevel : UniverseLevel)
    (universeLevelLt : universeLevel.toNat + 1 ≤ level)
    (sourceType targetType : Ty level scope)
    (sourceTypeRaw targetTypeRaw : RawTerm scope)
    {pathRaw sourceRaw : RawTerm scope}
    {typePath :
      Term context
        (Ty.path (Ty.universe universeLevel universeLevelLt)
          sourceTypeRaw targetTypeRaw)
        pathRaw}
    {sourceValue : Term context sourceType sourceRaw}
    (pathIsSN : Term.isStronglyNormalizing typePath)
    (sourceIsSN : Term.isStronglyNormalizing sourceValue)
    (uaContractumIsSN :
      ∀ {equivRaw sourceTargetRaw : RawTerm scope},
        RawTerm.isStronglyNormalizing equivRaw →
        RawTerm.isStronglyNormalizing sourceTargetRaw →
        RawTerm.isStronglyNormalizing
          (RawTerm.equivApply equivRaw sourceTargetRaw))
    (composeContractumIsSN :
      ∀ {leftPathRaw rightPathRaw sourceTargetRaw : RawTerm scope},
        RawTerm.isStronglyNormalizing
          (RawTerm.pathCompose leftPathRaw rightPathRaw) →
        RawTerm.isStronglyNormalizing sourceTargetRaw →
        RawTerm.isStronglyNormalizing
          (RawTerm.transp rightPathRaw
            (RawTerm.transp leftPathRaw sourceTargetRaw))) :
    Term.isStronglyNormalizing
      (Term.transp modeIsUnivalent universeLevel universeLevelLt
        sourceType targetType sourceTypeRaw targetTypeRaw
        typePath sourceValue) :=
  Term.transp_isStronglyNormalizing modeIsUnivalent universeLevel
    universeLevelLt sourceType targetType sourceTypeRaw targetTypeRaw
    pathIsSN sourceIsSN uaContractumIsSN composeContractumIsSN

/-- **K12.24 Kripke SN headline for hcomp**.  At the current raw layer,
`hcomp` is congruence-only; the future boundary-computation rule is tracked
outside this headline. -/
theorem Term.hcomp_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    (modeIsUnivalent : mode = Mode.univalent)
    {carrierType : Ty level scope}
    {sidesRaw capRaw : RawTerm scope}
    {sidesValue : Term context carrierType sidesRaw}
    {capValue : Term context carrierType capRaw}
    (sidesIsSN : Term.isStronglyNormalizing sidesValue)
    (capIsSN : Term.isStronglyNormalizing capValue) :
    Term.isStronglyNormalizing
      (Term.hcomp modeIsUnivalent sidesValue capValue) :=
  Term.hcomp_isStronglyNormalizing modeIsUnivalent sidesIsSN capIsSN

end LeanFX2
