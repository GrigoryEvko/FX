import LeanFX2.Reducibility.Kripke.Project
import LeanFX2.Reducibility.Kripke.Fundamental
import LeanFX2.Reducibility.Kripke.Arrow
import LeanFX2.Reducibility.Kripke.SNExtraction

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

/-! ## Deferred Kripke SN headlines — natElim / natRec

Earlier this file shipped `Term.natElim_strong_normalization_via_kripke`
and `Term.natRec_strong_normalization_via_kripke` as theorems with a
universally-quantified `succAppIsSN` / `contractumIsSN` postulate
hypothesis describing the raw ι contractum's SN status.  Per the
project's "hypothesis-as-postulate is BANNED" rule, those theorems
were vacuous-by-input on raw terms the kernel cannot construct; they
have been DELETED.

The honest path to non-vacuous Kripke SN of natElim / natRec is the
M04 fundamental strong-normalization theorem, which proves
reducibility by induction on the typing derivation.  That theorem
backward-closes the Ty.nat predicate under ι reduction, so it
discharges the contractum-SN obligation as a real consequence (not a
hypothesis).  Until M04 lands, these eliminator headlines remain
deferred — there is no shorter honest route.

The closed-leaf SN status of natZero (and natSucc preservation) is
unaffected and remains shipped via the direct cascade above. -/

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

/-- **SN of `Term.codataDest` via Kripke (real Tait pattern, no
`contractumIsSN` postulate)**.  Takes the codata value's reducibility
at `Ty.codata stateType outputType`, applies the codata closure
clause at identity renaming via `ReducibleK.codata_dest`, and projects
SN via `sn_of_any`. -/
theorem Term.codataDest_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stateType outputType : Ty level scope}
    {codataRaw : RawTerm scope}
    {codataValue :
      Term context (Ty.codata stateType outputType) codataRaw}
    {stepCount : Nat}
    (codataIsR :
      @ReducibleK mode level scope context (stepCount + 2)
        (Ty.codata stateType outputType) codataRaw codataValue) :
    Term.isStronglyNormalizing (Term.codataDest codataValue) := by
  have destIsR :=
    ReducibleK.codata_dest codataIsR (TermRenaming.identity context)
  have destIsSN := ReducibleK.sn_of_any destIsR
  show RawTerm.isStronglyNormalizing (RawTerm.codataDest codataRaw)
  have rawDestEq :
      RawTerm.codataDest (codataRaw.rename RawRenaming.identity)
        = RawTerm.codataDest codataRaw := by
    rw [RawTerm.rename_identity codataRaw]
  exact rawDestEq ▸ destIsSN

/-- **SN of `Term.listElim` via Kripke (real Tait pattern, no
`contractumIsSN` postulate)**.  Takes ReducibleK premises on the
scrutinee at `Ty.listType A`, the nilBranch at the motive, and the
consBranch at `Ty.arrow A (Ty.arrow (Ty.listType A) motive)`;
applies the list ι-closure at identity renaming via
`ReducibleK.listType_elim`; projects SN via `sn_of_any`.  The
`elementType.rename identity = elementType` rewrite is dispatched
through `ReducibleK.transport` on the cons branch's arrow shape. -/
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
    {stepCount : Nat}
    (scrutineeIsR :
      @ReducibleK mode level scope context (stepCount + 2)
        (Ty.listType elementType) scrutineeRaw scrutinee)
    (nilIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        motiveType nilRaw nilBranch)
    (consIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.arrow elementType (Ty.arrow (Ty.listType elementType) motiveType))
        consRaw consBranch) :
    Term.isStronglyNormalizing
      (Term.listElim scrutinee nilBranch consBranch) := by
  -- The closure clause expects the consBranch's domain `elementType`
  -- to be renamed at identity.  Cast through `Ty.rename_identity`.
  have consTyEq :
      Ty.arrow elementType
          (Ty.arrow (Ty.listType elementType) motiveType)
        =
      Ty.arrow (elementType.rename RawRenaming.identity)
          (Ty.arrow (Ty.listType (elementType.rename RawRenaming.identity))
            motiveType) := by
    rw [Ty.rename_identity elementType]
  have elimIsR :=
    ReducibleK.listType_elim scrutineeIsR
      (TermRenaming.identity context) motiveType
      nilBranch (consTyEq ▸ consBranch)
      nilIsR (ReducibleK.transport consTyEq consIsR)
  have elimIsSN := ReducibleK.sn_of_any elimIsR
  show RawTerm.isStronglyNormalizing
        (RawTerm.listElim scrutineeRaw nilRaw consRaw)
  have rawElimEq :
      RawTerm.listElim (scrutineeRaw.rename RawRenaming.identity)
          nilRaw consRaw
        = RawTerm.listElim scrutineeRaw nilRaw consRaw := by
    rw [RawTerm.rename_identity scrutineeRaw]
  exact rawElimEq ▸ elimIsSN

/-- **SN of `Term.optionMatch` via Kripke (real Tait pattern, no
`contractumIsSN` postulate)**.  Same shape as `listElim` strip: takes
ReducibleK premises on scrutinee/noneBranch/someBranch, applies the
option ι-closure at identity via `ReducibleK.optionType_match`,
projects SN through `sn_of_any`. -/
theorem Term.optionMatch_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {elementType motiveType : Ty level scope}
    {scrutineeRaw noneRaw someRaw : RawTerm scope}
    {scrutinee : Term context (Ty.optionType elementType) scrutineeRaw}
    {noneBranch : Term context motiveType noneRaw}
    {someBranch : Term context (Ty.arrow elementType motiveType) someRaw}
    {stepCount : Nat}
    (scrutineeIsR :
      @ReducibleK mode level scope context (stepCount + 2)
        (Ty.optionType elementType) scrutineeRaw scrutinee)
    (noneIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        motiveType noneRaw noneBranch)
    (someIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.arrow elementType motiveType) someRaw someBranch) :
    Term.isStronglyNormalizing
      (Term.optionMatch scrutinee noneBranch someBranch) := by
  have someTyEq :
      Ty.arrow elementType motiveType
        =
      Ty.arrow (elementType.rename RawRenaming.identity) motiveType := by
    rw [Ty.rename_identity elementType]
  have matchIsR :=
    ReducibleK.optionType_match scrutineeIsR
      (TermRenaming.identity context) motiveType
      noneBranch (someTyEq ▸ someBranch)
      noneIsR (ReducibleK.transport someTyEq someIsR)
  have matchIsSN := ReducibleK.sn_of_any matchIsR
  show RawTerm.isStronglyNormalizing
        (RawTerm.optionMatch scrutineeRaw noneRaw someRaw)
  have rawMatchEq :
      RawTerm.optionMatch (scrutineeRaw.rename RawRenaming.identity)
          noneRaw someRaw
        = RawTerm.optionMatch scrutineeRaw noneRaw someRaw := by
    rw [RawTerm.rename_identity scrutineeRaw]
  exact rawMatchEq ▸ matchIsSN

/-- **SN of `Term.eitherMatch` via Kripke (real Tait pattern, no
`contractumIsSN` postulates)**.  Same shape as `listElim`/`optionMatch`
strips: takes ReducibleK premises on scrutinee/leftBranch/rightBranch,
applies the either ι-closure at identity via
`ReducibleK.eitherType_match`, projects SN through `sn_of_any`.  The
two contractumIsSN postulates (one per inl/inr arm) are eliminated
together because the closure clause bakes both into its single
reducibility output. -/
theorem Term.eitherMatch_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {leftType rightType motiveType : Ty level scope}
    {scrutineeRaw leftRaw rightRaw : RawTerm scope}
    {scrutinee :
      Term context (Ty.eitherType leftType rightType) scrutineeRaw}
    {leftBranch : Term context (Ty.arrow leftType motiveType) leftRaw}
    {rightBranch : Term context (Ty.arrow rightType motiveType) rightRaw}
    {stepCount : Nat}
    (scrutineeIsR :
      @ReducibleK mode level scope context (stepCount + 2)
        (Ty.eitherType leftType rightType) scrutineeRaw scrutinee)
    (leftIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.arrow leftType motiveType) leftRaw leftBranch)
    (rightIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.arrow rightType motiveType) rightRaw rightBranch) :
    Term.isStronglyNormalizing
      (Term.eitherMatch scrutinee leftBranch rightBranch) := by
  have leftTyEq :
      Ty.arrow leftType motiveType
        =
      Ty.arrow (leftType.rename RawRenaming.identity) motiveType := by
    rw [Ty.rename_identity leftType]
  have rightTyEq :
      Ty.arrow rightType motiveType
        =
      Ty.arrow (rightType.rename RawRenaming.identity) motiveType := by
    rw [Ty.rename_identity rightType]
  have matchIsR :=
    ReducibleK.eitherType_match scrutineeIsR
      (TermRenaming.identity context) motiveType
      (leftTyEq ▸ leftBranch) (rightTyEq ▸ rightBranch)
      (ReducibleK.transport leftTyEq leftIsR)
      (ReducibleK.transport rightTyEq rightIsR)
  have matchIsSN := ReducibleK.sn_of_any matchIsR
  show RawTerm.isStronglyNormalizing
        (RawTerm.eitherMatch scrutineeRaw leftRaw rightRaw)
  have rawMatchEq :
      RawTerm.eitherMatch (scrutineeRaw.rename RawRenaming.identity)
          leftRaw rightRaw
        = RawTerm.eitherMatch scrutineeRaw leftRaw rightRaw := by
    rw [RawTerm.rename_identity scrutineeRaw]
  exact rawMatchEq ▸ matchIsSN

/-- **SN of `Term.app` via Kripke (real Tait pattern, no
`contractumIsSN` postulate)**.  Takes the FUNCTION'S reducibility at
`Ty.arrow A B` and the ARGUMENT'S reducibility at `A`, applies the
arrow-closure clause at identity renaming, projects via `sn_of_any`
to SN of the resulting (renamed) application, and rewrites the
residual `RawTerm.rename_identity` on the function subterm to
recover SN of `Term.app functionTerm argumentTerm`.

The premises are `ReducibleK` rather than `Term.isStronglyNormalizing`
because the arrow closure clause demands reducibility of the argument
to produce reducibility of the application — pure Tait pattern, not
hypothesis-as-postulate. -/
theorem Term.app_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType codomainType : Ty level scope}
    {functionRaw argumentRaw : RawTerm scope}
    {functionTerm :
      Term context (Ty.arrow domainType codomainType) functionRaw}
    {argumentTerm : Term context domainType argumentRaw}
    {stepCount : Nat}
    (functionIsR :
      @ReducibleK mode level scope context (stepCount + 2)
        (Ty.arrow domainType codomainType) functionRaw functionTerm)
    (argumentIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        domainType argumentRaw argumentTerm) :
    Term.isStronglyNormalizing (Term.app functionTerm argumentTerm) := by
  -- Generalize over the renamed-domain index via `Ty.rename_identity`
  -- so the arrow-closure's renamed-domain argument lines up with
  -- `argumentTerm : Term context domainType argRaw`.  Using `subst`
  -- on the equation transports both `argumentTerm` and `argumentIsR`
  -- to the renamed-domain side simultaneously, eliminating the
  -- separate `▸` casts and the resulting double-rename motive.
  have domainRenameEq : domainType = domainType.rename RawRenaming.identity :=
    (Ty.rename_identity domainType).symm
  -- Apply arrow closure: it returns reducibility at
  -- `codomainType.rename identity` of the renamed-function applied
  -- to argumentTerm (cast to renamed domain).
  have appIsR :=
    ReducibleK.arrow_apply functionIsR
      (TermRenaming.identity context)
      (domainRenameEq ▸ argumentTerm)
      (ReducibleK.transport domainRenameEq argumentIsR)
  -- Project to SN via the universal dispatcher.
  have appIsSN := ReducibleK.sn_of_any appIsR
  -- Unfold typed SN to raw SN, then rewrite the residual
  -- `functionRaw.rename identity` back to `functionRaw`.
  show RawTerm.isStronglyNormalizing (RawTerm.app functionRaw argumentRaw)
  have rawAppEq :
      RawTerm.app (functionRaw.rename RawRenaming.identity) argumentRaw
        = RawTerm.app functionRaw argumentRaw := by
    rw [RawTerm.rename_identity functionRaw]
  exact rawAppEq ▸ appIsSN

/-- **SN of `Term.appPi` via Kripke (real Tait pattern, no
`contractumIsSN` postulate)**.  Dependent-Π elimination — same shape
as `Term.app_strong_normalization_via_kripke` modulo `piTy_apply`
instead of `arrow_apply` (the closure clause's output type carries a
substitution rather than a renaming since the codomain depends on
the argument). -/
theorem Term.appPi_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {domainType : Ty level scope}
    {codomainType : Ty level (scope + 1)}
    {functionRaw argumentRaw : RawTerm scope}
    {functionTerm :
      Term context (Ty.piTy domainType codomainType) functionRaw}
    {argumentTerm : Term context domainType argumentRaw}
    {stepCount : Nat}
    (functionIsR :
      @ReducibleK mode level scope context (stepCount + 2)
        (Ty.piTy domainType codomainType) functionRaw functionTerm)
    (argumentIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        domainType argumentRaw argumentTerm) :
    Term.isStronglyNormalizing (Term.appPi functionTerm argumentTerm) := by
  have domainRenameEq : domainType = domainType.rename RawRenaming.identity :=
    (Ty.rename_identity domainType).symm
  have appIsR :=
    ReducibleK.piTy_apply functionIsR
      (TermRenaming.identity context)
      (domainRenameEq ▸ argumentTerm)
      (ReducibleK.transport domainRenameEq argumentIsR)
  have appIsSN := ReducibleK.sn_of_any appIsR
  show RawTerm.isStronglyNormalizing (RawTerm.app functionRaw argumentRaw)
  have rawAppEq :
      RawTerm.app (functionRaw.rename RawRenaming.identity) argumentRaw
        = RawTerm.app functionRaw argumentRaw := by
    rw [RawTerm.rename_identity functionRaw]
  exact rawAppEq ▸ appIsSN

/-- **K12.24 Kripke SN headline for pathApp** — cubical-mode path
application via Kripke step-indexed reducibility (real Tait pattern,
no `contractumIsSN` postulate).  Takes the PATH'S reducibility at
`Ty.path C l r` and the INTERVAL's reducibility at `Ty.interval`,
applies the path closure clause at identity renaming, and projects
SN via `sn_of_any`. -/
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
    {stepCount : Nat}
    (pathIsR :
      @ReducibleK mode level scope context (stepCount + 2)
        (Ty.path carrierType leftEndpoint rightEndpoint) pathRaw pathTerm)
    (intervalIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        Ty.interval intervalRaw intervalTerm) :
    Term.isStronglyNormalizing
      (Term.pathApp modeIsUnivalent pathTerm intervalTerm) := by
  -- Apply the path closure (intervalTerm has type `Ty.interval`, which
  -- is scope-polymorphic and renames to itself, so no cast is needed
  -- on the argument side).
  have appIsR :=
    pathIsR.2 modeIsUnivalent
      (TermRenaming.identity context) intervalTerm intervalIsR
  have appIsSN := ReducibleK.sn_of_any appIsR
  show RawTerm.isStronglyNormalizing
        (RawTerm.pathApp pathRaw intervalRaw)
  have rawPathAppEq :
      RawTerm.pathApp (pathRaw.rename RawRenaming.identity) intervalRaw
        = RawTerm.pathApp pathRaw intervalRaw := by
    rw [RawTerm.rename_identity pathRaw]
  exact rawPathAppEq ▸ appIsSN

/-! ## Deferred Kripke SN headlines — transp / hcomp

Earlier this file shipped `Term.transp_strong_normalization_via_kripke`
with `uaContractumIsSN` + `composeContractumIsSN` postulates and a
trivial `Term.hcomp_strong_normalization_via_kripke` (no cubical β
rule yet exists — `Step.hcompBeta` is tracked pending under #1528).

Both have been DELETED.  The `transp` headline shipped a banned
hypothesis-as-postulate over universe-quantified raw `equivApply` /
`transp` contractum shapes the kernel cannot construct; the `hcomp`
headline, while postulate-free, was congruence-only and added no
information beyond `Term.hcomp_isStronglyNormalizing` (the underlying
SN helper that ships as a Term-level theorem with a real body).

The honest path is the M04 fundamental theorem combined with the
landed `Step.transpUaBeta` / `Step.transpCompose` / `Step.hcompBeta`
computational reductions.  Once both ship, these Kripke headlines
return as proper consequences. -/

end LeanFX2
