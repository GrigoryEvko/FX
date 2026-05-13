import LeanFX2.Reducibility.FundamentalAliases.RawPayloads

/-! # LeanFX2.Reducibility.FundamentalAliases.M04Cases

K12.27 direct M04 endpoints — base-case SN witnesses (unit,
boolTrue, boolFalse, natZero, intervals, universe code, etc.)
plus the recursive-intro M04 endpoints (lam, pair, listCons,
optionSome, natSucc, eitherInl/Inr, refl trinity) plus the
congruence-form closures.

## Root status

Layer 3 metatheory leaf.  Third slice of FundamentalAliases. -/

namespace LeanFX2



/-! ## K12.27 direct leaf M04 endpoints -/

/-- Direct M04 SN case for typed variables. -/
theorem Term.var_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (position : Fin scope) :
    Term.isStronglyNormalizing
      (Term.var (context := sourceCtx) position) :=
  RawTerm.var_isStronglyNormalizing position

/-- Direct M04 SN case for the unit value. -/
theorem Term.unit_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope} :
    Term.isStronglyNormalizing
      (Term.unit (context := sourceCtx)) :=
  RawTerm.unit_isStronglyNormalizing

/-- Direct M04 SN case for `true`. -/
theorem Term.boolTrue_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope} :
    Term.isStronglyNormalizing
      (Term.boolTrue (context := sourceCtx)) :=
  RawTerm.boolTrue_isStronglyNormalizing

/-- Direct M04 SN case for `false`. -/
theorem Term.boolFalse_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope} :
    Term.isStronglyNormalizing
      (Term.boolFalse (context := sourceCtx)) :=
  RawTerm.boolFalse_isStronglyNormalizing

/-- Direct M04 SN case for zero. -/
theorem Term.natZero_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope} :
    Term.isStronglyNormalizing
      (Term.natZero (context := sourceCtx)) :=
  RawTerm.natZero_isStronglyNormalizing

/-- Direct M04 SN case for the empty list. -/
theorem Term.listNil_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {elementType : Ty level scope} :
    Term.isStronglyNormalizing
      (Term.listNil (context := sourceCtx)
        (elementType := elementType)) :=
  RawTerm.listNil_isStronglyNormalizing

/-- Direct M04 SN case for `None`. -/
theorem Term.optionNone_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {elementType : Ty level scope} :
    Term.isStronglyNormalizing
      (Term.optionNone (context := sourceCtx)
        (elementType := elementType)) :=
  RawTerm.optionNone_isStronglyNormalizing

/-- Direct M04 SN case for the left interval endpoint. -/
theorem Term.interval0_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope} :
    Term.isStronglyNormalizing
      (Term.interval0 (context := sourceCtx)) :=
  RawTerm.interval0_isStronglyNormalizing

/-- Direct M04 SN case for the right interval endpoint. -/
theorem Term.interval1_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope} :
    Term.isStronglyNormalizing
      (Term.interval1 (context := sourceCtx)) :=
  RawTerm.interval1_isStronglyNormalizing

/-! ## K12.27 direct recursive-intro M04 endpoints -/

/-- Direct M04 SN case for successor. -/
theorem Term.natSucc_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {predecessorRaw : RawTerm scope}
    {predecessor : Term sourceCtx Ty.nat predecessorRaw}
    (predecessorIsSN : Term.isStronglyNormalizing predecessor) :
    Term.isStronglyNormalizing (Term.natSucc predecessor) :=
  RawTerm.natSucc_isStronglyNormalizing predecessorIsSN

/-- Direct M04 SN case for list cons. -/
theorem Term.listCons_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {elementType : Ty level scope}
    {headRaw tailRaw : RawTerm scope}
    {headTerm : Term sourceCtx elementType headRaw}
    {tailTerm : Term sourceCtx (Ty.listType elementType) tailRaw}
    (headIsSN : Term.isStronglyNormalizing headTerm)
    (tailIsSN : Term.isStronglyNormalizing tailTerm) :
    Term.isStronglyNormalizing
      (Term.listCons headTerm tailTerm) :=
  RawTerm.listCons_isStronglyNormalizing headIsSN tailIsSN

/-- Direct M04 SN case for `Some`. -/
theorem Term.optionSome_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {elementType : Ty level scope}
    {valueRaw : RawTerm scope}
    {valueTerm : Term sourceCtx elementType valueRaw}
    (valueIsSN : Term.isStronglyNormalizing valueTerm) :
    Term.isStronglyNormalizing (Term.optionSome valueTerm) :=
  RawTerm.optionSome_isStronglyNormalizing valueIsSN

/-- Direct M04 SN case for left injection. -/
theorem Term.eitherInl_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {valueRaw : RawTerm scope}
    {valueTerm : Term sourceCtx leftType valueRaw}
    (valueIsSN : Term.isStronglyNormalizing valueTerm) :
    Term.isStronglyNormalizing
      (Term.eitherInl (rightType := rightType) valueTerm) :=
  RawTerm.eitherInl_isStronglyNormalizing valueIsSN

/-- Direct M04 SN case for right injection. -/
theorem Term.eitherInr_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {leftType rightType : Ty level scope}
    {valueRaw : RawTerm scope}
    {valueTerm : Term sourceCtx rightType valueRaw}
    (valueIsSN : Term.isStronglyNormalizing valueTerm) :
    Term.isStronglyNormalizing
      (Term.eitherInr (leftType := leftType) valueTerm) :=
  RawTerm.eitherInr_isStronglyNormalizing valueIsSN

/-- Direct M04 SN case for interval negation. -/
theorem Term.intervalOpp_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {innerRaw : RawTerm scope}
    {innerValue : Term sourceCtx Ty.interval innerRaw}
    (innerIsSN : Term.isStronglyNormalizing innerValue) :
    Term.isStronglyNormalizing (Term.intervalOpp innerValue) :=
  RawTerm.intervalOpp_isStronglyNormalizing innerIsSN

/-- Direct M04 SN case for interval meet. -/
theorem Term.intervalMeet_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {leftRaw rightRaw : RawTerm scope}
    {leftValue : Term sourceCtx Ty.interval leftRaw}
    {rightValue : Term sourceCtx Ty.interval rightRaw}
    (leftIsSN : Term.isStronglyNormalizing leftValue)
    (rightIsSN : Term.isStronglyNormalizing rightValue) :
    Term.isStronglyNormalizing
      (Term.intervalMeet leftValue rightValue) :=
  RawTerm.intervalMeet_isStronglyNormalizing leftIsSN rightIsSN

/-- Direct M04 SN case for interval join. -/
theorem Term.intervalJoin_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {leftRaw rightRaw : RawTerm scope}
    {leftValue : Term sourceCtx Ty.interval leftRaw}
    {rightValue : Term sourceCtx Ty.interval rightRaw}
    (leftIsSN : Term.isStronglyNormalizing leftValue)
    (rightIsSN : Term.isStronglyNormalizing rightValue) :
    Term.isStronglyNormalizing
      (Term.intervalJoin leftValue rightValue) :=
  RawTerm.intervalJoin_isStronglyNormalizing leftIsSN rightIsSN

/-- Direct M04 SN case for modal introduction. -/
theorem Term.modIntro_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx innerType innerRaw}
    (innerIsSN : Term.isStronglyNormalizing innerTerm) :
    Term.isStronglyNormalizing (Term.modIntro innerTerm) :=
  RawTerm.modIntro_isStronglyNormalizing innerIsSN

/-- Direct M04 SN case for modal subsumption. -/
theorem Term.subsume_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx innerType innerRaw}
    (innerIsSN : Term.isStronglyNormalizing innerTerm) :
    Term.isStronglyNormalizing (Term.subsume innerTerm) :=
  RawTerm.subsume_isStronglyNormalizing innerIsSN

/-! ## K12.27 direct congruence-form M04 endpoints -/

/-- Direct M04 SN case for observational funext. -/
theorem Term.oeqFunext_isStronglyNormalizing
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
  RawTerm.oeqFunext_isStronglyNormalizing pointwiseIsSN

/-- Direct M04 SN case for session receive. -/
theorem Term.sessionRecv_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {protocolStep : RawTerm scope}
    {channelRaw : RawTerm scope}
    {channel : Term sourceCtx (Ty.session protocolStep) channelRaw}
    (channelIsSN : Term.isStronglyNormalizing channel) :
    Term.isStronglyNormalizing (Term.sessionRecv channel) :=
  RawTerm.sessionRecv_isStronglyNormalizing channelIsSN

/-- Direct M04 SN case for session send. -/
theorem Term.sessionSend_isStronglyNormalizing
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
  RawTerm.sessionSend_isStronglyNormalizing channelIsSN payloadIsSN

/-- Direct M04 SN case for algebraic effect perform. -/
theorem Term.effectPerform_isStronglyNormalizing
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
  RawTerm.effectPerform_isStronglyNormalizing operationIsSN argumentsAreSN

/-- Direct M04 SN case for universe cumulativity markers. -/
theorem Term.cumulUp_isStronglyNormalizing
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
  RawTerm.cumulUpMarker_isStronglyNormalizing typeCodeIsSN

/-- Direct M04 SN case for the canonical identity equivalence. -/
theorem Term.equivReflId_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (carrier : Ty level scope) :
    Term.isStronglyNormalizing
      (Term.equivReflId (context := sourceCtx) carrier) := by
  let identityVar : Fin (scope + 1) := ⟨0, Nat.zero_lt_succ scope⟩
  have identityBodyIsSN :
      RawTerm.isStronglyNormalizing (RawTerm.var identityVar) :=
    RawTerm.var_isStronglyNormalizing identityVar
  have identityFunctionIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.lam (RawTerm.var identityVar)) :=
    RawTerm.lam_isStronglyNormalizing identityBodyIsSN
  exact RawTerm.equivIntro_isStronglyNormalizing
    identityFunctionIsSN identityFunctionIsSN

/-- Direct M04 SN case for the universe-identity view of the canonical
identity equivalence. -/
theorem Term.equivReflIdAtId_isStronglyNormalizing
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level scope)
    (carrierRaw : RawTerm scope) :
    Term.isStronglyNormalizing
      (Term.equivReflIdAtId (context := sourceCtx)
        innerLevel innerLevelLt carrier carrierRaw) := by
  let identityVar : Fin (scope + 1) := ⟨0, Nat.zero_lt_succ scope⟩
  have identityBodyIsSN :
      RawTerm.isStronglyNormalizing (RawTerm.var identityVar) :=
    RawTerm.var_isStronglyNormalizing identityVar
  have identityFunctionIsSN :
      RawTerm.isStronglyNormalizing
        (RawTerm.lam (RawTerm.var identityVar)) :=
    RawTerm.lam_isStronglyNormalizing identityBodyIsSN
  exact RawTerm.equivIntro_isStronglyNormalizing
    identityFunctionIsSN identityFunctionIsSN

/-- Direct M04 SN case for heterogeneous univalence introduction.

The raw projection is definitionally the same as the packaged equivalence
witness, so the SN evidence is reused directly. -/
theorem Term.uaIntroHet_isStronglyNormalizing
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
  equivWitnessIsSN

/-- Direct M04 SN case for univalence-to-equivalence extraction. -/
theorem Term.uaToEquiv_isStronglyNormalizing
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
  RawTerm.uaToEquiv_isStronglyNormalizing proofIsSN

end LeanFX2
