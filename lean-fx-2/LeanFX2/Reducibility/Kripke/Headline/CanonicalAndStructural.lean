import LeanFX2.Reducibility.Kripke.Project
import LeanFX2.Reducibility.Kripke.Fundamental
import LeanFX2.Reducibility.Kripke.Arrow
import LeanFX2.Reducibility.Kripke.SNExtraction

/-! # LeanFX2.Reducibility.Kripke.Headline.CanonicalAndStructural

Kripke-derived strong-normalization headlines for canonical leaves and
structural constructors whose SN proof is direct from child SN.
-/

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

end LeanFX2
