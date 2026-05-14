import LeanFX2.Reducibility.Kripke.Project
import LeanFX2.Reducibility.Kripke.Fundamental

/-! Kripke-derived SN of closed-leaf canonical values.

Headline shape demonstrating fundamental ∘ sn_of_X composition:
every canonical closed-leaf value is strongly normalizing via the
Kripke fundamental theorem. -/

namespace LeanFX2

/-- SN of unit via the Kripke fundamental theorem. -/
theorem Term.unit_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope} :
    Term.isStronglyNormalizing (Term.unit (context := sourceCtx)) :=
  ReducibleK.sn_of_unit (ReducibleK.fundamental_unit (sourceCtx := sourceCtx) 1)

theorem Term.boolTrue_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope} :
    Term.isStronglyNormalizing (Term.boolTrue (context := sourceCtx)) :=
  ReducibleK.sn_of_bool (ReducibleK.fundamental_boolTrue (sourceCtx := sourceCtx) 1)

theorem Term.boolFalse_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope} :
    Term.isStronglyNormalizing (Term.boolFalse (context := sourceCtx)) :=
  ReducibleK.sn_of_bool (ReducibleK.fundamental_boolFalse (sourceCtx := sourceCtx) 1)

theorem Term.natZero_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope} :
    Term.isStronglyNormalizing (Term.natZero (context := sourceCtx)) :=
  ReducibleK.sn_of_nat (ReducibleK.fundamental_natZero (sourceCtx := sourceCtx) 1)

/-- SN of natSucc via Kripke: SN(pred) → SN(natSucc pred). -/
theorem Term.natSucc_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {predRaw : RawTerm scope}
    {predTerm : Term sourceCtx Ty.nat predRaw}
    (predIsSN : Term.isStronglyNormalizing predTerm) :
    Term.isStronglyNormalizing (Term.natSucc predTerm) :=
  ReducibleK.sn_of_nat
    (ReducibleK.fundamental_natSucc (predIsR :=
      show @ReducibleK _ _ _ sourceCtx 1 Ty.nat predRaw predTerm from predIsSN))

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
  ReducibleK.fundamental_pair_sn firstIsSN secondIsSN

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
  ReducibleK.fundamental_fst_sn pairIsSN

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
  ReducibleK.fundamental_snd_sn pairIsSN

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
  ReducibleK.fundamental_lam_sn bodyIsSN

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
  ReducibleK.fundamental_lamPi_sn bodyIsSN

/-- SN of modIntro via Kripke. -/
theorem Term.modIntro_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx innerType innerRaw}
    (innerIsSN : Term.isStronglyNormalizing innerTerm) :
    Term.isStronglyNormalizing (Term.modIntro innerTerm) :=
  ReducibleK.fundamental_modIntro_sn innerIsSN

/-- SN of subsume via Kripke. -/
theorem Term.subsume_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx innerType innerRaw}
    (innerIsSN : Term.isStronglyNormalizing innerTerm) :
    Term.isStronglyNormalizing (Term.subsume innerTerm) :=
  ReducibleK.fundamental_subsume_sn innerIsSN

/-- SN of recordIntro via Kripke. -/
theorem Term.recordIntro_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {firstRaw : RawTerm scope}
    {firstField : Term context singleFieldType firstRaw}
    (firstFieldIsSN : Term.isStronglyNormalizing firstField) :
    Term.isStronglyNormalizing (Term.recordIntro firstField) :=
  ReducibleK.fundamental_recordIntro_sn firstFieldIsSN

/-- SN of recordProj via Kripke. -/
theorem Term.recordProj_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {singleFieldType : Ty level scope}
    {recordRaw : RawTerm scope}
    {recordValue : Term context (Ty.record singleFieldType) recordRaw}
    (recordIsSN : Term.isStronglyNormalizing recordValue) :
    Term.isStronglyNormalizing (Term.recordProj recordValue) :=
  ReducibleK.fundamental_recordProj_sn recordIsSN

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
  ReducibleK.fundamental_refineIntro_sn valueIsSN proofIsSN

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
  ReducibleK.fundamental_refineElim_sn refinedIsSN

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
  ReducibleK.fundamental_codataUnfold_sn stateIsSN transitionIsSN

/-- SN of sessionRecv via Kripke. -/
theorem Term.sessionRecv_strong_normalization_via_kripke
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {protocolStep : RawTerm scope}
    {channelRaw : RawTerm scope}
    {channel : Term sourceCtx (Ty.session protocolStep) channelRaw}
    (channelIsSN : Term.isStronglyNormalizing channel) :
    Term.isStronglyNormalizing (Term.sessionRecv channel) :=
  ReducibleK.fundamental_sessionRecv_sn channelIsSN

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
  ReducibleK.fundamental_sessionSend_sn protocolStep channelIsSN payloadIsSN

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

end LeanFX2
