import LeanFX2.Reducibility.Kripke.Fundamental.ClosedAndVariables

/-! # LeanFX2.Reducibility.Kripke.Fundamental.StructuralSN

Structural ReducibleK and SN-preservation wrappers for product,
interval, modal, session, record, refine, codata, lambda, and cubical
introduction forms.
-/

namespace LeanFX2

/-- intervalOpp preserves ReducibleK at Ty.interval. -/
theorem ReducibleK.fundamental_intervalOpp
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {stepCount : Nat} {innerRaw : RawTerm scope}
    {innerValue : Term sourceCtx Ty.interval innerRaw}
    (innerIsR :
      @ReducibleK mode level scope sourceCtx stepCount Ty.interval
        innerRaw innerValue) :
    @ReducibleK mode level scope sourceCtx stepCount Ty.interval
      (RawTerm.intervalOpp innerRaw) (Term.intervalOpp innerValue) := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    have innerSN : Term.isStronglyNormalizing innerValue := innerIsR
    exact Term.intervalOpp_isStronglyNormalizing innerSN

/-- intervalMeet preserves ReducibleK at Ty.interval. -/
theorem ReducibleK.fundamental_intervalMeet
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {stepCount : Nat} {leftRaw rightRaw : RawTerm scope}
    {leftValue : Term sourceCtx Ty.interval leftRaw}
    {rightValue : Term sourceCtx Ty.interval rightRaw}
    (leftIsR :
      @ReducibleK mode level scope sourceCtx stepCount Ty.interval
        leftRaw leftValue)
    (rightIsR :
      @ReducibleK mode level scope sourceCtx stepCount Ty.interval
        rightRaw rightValue) :
    @ReducibleK mode level scope sourceCtx stepCount Ty.interval
      (RawTerm.intervalMeet leftRaw rightRaw)
      (Term.intervalMeet leftValue rightValue) := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    have leftSN : Term.isStronglyNormalizing leftValue := leftIsR
    have rightSN : Term.isStronglyNormalizing rightValue := rightIsR
    exact Term.intervalMeet_isStronglyNormalizing leftSN rightSN

/-- intervalJoin preserves ReducibleK at Ty.interval. -/
theorem ReducibleK.fundamental_intervalJoin
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {stepCount : Nat} {leftRaw rightRaw : RawTerm scope}
    {leftValue : Term sourceCtx Ty.interval leftRaw}
    {rightValue : Term sourceCtx Ty.interval rightRaw}
    (leftIsR :
      @ReducibleK mode level scope sourceCtx stepCount Ty.interval
        leftRaw leftValue)
    (rightIsR :
      @ReducibleK mode level scope sourceCtx stepCount Ty.interval
        rightRaw rightValue) :
    @ReducibleK mode level scope sourceCtx stepCount Ty.interval
      (RawTerm.intervalJoin leftRaw rightRaw)
      (Term.intervalJoin leftValue rightValue) := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    have leftSN : Term.isStronglyNormalizing leftValue := leftIsR
    have rightSN : Term.isStronglyNormalizing rightValue := rightIsR
    exact Term.intervalJoin_isStronglyNormalizing leftSN rightSN

/-- modIntro preserves ReducibleK at any inner type (Term.modIntro
keeps the same Ty index, only wraps the raw projection). -/
theorem ReducibleK.fundamental_modIntro_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx innerType innerRaw}
    (innerIsSN : Term.isStronglyNormalizing innerTerm) :
    Term.isStronglyNormalizing (Term.modIntro innerTerm) :=
  Term.modIntro_isStronglyNormalizing innerIsSN

/-- subsume preserves SN at any inner type. -/
theorem ReducibleK.fundamental_subsume_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term sourceCtx innerType innerRaw}
    (innerIsSN : Term.isStronglyNormalizing innerTerm) :
    Term.isStronglyNormalizing (Term.subsume innerTerm) :=
  Term.subsume_isStronglyNormalizing innerIsSN

/-- pair preserves SN: both component SN → pair SN. -/
theorem ReducibleK.fundamental_pair_sn
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

/-- fst preserves SN: pair SN → fst SN. -/
theorem ReducibleK.fundamental_fst_sn
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    {pairTerm : Term context (Ty.sigmaTy firstType secondType) pairRaw}
    (pairIsSN : Term.isStronglyNormalizing pairTerm) :
    Term.isStronglyNormalizing (Term.fst pairTerm) :=
  Term.fst_isStronglyNormalizing pairIsSN

/-- snd preserves SN: pair SN → snd SN. -/
theorem ReducibleK.fundamental_snd_sn
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {firstType : Ty level scope}
    {secondType : Ty level (scope + 1)}
    {pairRaw : RawTerm scope}
    {pairTerm : Term context (Ty.sigmaTy firstType secondType) pairRaw}
    (pairIsSN : Term.isStronglyNormalizing pairTerm) :
    Term.isStronglyNormalizing (Term.snd pairTerm) :=
  Term.snd_isStronglyNormalizing pairIsSN

/-- refl preserves SN: raw endpoint SN → refl SN. -/
theorem ReducibleK.fundamental_refl_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (carrier : Ty level scope)
    (rawWitness : RawTerm scope)
    (endpointIsSN : RawTerm.isStronglyNormalizing rawWitness) :
    Term.isStronglyNormalizing
      (Term.refl (context := sourceCtx) carrier rawWitness) :=
  Term.refl_isStronglyNormalizing endpointIsSN

/-- oeqRefl preserves SN: raw endpoint SN → oeqRefl SN. -/
theorem ReducibleK.fundamental_oeqRefl_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (carrier : Ty level scope)
    (rawWitness : RawTerm scope)
    (endpointIsSN : RawTerm.isStronglyNormalizing rawWitness) :
    Term.isStronglyNormalizing
      (Term.oeqRefl (context := sourceCtx) carrier rawWitness) :=
  Term.oeqRefl_isStronglyNormalizing endpointIsSN

/-- idStrictRefl preserves SN at strict mode: raw endpoint SN → SN. -/
theorem ReducibleK.fundamental_idStrictRefl_sn
    {level scope : Nat}
    {sourceCtx : Ctx Mode.strict level scope}
    (carrier : Ty level scope)
    (rawWitness : RawTerm scope)
    (endpointIsSN : RawTerm.isStronglyNormalizing rawWitness) :
    Term.isStronglyNormalizing
      (Term.idStrictRefl (context := sourceCtx) rfl carrier rawWitness) :=
  Term.idStrictRefl_isStronglyNormalizing rfl endpointIsSN

/-- sessionRecv preserves SN: channel SN → sessionRecv SN. -/
theorem ReducibleK.fundamental_sessionRecv_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {protocolStep : RawTerm scope}
    {channelRaw : RawTerm scope}
    {channel : Term sourceCtx (Ty.session protocolStep) channelRaw}
    (channelIsSN : Term.isStronglyNormalizing channel) :
    Term.isStronglyNormalizing (Term.sessionRecv channel) :=
  Term.sessionRecv_isStronglyNormalizing channelIsSN

/-- sessionSend preserves SN: channel + payload SN → sessionSend SN. -/
theorem ReducibleK.fundamental_sessionSend_sn
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

/-- cumulUp preserves SN: typeCode SN → cumulUp SN. -/
theorem ReducibleK.fundamental_cumulUp_sn
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
