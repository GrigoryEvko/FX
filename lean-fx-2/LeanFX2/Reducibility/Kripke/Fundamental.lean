import LeanFX2.Reducibility.Kripke.Basic
import LeanFX2.Term.SN.DirectCases

/-! Kripke fundamental theorem — closed-leaf base cases.

Every canonical closed-leaf value is `ReducibleK n` at its type
for every step `n`.  Closed leaves reduce to SN; canonical values
have empty progress graphs, so SN is trivial. -/

namespace LeanFX2

/-- The unit value is ReducibleK at Ty.unit for any step. -/
theorem ReducibleK.fundamental_unit
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (stepCount : Nat) :
    @ReducibleK mode level scope sourceCtx stepCount Ty.unit
      RawTerm.unit Term.unit := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    exact (Term.unit_isStronglyNormalizing (sourceCtx := sourceCtx))

theorem ReducibleK.fundamental_boolTrue
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (stepCount : Nat) :
    @ReducibleK mode level scope sourceCtx stepCount Ty.bool
      RawTerm.boolTrue Term.boolTrue := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    exact (Term.boolTrue_isStronglyNormalizing (sourceCtx := sourceCtx))

theorem ReducibleK.fundamental_boolFalse
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (stepCount : Nat) :
    @ReducibleK mode level scope sourceCtx stepCount Ty.bool
      RawTerm.boolFalse Term.boolFalse := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    exact (Term.boolFalse_isStronglyNormalizing (sourceCtx := sourceCtx))

theorem ReducibleK.fundamental_natZero
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (stepCount : Nat) :
    @ReducibleK mode level scope sourceCtx stepCount Ty.nat
      RawTerm.natZero Term.natZero := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    exact (Term.natZero_isStronglyNormalizing (sourceCtx := sourceCtx))

/-- Variables at any closed-leaf type are ReducibleK.  Demonstrated for
the five shipped closed-leaf arms. -/
theorem ReducibleK.fundamental_var_unit
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (stepCount : Nat) (position : Fin scope)
    (typesAt : varType sourceCtx position = Ty.unit) :
    @ReducibleK mode level scope sourceCtx stepCount Ty.unit
      (RawTerm.var position) (typesAt ▸ Term.var (context := sourceCtx) position) := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    exact RawTerm.var_isStronglyNormalizing position

theorem ReducibleK.fundamental_var_bool
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (stepCount : Nat) (position : Fin scope)
    (typesAt : varType sourceCtx position = Ty.bool) :
    @ReducibleK mode level scope sourceCtx stepCount Ty.bool
      (RawTerm.var position) (typesAt ▸ Term.var (context := sourceCtx) position) := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    exact RawTerm.var_isStronglyNormalizing position

theorem ReducibleK.fundamental_var_nat
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (stepCount : Nat) (position : Fin scope)
    (typesAt : varType sourceCtx position = Ty.nat) :
    @ReducibleK mode level scope sourceCtx stepCount Ty.nat
      (RawTerm.var position) (typesAt ▸ Term.var (context := sourceCtx) position) := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    exact RawTerm.var_isStronglyNormalizing position

theorem ReducibleK.fundamental_var_empty
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (stepCount : Nat) (position : Fin scope)
    (typesAt : varType sourceCtx position = Ty.empty) :
    @ReducibleK mode level scope sourceCtx stepCount Ty.empty
      (RawTerm.var position) (typesAt ▸ Term.var (context := sourceCtx) position) := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    exact RawTerm.var_isStronglyNormalizing position

theorem ReducibleK.fundamental_var_interval
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (stepCount : Nat) (position : Fin scope)
    (typesAt : varType sourceCtx position = Ty.interval) :
    @ReducibleK mode level scope sourceCtx stepCount Ty.interval
      (RawTerm.var position) (typesAt ▸ Term.var (context := sourceCtx) position) := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    exact RawTerm.var_isStronglyNormalizing position

/-- natSucc preserves ReducibleK at Ty.nat: SN(pred) → SN(natSucc pred). -/
theorem ReducibleK.fundamental_natSucc
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {stepCount : Nat} {predecessorRaw : RawTerm scope}
    {predecessorTerm : Term sourceCtx Ty.nat predecessorRaw}
    (predIsR :
      @ReducibleK mode level scope sourceCtx stepCount Ty.nat
        predecessorRaw predecessorTerm) :
    @ReducibleK mode level scope sourceCtx stepCount Ty.nat
      (RawTerm.natSucc predecessorRaw) (Term.natSucc predecessorTerm) := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    have predSN : Term.isStronglyNormalizing predecessorTerm := predIsR
    exact RawTerm.natSucc_isStronglyNormalizing predSN

/-! ## Deferred Kripke-introducer fundamentals — listNil / listCons /
optionNone / optionSome / eitherInl / eitherInr

Earlier this file shipped Kripke ι-introducer fundamentals taking
an `elimClosureWitness` / `matchClosureWitness` hypothesis encoding
"for every future world and reducible eliminator branches, the
`listElim`/`optionMatch`/`eitherMatch` application is reducible at
the motive."  That hypothesis is structurally a banned
hypothesis-as-postulate — the witness universally quantifies over a
motive and reducibility data the kernel cannot construct without the
M04 fundamental theorem's backward ι closure on the corresponding
Ty arms.

All six theorems have been DELETED.  Their honest replacement is the
M04 fundamental strong-normalization theorem inducting on typing
derivations, which produces the eliminator closure data as a real
consequence (not a hypothesis).  Until M04 lands, the introducer
direction of these constructors remains deferred — the closed-leaf SN
status of `listNil` / `optionNone` and the SN preservation of
`listCons` / `optionSome` / `eitherInl` / `eitherInr` are unaffected
and remain shipped via the direct cascade in
`Term/SN/DirectCases.lean`. -/

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

/-! ## SN-preservation wrappers for SN-only eliminators

Eliminators whose underlying SN preservation requires only SN of their
subterms (no full Reducible closure) ship as Kripke-namespace
fundamentals via direct delegation to `Term.X_isStronglyNormalizing`.
Eliminators that require a full `Reducible` scrutinee or arrow
application closure (`app`, `appPi`, `natElim`, `natRec`, `listElim`,
`optionMatch`, `eitherMatch`, `pathApp`) remain Phase B targets that
ship through `arrow_apply` chains. -/

/-- SN of boolElim via Kripke: SN(scrutinee), SN(then), SN(else) →
SN(boolElim scrutinee then else). -/
theorem ReducibleK.fundamental_boolElim_sn
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

/-- SN of idJ via Kripke: SN(base), SN(witness) → SN(idJ base witness). -/
theorem ReducibleK.fundamental_idJ_sn
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

/-- SN of oeqJ via Kripke: SN(base), SN(witness) → SN(oeqJ base witness). -/
theorem ReducibleK.fundamental_oeqJ_sn
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

/-- SN of idStrictRec via Kripke: SN(base), SN(witness) → SN. -/
theorem ReducibleK.fundamental_idStrictRec_sn
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

/-- SN of equivApp via Kripke: SN(equiv), SN(argument) → SN. -/
theorem ReducibleK.fundamental_equivApp_sn
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

/-- SN of equivApply via Kripke: SN(equiv), SN(argument) → SN. -/
theorem ReducibleK.fundamental_equivApply_sn
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

/-- SN of modElim via Kripke: SN(inner) → SN(modElim inner). -/
theorem ReducibleK.fundamental_modElim_sn
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {innerType : Ty level scope}
    {innerRaw : RawTerm scope}
    {innerTerm : Term context innerType innerRaw}
    (innerIsSN : Term.isStronglyNormalizing innerTerm) :
    Term.isStronglyNormalizing (Term.modElim innerTerm) :=
  Term.modElim_isStronglyNormalizing innerIsSN

/-! ## Deferred Kripke fundamentals — natElim / natRec

Earlier this file shipped `ReducibleK.fundamental_natElim_sn` and
`ReducibleK.fundamental_natRec_sn` as Term-level SN wrappers taking
a `succAppIsSN` / `contractumIsSN` universally-quantified raw SN
hypothesis.  Per the project's banned-hypothesis-as-postulate rule
those theorems vacuously shipped over raw forms the kernel cannot
construct.  They have been DELETED.

The honest path is the M04 fundamental theorem (proves reducibility
by induction on typing), which produces the contractum-SN status of
the ι reducts as a real consequence.  Defer until M04. -/

/-! ## Closed-leaf type-code fundamentals

The five `Term.X_isStronglyNormalizing` lemmas in `NeutralSNClosure.TypeCodeSN`
plus the two `Term.intervalN_isStronglyNormalizing` lemmas in
`Term.SN.DirectCases` give the Kripke fundamental cases
for the seven closed-leaf canonical-value Term ctors that the
upstream cascade left out. -/

theorem ReducibleK.fundamental_interval0
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (stepCount : Nat) :
    @ReducibleK mode level scope sourceCtx stepCount Ty.interval
      RawTerm.interval0 (Term.interval0 (context := sourceCtx)) := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    exact (Term.interval0_isStronglyNormalizing (sourceCtx := sourceCtx))

theorem ReducibleK.fundamental_interval1
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (stepCount : Nat) :
    @ReducibleK mode level scope sourceCtx stepCount Ty.interval
      RawTerm.interval1 (Term.interval1 (context := sourceCtx)) := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    exact (Term.interval1_isStronglyNormalizing (sourceCtx := sourceCtx))

theorem ReducibleK.fundamental_universeCode_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    Term.isStronglyNormalizing
      (Term.universeCode (context := sourceCtx)
        innerLevel outerLevel cumulOk levelLe) :=
  Term.universeCode_isStronglyNormalizing
    innerLevel outerLevel cumulOk levelLe

theorem ReducibleK.fundamental_piTyCode_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {domainCodeRaw : RawTerm scope}
    {codomainCodeRaw : RawTerm (scope + 1)}
    (domainCodeIsSN : RawTerm.isStronglyNormalizing domainCodeRaw)
    (codomainCodeIsSN : RawTerm.isStronglyNormalizing codomainCodeRaw) :
    Term.isStronglyNormalizing
      (Term.piTyCode (context := sourceCtx)
        outerLevel levelLe domainCodeRaw codomainCodeRaw) :=
  Term.piTyCode_isStronglyNormalizing outerLevel levelLe
    domainCodeIsSN codomainCodeIsSN

theorem ReducibleK.fundamental_sigmaTyCode_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {domainCodeRaw : RawTerm scope}
    {codomainCodeRaw : RawTerm (scope + 1)}
    (domainCodeIsSN : RawTerm.isStronglyNormalizing domainCodeRaw)
    (codomainCodeIsSN : RawTerm.isStronglyNormalizing codomainCodeRaw) :
    Term.isStronglyNormalizing
      (Term.sigmaTyCode (context := sourceCtx)
        outerLevel levelLe domainCodeRaw codomainCodeRaw) :=
  Term.sigmaTyCode_isStronglyNormalizing outerLevel levelLe
    domainCodeIsSN codomainCodeIsSN

theorem ReducibleK.fundamental_productCode_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {firstCodeRaw secondCodeRaw : RawTerm scope}
    (firstCodeIsSN : RawTerm.isStronglyNormalizing firstCodeRaw)
    (secondCodeIsSN : RawTerm.isStronglyNormalizing secondCodeRaw) :
    Term.isStronglyNormalizing
      (Term.productCode (context := sourceCtx)
        outerLevel levelLe firstCodeRaw secondCodeRaw) :=
  Term.productCode_isStronglyNormalizing outerLevel levelLe
    firstCodeIsSN secondCodeIsSN

theorem ReducibleK.fundamental_sumCode_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    {leftCodeRaw rightCodeRaw : RawTerm scope}
    (leftCodeIsSN : RawTerm.isStronglyNormalizing leftCodeRaw)
    (rightCodeIsSN : RawTerm.isStronglyNormalizing rightCodeRaw) :
    Term.isStronglyNormalizing
      (Term.sumCode (context := sourceCtx)
        outerLevel levelLe leftCodeRaw rightCodeRaw) :=
  Term.sumCode_isStronglyNormalizing outerLevel levelLe
    leftCodeIsSN rightCodeIsSN

/-- SN of funextIntroHet via Kripke.  The raw projection is
`lam (refl applyARaw)`; applyBRaw is schematic and irrelevant. -/
theorem ReducibleK.fundamental_funextIntroHet_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (domainType codomainType : Ty level scope)
    {applyARaw applyBRaw : RawTerm (scope + 1)}
    (applyAIsSN : RawTerm.isStronglyNormalizing applyARaw) :
    Term.isStronglyNormalizing
      (Term.funextIntroHet (context := sourceCtx)
        domainType codomainType applyARaw applyBRaw) :=
  Term.funextIntroHet_isStronglyNormalizing
    domainType codomainType applyAIsSN

/-- SN of codataDest via Kripke.  The contractum-SN closure
hypothesis covers the β arm `codataDest (codataUnfold s t) → app t s`. -/
theorem ReducibleK.fundamental_codataDest_sn
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

/-- SN of listElim via Kripke.  Takes SN of scrutinee/nilBranch/
consBranch plus the contractum closure for the cons-ι arm
`listElim (listCons h t) n c → app (app c h) t`. -/
theorem ReducibleK.fundamental_listElim_sn
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

/-- SN of optionMatch via Kripke.  Takes SN of scrutinee/noneBranch/
someBranch plus the contractum closure for the some-ι arm
`optionMatch (optionSome v) n s → app s v`. -/
theorem ReducibleK.fundamental_optionMatch_sn
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

/-- SN of eitherMatch via Kripke.  Takes SN of scrutinee/leftBranch/
rightBranch plus a pair of contractum closures for the two ι arms:
`eitherMatch (eitherInl v) l r → app l v` and the inr-symmetric arm. -/
theorem ReducibleK.fundamental_eitherMatch_sn
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

/-- SN of app via Kripke.  Takes SN of function and argument plus the
contractum closure for the β arm `app (lam body) arg → body[arg/0]`.
The closure consumes SN of body (extracted from the lam-form function
reduct) and SN of the argument reduct. -/
theorem ReducibleK.fundamental_app_sn
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

/-- SN of appPi via Kripke.  Dependent-Π elimination shares the raw
β rule with `Term.app`; the typed signature differs only in carrying
a dependent codomain that substitutes the argument. -/
theorem ReducibleK.fundamental_appPi_sn
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

/-- SN of pathApp via Kripke.  Cubical path application: the β rule
fires when the path develops to a `pathLam` and the interval argument
develops to any normal form, yielding `body.subst0 interval`.  Mirrors
the `app` family modulo the cubical-mode parameter and the path-typed
domain. -/
theorem ReducibleK.fundamental_pathApp_sn
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

/-- SN of transp via Kripke.  The current raw transport relation has
constant-path, univalence, and path-composition computational arms; the two
nontrivial reduct families are supplied as explicit contractum closures. -/
theorem ReducibleK.fundamental_transp_sn
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

/-- SN of hcomp via Kripke.  The current raw `hcomp` relation is
congruence-only; boundary computation is still tracked separately by the
future cubical β-rule work. -/
theorem ReducibleK.fundamental_hcomp_sn
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

/-! ## Priority-1 Kripke closure-application fundamentals (eliminator-side).

The following theorems are the Kripke fundamental-theorem cases for
**eliminator-direction** application: given a Tait-reducible scrutinee
(or function or witness) plus reducible argument(s) where required, the
eliminator application is Tait-reducible at the result type.  These
fundamentals are direct projections from the `ReducibleK` predicate
closures defined in `Predicate.lean`.

Together with the existing `arrow_apply` (Arrow.lean), `piTy_apply`,
`sigmaTy_fst`, `sigmaTy_snd`, `listType_elim`, `optionType_match`,
`eitherType_match`, `refine_elim`, `record_proj`, `codata_dest`,
`session_recv`, `mod_elim`, `effect_rename` (Project.lean), these close
the eliminator-direction half of the fundamental theorem for all 19
Kripke-closure Ty arms.

The remaining fundamental-theorem work is the **introducer-direction**
(reducible-input → reducible-introduction) and **β-redex backward
closure** cases, which require the head-expansion cascade (parProgress
backward closure of ReducibleK).  Those are Priority-2/3 and deferred
per the M04/K12.27 sub-prerequisite scope. -/

/-- Kripke fundamental: identity-type J elimination preserves
reducibility.  Given a Tait-reducible witness at `Ty.id` and a
Tait-reducible base case at the motive (in every future world,
parameterized by an arbitrary motive type), `Term.idJ baseCase witness`
is Tait-reducible at the motive.  Mirrors the J induction principle on
identity types — the motive is universally quantified because the
identity-type's structure does not constrain the eliminator's result
type. -/
theorem ReducibleK.fundamental_idJ
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {witnessRaw : RawTerm scope}
    {witnessTerm :
      Term context (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw}
    (witnessIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw witnessTerm)
    {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming scope targetScope}
    (termRenaming : TermRenaming context targetCtx rho)
    {motiveType : Ty level targetScope}
    {baseRaw : RawTerm targetScope}
    (baseCase : Term targetCtx motiveType baseRaw)
    (baseCaseIsR :
      @ReducibleK mode level targetScope targetCtx stepCount
        motiveType baseRaw baseCase) :
    @ReducibleK mode level targetScope targetCtx stepCount
      motiveType _
      (Term.idJ baseCase (Term.rename termRenaming witnessTerm)) :=
  witnessIsR.2 termRenaming baseCase baseCaseIsR

/-- Kripke fundamental: observational-equality J elimination preserves
reducibility.  Same shape as `fundamental_idJ` over the `Ty.oeq`
carrier. -/
theorem ReducibleK.fundamental_oeqJ
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {witnessRaw : RawTerm scope}
    {witnessTerm :
      Term context (Ty.oeq carrier leftEndpoint rightEndpoint) witnessRaw}
    (witnessIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.oeq carrier leftEndpoint rightEndpoint) witnessRaw witnessTerm)
    {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming scope targetScope}
    (termRenaming : TermRenaming context targetCtx rho)
    {motiveType : Ty level targetScope}
    {baseRaw : RawTerm targetScope}
    (baseCase : Term targetCtx motiveType baseRaw)
    (baseCaseIsR :
      @ReducibleK mode level targetScope targetCtx stepCount
        motiveType baseRaw baseCase) :
    @ReducibleK mode level targetScope targetCtx stepCount
      motiveType _
      (Term.oeqJ baseCase (Term.rename termRenaming witnessTerm)) :=
  witnessIsR.2 termRenaming baseCase baseCaseIsR

/-- Kripke fundamental: strict-identity recursion preserves
reducibility.  Same shape as `fundamental_idJ` over the `Ty.idStrict`
carrier modulo the strict-mode side condition. -/
theorem ReducibleK.fundamental_idStrictRec
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {carrier : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {witnessRaw : RawTerm scope}
    {witnessTerm :
      Term context (Ty.idStrict carrier leftEndpoint rightEndpoint) witnessRaw}
    (witnessIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.idStrict carrier leftEndpoint rightEndpoint) witnessRaw witnessTerm)
    (modeIsStrict : mode = Mode.strict)
    {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming scope targetScope}
    (termRenaming : TermRenaming context targetCtx rho)
    {motiveType : Ty level targetScope}
    {baseRaw : RawTerm targetScope}
    (baseCase : Term targetCtx motiveType baseRaw)
    (baseCaseIsR :
      @ReducibleK mode level targetScope targetCtx stepCount
        motiveType baseRaw baseCase) :
    @ReducibleK mode level targetScope targetCtx stepCount
      motiveType _
      (Term.idStrictRec modeIsStrict baseCase
        (Term.rename termRenaming witnessTerm)) :=
  witnessIsR.2 modeIsStrict termRenaming baseCase baseCaseIsR

/-- Kripke fundamental: equivalence-type application preserves
reducibility.  Given a Tait-reducible packaged equivalence at
`Ty.equiv leftTy rightTy` and a Tait-reducible argument at the
renamed leftTy, `Term.equivApply (rename equiv) arg` is Tait-reducible
at the renamed rightTy.  Mirrors `arrow_apply` over the equivalence
carrier swap. -/
theorem ReducibleK.fundamental_equivApply
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {leftTy rightTy : Ty level scope}
    {equivRaw : RawTerm scope}
    {equivTerm : Term context (Ty.equiv leftTy rightTy) equivRaw}
    (equivIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.equiv leftTy rightTy) equivRaw equivTerm)
    {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming scope targetScope}
    (termRenaming : TermRenaming context targetCtx rho)
    {argumentRaw : RawTerm targetScope}
    (argumentTerm : Term targetCtx (leftTy.rename rho) argumentRaw)
    (argumentIsR :
      @ReducibleK mode level targetScope targetCtx stepCount
        (leftTy.rename rho) argumentRaw argumentTerm) :
    @ReducibleK mode level targetScope targetCtx stepCount
      (rightTy.rename rho) _
      (Term.equivApply (Term.rename termRenaming equivTerm) argumentTerm) :=
  equivIsR.2 termRenaming argumentTerm argumentIsR

/-- Kripke fundamental: cubical path application preserves reducibility
under the univalent-mode discipline.  Given a Tait-reducible path at
`Ty.path` and a Tait-reducible interval value, `Term.pathApp` is
Tait-reducible at the renamed carrier.  Endpoint specialisation
(pathApp p i0 / pathApp p i1) is governed by Step-level reductions —
the closure only commits to the result sitting at `carrierType.rename
rho`. -/
theorem ReducibleK.fundamental_pathApp
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {carrierType : Ty level scope}
    {leftEndpoint rightEndpoint : RawTerm scope}
    {pathRaw : RawTerm scope}
    {pathTerm :
      Term context (Ty.path carrierType leftEndpoint rightEndpoint) pathRaw}
    (pathIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.path carrierType leftEndpoint rightEndpoint) pathRaw pathTerm)
    (modeIsUnivalent : mode = Mode.univalent)
    {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming scope targetScope}
    (termRenaming : TermRenaming context targetCtx rho)
    {intervalRaw : RawTerm targetScope}
    (intervalTerm : Term targetCtx Ty.interval intervalRaw)
    (intervalIsR :
      @ReducibleK mode level targetScope targetCtx stepCount
        Ty.interval intervalRaw intervalTerm) :
    @ReducibleK mode level targetScope targetCtx stepCount
      (carrierType.rename rho) _
      (Term.pathApp modeIsUnivalent
        (Term.rename termRenaming pathTerm) intervalTerm) :=
  pathIsR.2 modeIsUnivalent termRenaming intervalTerm intervalIsR

/-- Kripke fundamental: glue elimination preserves reducibility under
the univalent-mode discipline.  Given a Tait-reducible glue value at
`Ty.glue baseType boundaryWitness`, `Term.glueElim` produces a
Tait-reducible result at the renamed baseType.  Direct projection from
the glue closure clause in `Predicate.lean`. -/
theorem ReducibleK.fundamental_glueElim
    {mode : Mode} {level scope : Nat}
    {context : Ctx mode level scope}
    {stepCount : Nat}
    {baseType : Ty level scope}
    {boundaryWitness gluedRaw : RawTerm scope}
    {gluedTerm :
      Term context (Ty.glue baseType boundaryWitness) gluedRaw}
    (gluedIsR :
      @ReducibleK mode level scope context (stepCount + 1)
        (Ty.glue baseType boundaryWitness) gluedRaw gluedTerm)
    (modeIsUnivalent : mode = Mode.univalent)
    {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
    {rho : RawRenaming scope targetScope}
    (termRenaming : TermRenaming context targetCtx rho) :
    @ReducibleK mode level targetScope targetCtx stepCount
      (baseType.rename rho) _
      (Term.glueElim modeIsUnivalent
        (Term.rename termRenaming gluedTerm)) :=
  gluedIsR.2 modeIsUnivalent termRenaming

end LeanFX2
