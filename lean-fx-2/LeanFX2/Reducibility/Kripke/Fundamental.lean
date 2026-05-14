import LeanFX2.Reducibility.Kripke.Basic
import LeanFX2.Reducibility.FundamentalAliases

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

/-- listNil at any element type: SN at the SN-fallback Kripke arm. -/
theorem ReducibleK.fundamental_listNil
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {elementType : Ty level scope}
    (stepCount : Nat) :
    @ReducibleK mode level scope sourceCtx stepCount (Ty.listType elementType)
      RawTerm.listNil (Term.listNil) := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    exact (Term.listNil_isStronglyNormalizing
      (sourceCtx := sourceCtx) (elementType := elementType))

/-- optionNone at any element type. -/
theorem ReducibleK.fundamental_optionNone
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {elementType : Ty level scope}
    (stepCount : Nat) :
    @ReducibleK mode level scope sourceCtx stepCount (Ty.optionType elementType)
      RawTerm.optionNone (Term.optionNone) := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    exact (Term.optionNone_isStronglyNormalizing
      (sourceCtx := sourceCtx) (elementType := elementType))

/-- listCons preserves ReducibleK at Ty.listType (SN-fallback arm).
SN-only variant; takes SN witnesses for both sub-terms directly
because the elementType arm is unrestricted and head reducibility
doesn't immediately project to SN at compound elementType. -/
theorem ReducibleK.fundamental_listCons_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {elementType : Ty level scope}
    {stepCount : Nat}
    {headRaw tailRaw : RawTerm scope}
    {headTerm : Term sourceCtx elementType headRaw}
    {tailTerm : Term sourceCtx (Ty.listType elementType) tailRaw}
    (headIsSN : Term.isStronglyNormalizing headTerm)
    (tailIsSN : Term.isStronglyNormalizing tailTerm) :
    @ReducibleK mode level scope sourceCtx stepCount
      (Ty.listType elementType) (RawTerm.listCons headRaw tailRaw)
      (Term.listCons headTerm tailTerm) := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    exact Term.listCons_isStronglyNormalizing headIsSN tailIsSN

/-- optionSome preserves ReducibleK at Ty.optionType (SN-fallback). -/
theorem ReducibleK.fundamental_optionSome_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    {elementType : Ty level scope}
    {stepCount : Nat}
    {valueRaw : RawTerm scope}
    {valueTerm : Term sourceCtx elementType valueRaw}
    (valueIsSN : Term.isStronglyNormalizing valueTerm) :
    @ReducibleK mode level scope sourceCtx stepCount
      (Ty.optionType elementType) (RawTerm.optionSome valueRaw)
      (Term.optionSome valueTerm) := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    exact Term.optionSome_isStronglyNormalizing valueIsSN

/-- eitherInl preserves ReducibleK at Ty.eitherType (SN-fallback). -/
theorem ReducibleK.fundamental_eitherInl_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (leftType rightType : Ty level scope)
    {stepCount : Nat}
    {valueRaw : RawTerm scope}
    {valueTerm : Term sourceCtx leftType valueRaw}
    (valueIsSN : Term.isStronglyNormalizing valueTerm) :
    @ReducibleK mode level scope sourceCtx stepCount
      (Ty.eitherType leftType rightType) (RawTerm.eitherInl valueRaw)
      (Term.eitherInl (rightType := rightType) valueTerm) := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    exact (Term.eitherInl_isStronglyNormalizing (rightType := rightType) valueIsSN)

/-- eitherInr preserves ReducibleK at Ty.eitherType (SN-fallback). -/
theorem ReducibleK.fundamental_eitherInr_sn
    {mode : Mode} {level scope : Nat}
    {sourceCtx : Ctx mode level scope}
    (leftType rightType : Ty level scope)
    {stepCount : Nat}
    {valueRaw : RawTerm scope}
    {valueTerm : Term sourceCtx rightType valueRaw}
    (valueIsSN : Term.isStronglyNormalizing valueTerm) :
    @ReducibleK mode level scope sourceCtx stepCount
      (Ty.eitherType leftType rightType) (RawTerm.eitherInr valueRaw)
      (Term.eitherInr (leftType := leftType) valueTerm) := by
  cases stepCount with
  | zero => trivial
  | succ subCount =>
    exact (Term.eitherInr_isStronglyNormalizing (leftType := leftType) valueIsSN)

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

end LeanFX2
