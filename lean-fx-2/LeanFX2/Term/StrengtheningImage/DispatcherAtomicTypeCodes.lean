import LeanFX2.Term.StrengtheningImage.Core
import LeanFX2.Term.StrengtheningImage.TypeCodes
import LeanFX2.Term.StrengtheningImage.Reflexivity


/-! # Term/StrengtheningImage/DispatcherAtomicTypeCodes

Dispatcher-arm soundness for closed atoms, universe/type codes, and closed HoTT reflexivity constructors.
-/

namespace LeanFX2

namespace Term

/-- Dispatcher soundness at the `Term.unit` arm.  Closed-leaf: the
dispatcher returns `some (partialStrengthenTypedUnit strengthening)`
unconditionally, so the soundness is the wrapper soundness applied
directly. -/
theorem partialStrengthenTyped?_atUnit_imp_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result :
      StrengtheningResult strengthening (Term.unit (context := sourceCtx)))
    (success :
      partialStrengthenTyped? (Term.unit (context := sourceCtx))
          strengthening = some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  cases success
  exact partialStrengthenTypedUnit_sound strengthening

/-- Dispatcher soundness at the `Term.boolTrue` arm. -/
theorem partialStrengthenTyped?_atBoolTrue_imp_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result :
      StrengtheningResult strengthening
        (Term.boolTrue (context := sourceCtx)))
    (success :
      partialStrengthenTyped? (Term.boolTrue (context := sourceCtx))
          strengthening = some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  cases success
  exact partialStrengthenTypedBoolTrue_sound strengthening

/-- Dispatcher soundness at the `Term.boolFalse` arm. -/
theorem partialStrengthenTyped?_atBoolFalse_imp_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result :
      StrengtheningResult strengthening
        (Term.boolFalse (context := sourceCtx)))
    (success :
      partialStrengthenTyped? (Term.boolFalse (context := sourceCtx))
          strengthening = some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  cases success
  exact partialStrengthenTypedBoolFalse_sound strengthening

/-- Dispatcher soundness at the `Term.natZero` arm. -/
theorem partialStrengthenTyped?_atNatZero_imp_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result :
      StrengtheningResult strengthening
        (Term.natZero (context := sourceCtx)))
    (success :
      partialStrengthenTyped? (Term.natZero (context := sourceCtx))
          strengthening = some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  cases success
  exact partialStrengthenTypedNatZero_sound strengthening

/-- Dispatcher soundness at the `Term.interval0` arm. -/
theorem partialStrengthenTyped?_atInterval0_imp_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result :
      StrengtheningResult strengthening
        (Term.interval0 (context := sourceCtx)))
    (success :
      partialStrengthenTyped? (Term.interval0 (context := sourceCtx))
          strengthening = some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  cases success
  exact partialStrengthenTypedInterval0_sound strengthening

/-- Dispatcher soundness at the `Term.interval1` arm. -/
theorem partialStrengthenTyped?_atInterval1_imp_sound {mode : Mode} {level : Nat}
    {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result :
      StrengtheningResult strengthening
        (Term.interval1 (context := sourceCtx)))
    (success :
      partialStrengthenTyped? (Term.interval1 (context := sourceCtx))
          strengthening = some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  cases success
  exact partialStrengthenTypedInterval1_sound strengthening

/-- Dispatcher soundness at the `Term.arrowCode` arm.  Type-code closed
leaf with two flat-scope raw witnesses (domain + codomain) plus the
universe-level positional forwarding (`outerLevel`/`levelLe`).  No
value IH — the wrapper consumes the raw witnesses directly. -/
theorem partialStrengthenTyped?_atArrowCode_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw codomainCodeRaw : RawTerm sourceScope)
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.arrowCode (context := sourceCtx) outerLevel levelLe
        domainCodeRaw codomainCodeRaw))
    (success : partialStrengthenTyped?
        (Term.arrowCode (context := sourceCtx) outerLevel levelLe
          domainCodeRaw codomainCodeRaw) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetDomainCodeRaw domainSuccess
    split at success
    · cases success
    · rename_i targetCodomainCodeRaw codomainSuccess
      cases success
      exact partialStrengthenTypedArrowCode_sound outerLevel levelLe
        domainCodeRaw codomainCodeRaw targetDomainCodeRaw
        targetCodomainCodeRaw domainSuccess codomainSuccess

/-- Dispatcher soundness at the `Term.piTyCode` arm.  Π-type-code closed
leaf with one flat-scope raw (`domainCodeRaw`) plus one lifted raw
(`codomainCodeRaw` at `scope + 1`).  The codomain rides
`strengthening.back.lift` to track the bound variable from the Π
binder.  Universe-level positional forwarding identical to arrow. -/
theorem partialStrengthenTyped?_atPiTyCode_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm sourceScope)
    (codomainCodeRaw : RawTerm (sourceScope + 1))
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.piTyCode (context := sourceCtx) outerLevel levelLe
        domainCodeRaw codomainCodeRaw))
    (success : partialStrengthenTyped?
        (Term.piTyCode (context := sourceCtx) outerLevel levelLe
          domainCodeRaw codomainCodeRaw) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetDomainCodeRaw domainSuccess
    split at success
    · cases success
    · rename_i targetCodomainCodeRaw codomainSuccess
      cases success
      exact partialStrengthenTypedPiTyCode_sound outerLevel levelLe
        domainCodeRaw codomainCodeRaw targetDomainCodeRaw
        targetCodomainCodeRaw domainSuccess codomainSuccess

/-- Dispatcher soundness at the `Term.sigmaTyCode` arm.  Σ-type-code
closed leaf, structurally identical to piTyCode: one flat raw
(`domainCodeRaw`) plus one lifted raw (`codomainCodeRaw` at
`scope + 1`, dependent on the first component). -/
theorem partialStrengthenTyped?_atSigmaTyCode_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm sourceScope)
    (codomainCodeRaw : RawTerm (sourceScope + 1))
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.sigmaTyCode (context := sourceCtx) outerLevel levelLe
        domainCodeRaw codomainCodeRaw))
    (success : partialStrengthenTyped?
        (Term.sigmaTyCode (context := sourceCtx) outerLevel levelLe
          domainCodeRaw codomainCodeRaw) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetDomainCodeRaw domainSuccess
    split at success
    · cases success
    · rename_i targetCodomainCodeRaw codomainSuccess
      cases success
      exact partialStrengthenTypedSigmaTyCode_sound outerLevel levelLe
        domainCodeRaw codomainCodeRaw targetDomainCodeRaw
        targetCodomainCodeRaw domainSuccess codomainSuccess

/-- Dispatcher soundness at the `Term.productCode` arm.  Non-dependent
pair type-code closed leaf with two flat-scope raw witnesses (first +
second components, both at `sourceScope`).  Universe-level positional
forwarding identical to arrow. -/
theorem partialStrengthenTyped?_atProductCode_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (firstCodeRaw secondCodeRaw : RawTerm sourceScope)
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.productCode (context := sourceCtx) outerLevel levelLe
        firstCodeRaw secondCodeRaw))
    (success : partialStrengthenTyped?
        (Term.productCode (context := sourceCtx) outerLevel levelLe
          firstCodeRaw secondCodeRaw) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetFirstCodeRaw firstSuccess
    split at success
    · cases success
    · rename_i targetSecondCodeRaw secondSuccess
      cases success
      exact partialStrengthenTypedProductCode_sound outerLevel levelLe
        firstCodeRaw secondCodeRaw targetFirstCodeRaw
        targetSecondCodeRaw firstSuccess secondSuccess

/-- Dispatcher soundness at the `Term.sumCode` arm.  Binary sum
type-code closed leaf with two flat-scope raw witnesses (left + right
summands).  Structurally identical to productCode. -/
theorem partialStrengthenTyped?_atSumCode_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm sourceScope)
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.sumCode (context := sourceCtx) outerLevel levelLe
        leftCodeRaw rightCodeRaw))
    (success : partialStrengthenTyped?
        (Term.sumCode (context := sourceCtx) outerLevel levelLe
          leftCodeRaw rightCodeRaw) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetLeftCodeRaw leftSuccess
    split at success
    · cases success
    · rename_i targetRightCodeRaw rightSuccess
      cases success
      exact partialStrengthenTypedSumCode_sound outerLevel levelLe
        leftCodeRaw rightCodeRaw targetLeftCodeRaw
        targetRightCodeRaw leftSuccess rightSuccess

/-- Dispatcher soundness at the `Term.listCode` arm.  List-type-code
closed leaf with a single flat-scope raw witness (`elementCodeRaw`)
plus the universe-level positional forwarding (`outerLevel`/
`levelLe`).  No value IH; the wrapper consumes the raw witness
directly. -/
theorem partialStrengthenTyped?_atListCode_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm sourceScope)
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.listCode (context := sourceCtx) outerLevel levelLe
        elementCodeRaw))
    (success : partialStrengthenTyped?
        (Term.listCode (context := sourceCtx) outerLevel levelLe
          elementCodeRaw) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetElementCodeRaw elementSuccess
    cases success
    exact partialStrengthenTypedListCode_sound outerLevel levelLe
      elementCodeRaw targetElementCodeRaw elementSuccess

/-- Dispatcher soundness at the `Term.optionCode` arm.  Option-type-code
closed leaf with a single flat-scope raw witness (`elementCodeRaw`).
Structurally identical to `listCode`. -/
theorem partialStrengthenTyped?_atOptionCode_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm sourceScope)
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.optionCode (context := sourceCtx) outerLevel levelLe
        elementCodeRaw))
    (success : partialStrengthenTyped?
        (Term.optionCode (context := sourceCtx) outerLevel levelLe
          elementCodeRaw) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetElementCodeRaw elementSuccess
    cases success
    exact partialStrengthenTypedOptionCode_sound outerLevel levelLe
      elementCodeRaw targetElementCodeRaw elementSuccess

/-- Dispatcher soundness at the `Term.eitherCode` arm.  Either-type-code
closed leaf with two flat-scope raw witnesses (left + right summand
codes).  Universe-level positional forwarding identical to arrow. -/
theorem partialStrengthenTyped?_atEitherCode_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm sourceScope)
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.eitherCode (context := sourceCtx) outerLevel levelLe
        leftCodeRaw rightCodeRaw))
    (success : partialStrengthenTyped?
        (Term.eitherCode (context := sourceCtx) outerLevel levelLe
          leftCodeRaw rightCodeRaw) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetLeftCodeRaw leftSuccess
    split at success
    · cases success
    · rename_i targetRightCodeRaw rightSuccess
      cases success
      exact partialStrengthenTypedEitherCode_sound outerLevel levelLe
        leftCodeRaw rightCodeRaw targetLeftCodeRaw
        targetRightCodeRaw leftSuccess rightSuccess

/-- Dispatcher soundness at the `Term.idCode` arm.  Identity-type-code
closed leaf with THREE flat-scope raw witnesses (typeCode + left
endpoint + right endpoint).  Three nested `split at success` calls
plus three sequential `rename_i` to peel each Option layer. -/
theorem partialStrengthenTyped?_atIdCode_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (typeCodeRaw leftRaw rightRaw : RawTerm sourceScope)
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.idCode (context := sourceCtx) outerLevel levelLe
        typeCodeRaw leftRaw rightRaw))
    (success : partialStrengthenTyped?
        (Term.idCode (context := sourceCtx) outerLevel levelLe
          typeCodeRaw leftRaw rightRaw) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetTypeCodeRaw typeSuccess
    split at success
    · cases success
    · rename_i targetLeftRaw leftSuccess
      split at success
      · cases success
      · rename_i targetRightRaw rightSuccess
        cases success
        exact partialStrengthenTypedIdCode_sound outerLevel levelLe
          typeCodeRaw leftRaw rightRaw targetTypeCodeRaw
          targetLeftRaw targetRightRaw typeSuccess leftSuccess
          rightSuccess

/-- Dispatcher soundness at the `Term.equivCode` arm.  Equivalence-
type-code closed leaf with two flat-scope raw witnesses
(`leftTypeCodeRaw` + `rightTypeCodeRaw`).  Structurally identical to
`eitherCode`. -/
theorem partialStrengthenTyped?_atEquivCode_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftTypeCodeRaw rightTypeCodeRaw : RawTerm sourceScope)
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.equivCode (context := sourceCtx) outerLevel levelLe
        leftTypeCodeRaw rightTypeCodeRaw))
    (success : partialStrengthenTyped?
        (Term.equivCode (context := sourceCtx) outerLevel levelLe
          leftTypeCodeRaw rightTypeCodeRaw) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetLeftTypeCodeRaw leftSuccess
    split at success
    · cases success
    · rename_i targetRightTypeCodeRaw rightSuccess
      cases success
      exact partialStrengthenTypedEquivCode_sound outerLevel levelLe
        leftTypeCodeRaw rightTypeCodeRaw targetLeftTypeCodeRaw
        targetRightTypeCodeRaw leftSuccess rightSuccess

/-- Dispatcher soundness at the `Term.universeCode` arm.  The bare-
universe-of-codes producer carries no scope-dependent payload; the
dispatcher returns the wrapper unconditionally and the leaf simply
`cases success` and applies the wrapper's `_sound` companion. -/
theorem partialStrengthenTyped?_atUniverseCode_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.universeCode (context := sourceCtx) innerLevel outerLevel
        cumulOk levelLe))
    (success : partialStrengthenTyped?
        (Term.universeCode (context := sourceCtx) innerLevel outerLevel
          cumulOk levelLe) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  cases success
  exact partialStrengthenTypedUniverseCode_sound strengthening
    innerLevel outerLevel cumulOk levelLe

/-- Dispatcher soundness at the `Term.funextRefl` arm.  Closed-leaf
canonical funext reflexivity: two flat type witnesses (`domainType`
and `codomainType`) plus one lifted raw witness (`applyRaw` at
`scope + 1`).  No value IH. -/
theorem partialStrengthenTyped?_atFunextRefl_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (domainType codomainType : Ty level sourceScope)
    (applyRaw : RawTerm (sourceScope + 1))
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.funextRefl (context := sourceCtx) domainType codomainType
        applyRaw))
    (success : partialStrengthenTyped?
        (Term.funextRefl (context := sourceCtx) domainType codomainType
          applyRaw) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetDomainType domainSuccess
    split at success
    · cases success
    · rename_i targetCodomainType codomainSuccess
      split at success
      · cases success
      · rename_i targetApplyRaw applySuccess
        cases success
        exact partialStrengthenTypedFunextRefl_sound domainType
          codomainType targetDomainType targetCodomainType applyRaw
          targetApplyRaw domainSuccess codomainSuccess applySuccess

/-- Dispatcher soundness at the `Term.equivReflIdAtId` arm.  Closed-
leaf equivalence-reflexivity at the identity type: one positional
universe-level pair (`innerLevel`/`innerLevelLt`) + one type witness
(`carrier`) + one flat-scope raw witness (`carrierRaw`).  No value
IH. -/
theorem partialStrengthenTyped?_atEquivReflIdAtId_imp_sound
    {mode : Mode} {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level sourceScope)
    (carrierRaw : RawTerm sourceScope)
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.equivReflIdAtId (context := sourceCtx) innerLevel
        innerLevelLt carrier carrierRaw))
    (success : partialStrengthenTyped?
        (Term.equivReflIdAtId (context := sourceCtx) innerLevel
          innerLevelLt carrier carrierRaw) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetCarrier carrierSuccess
    split at success
    · cases success
    · rename_i targetCarrierRaw carrierRawSuccess
      cases success
      exact partialStrengthenTypedEquivReflIdAtId_sound innerLevel
        innerLevelLt carrier targetCarrier carrierRaw targetCarrierRaw
        carrierSuccess carrierRawSuccess

/-- Dispatcher soundness at the `Term.funextReflAtId` arm.
Structurally identical to `funextRefl` — two flat type witnesses plus
one lifted raw witness; only the wrapper's resulting type differs
(Id-typed instead of canonical funext form). -/
theorem partialStrengthenTyped?_atFunextReflAtId_imp_sound {mode : Mode}
    {level : Nat} {sourceScope targetScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {targetCtx : Ctx mode level targetScope}
    (domainType codomainType : Ty level sourceScope)
    (applyRaw : RawTerm (sourceScope + 1))
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening
      (Term.funextReflAtId (context := sourceCtx) domainType
        codomainType applyRaw))
    (success : partialStrengthenTyped?
        (Term.funextReflAtId (context := sourceCtx) domainType
          codomainType applyRaw) strengthening =
          some result) :
    StrengtheningSoundness result := by
  unfold partialStrengthenTyped? at success
  split at success
  · cases success
  · rename_i targetDomainType domainSuccess
    split at success
    · cases success
    · rename_i targetCodomainType codomainSuccess
      split at success
      · cases success
      · rename_i targetApplyRaw applySuccess
        cases success
        exact partialStrengthenTypedFunextReflAtId_sound domainType
          codomainType targetDomainType targetCodomainType applyRaw
          targetApplyRaw domainSuccess codomainSuccess applySuccess

end Term

end LeanFX2
