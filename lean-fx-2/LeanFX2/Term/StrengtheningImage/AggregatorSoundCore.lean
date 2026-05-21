import LeanFX2.Term.StrengtheningImage.DispatcherBasicCollections
import LeanFX2.Term.StrengtheningImage.DispatcherStructured
import LeanFX2.Term.StrengtheningImage.DispatcherEliminatorsApplications
import LeanFX2.Term.StrengtheningImage.DispatcherAtomicTypeCodes
import LeanFX2.Term.StrengtheningImage.DispatcherAdvanced

/-! # Term/StrengtheningImage/AggregatorSoundCore

Aggregator-soundness predicate and atomic/type-code constructor instances.
-/

namespace LeanFX2

namespace Term

/-! ## Headline aggregator infrastructure

The layer above the 78 per-arm dispatcher leaves
(`partialStrengthenTyped?_at<Ctor>_imp_sound`) is the full structural
aggregator: for any typed source term, a successful
`partialStrengthenTyped?` result satisfies `StrengtheningSoundness`.
The universal theorem itself lives in
`AggregatorSoundUniversal.lean`; this file defines the uniform
predicate and the per-constructor wrappers consumed by that theorem. -/

/-- The aggregator-soundness property for a typed source term.

`IsAggregatorSound sourceTerm` asserts that for ANY context
strengthening from `sourceTerm`'s context, ANY successful dispatch
of `partialStrengthenTyped?` produces a result whose recovery
equations hold (via `StrengtheningSoundness`).

The 78 per-arm dispatcher leaves
`partialStrengthenTyped?_at<Ctor>_imp_sound` each prove this
property for terms whose head constructor is the respective ctor,
under inductive hypotheses for the recursive children.

The full aggregator is the headline theorem
`∀ sourceTerm, IsAggregatorSound sourceTerm`, proved by structural
induction on `Term`; this file ships the predicate plus the `var`
base case as scaffolding. -/
def IsAggregatorSound {mode : Mode} {level : Nat} {sourceScope : Nat}
    {sourceCtx : Ctx mode level sourceScope}
    {ty : Ty level sourceScope} {rawTerm : RawTerm sourceScope}
    (sourceTerm : Term sourceCtx ty rawTerm) : Prop :=
  ∀ {targetScope : Nat} {targetCtx : Ctx mode level targetScope}
    (strengthening : ContextStrengthening sourceCtx targetCtx)
    (result : StrengtheningResult strengthening sourceTerm),
    partialStrengthenTyped? sourceTerm strengthening = some result →
    StrengtheningSoundness result

/-- Headline aggregator soundness at the `Term.var` arm.

Lifts `partialStrengthenTyped?_atVar_imp_sound` into the uniform
`IsAggregatorSound` predicate shape consumed by downstream image
theorems (Steps 2–4 of `Term.weaken` strengthening invertibility).

The proof is a single-line delegation: `intros _ _ str res suc`
introduces the universally-quantified strengthening / result /
success arguments, then `exact` calls the per-arm leaf.

This is the variable arm in the 78-wrapper family composed by
`isAggregatorSound_universal`. -/
theorem isAggregatorSound_var {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (sourcePosition : Fin sourceScope) :
    IsAggregatorSound
      (Term.var (context := sourceCtx) sourcePosition) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atVar_imp_sound sourcePosition
    strengthening result success

/-- Headline aggregator soundness at the `Term.unit` arm.

Lifts `partialStrengthenTyped?_atUnit_imp_sound` into the uniform
`IsAggregatorSound` predicate shape.  Second zero-IH closed-atomic
ctor; confirms the template scales identically to `var` with no
ctor-specific positional arguments — the leaf takes only
strengthening / result / success. -/
theorem isAggregatorSound_unit {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope} :
    IsAggregatorSound (Term.unit (context := sourceCtx)) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atUnit_imp_sound strengthening result
    success

/-- Headline aggregator soundness at the `Term.boolTrue` arm. -/
theorem isAggregatorSound_boolTrue {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope} :
    IsAggregatorSound (Term.boolTrue (context := sourceCtx)) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atBoolTrue_imp_sound strengthening
    result success

/-- Headline aggregator soundness at the `Term.boolFalse` arm. -/
theorem isAggregatorSound_boolFalse {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope} :
    IsAggregatorSound (Term.boolFalse (context := sourceCtx)) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atBoolFalse_imp_sound strengthening
    result success

/-- Headline aggregator soundness at the `Term.natZero` arm. -/
theorem isAggregatorSound_natZero {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope} :
    IsAggregatorSound (Term.natZero (context := sourceCtx)) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atNatZero_imp_sound strengthening
    result success

/-- Headline aggregator soundness at the `Term.interval0` arm. -/
theorem isAggregatorSound_interval0 {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope} :
    IsAggregatorSound (Term.interval0 (context := sourceCtx)) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atInterval0_imp_sound strengthening
    result success

/-- Headline aggregator soundness at the `Term.interval1` arm. -/
theorem isAggregatorSound_interval1 {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope} :
    IsAggregatorSound (Term.interval1 (context := sourceCtx)) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atInterval1_imp_sound strengthening
    result success

/-- Headline aggregator soundness at the `Term.listNil` arm.  Takes
the element type explicitly (parametric closed value). -/
theorem isAggregatorSound_listNil {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (elementType : Ty level sourceScope) :
    IsAggregatorSound
      (Term.listNil (context := sourceCtx)
        (elementType := elementType)) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atListNil_imp_sound elementType
    strengthening result success

/-- Headline aggregator soundness at the `Term.optionNone` arm. -/
theorem isAggregatorSound_optionNone {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (elementType : Ty level sourceScope) :
    IsAggregatorSound
      (Term.optionNone (context := sourceCtx)
        (elementType := elementType)) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atOptionNone_imp_sound elementType
    strengthening result success

/-- Headline aggregator soundness at the `Term.refl` arm.  HoTT
identity-refl: takes carrier type and raw witness as implicits
matching the leaf's signature. -/
theorem isAggregatorSound_refl {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {carrier : Ty level sourceScope} {rawWitness : RawTerm sourceScope} :
    IsAggregatorSound
      (Term.refl (context := sourceCtx) (carrier := carrier)
        rawWitness) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atRefl_imp_sound strengthening result
    success

/-- Headline aggregator soundness at the `Term.oeqRefl` arm.
Observational-equality refl mirrors `refl`. -/
theorem isAggregatorSound_oeqRefl {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {carrier : Ty level sourceScope} {rawWitness : RawTerm sourceScope} :
    IsAggregatorSound
      (Term.oeqRefl (context := sourceCtx) (carrier := carrier)
        rawWitness) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atOeqRefl_imp_sound strengthening
    result success

/-- Headline aggregator soundness at the `Term.idStrictRefl` arm.
Strict-mode identity refl carries a mode-equality witness plus
carrier and raw witness. -/
theorem isAggregatorSound_idStrictRefl {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {modeIsStrict : mode = Mode.strict}
    {carrier : Ty level sourceScope} {rawWitness : RawTerm sourceScope} :
    IsAggregatorSound
      (Term.idStrictRefl (context := sourceCtx) (carrier := carrier)
        modeIsStrict rawWitness) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atIdStrictRefl_imp_sound strengthening
    result success

/-- Headline aggregator soundness at the `Term.equivReflId` arm.
Identity-as-equivalence: carrier-only zero-IH closed-atomic. -/
theorem isAggregatorSound_equivReflId {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {carrier : Ty level sourceScope} :
    IsAggregatorSound
      (Term.equivReflId (context := sourceCtx)
        (carrier := carrier)) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atEquivReflId_imp_sound strengthening
    result success

/-- Headline aggregator soundness at the `Term.arrowCode` arm.
Universe-level forwarding + two flat-scope raw witnesses. -/
theorem isAggregatorSound_arrowCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw codomainCodeRaw : RawTerm sourceScope) :
    IsAggregatorSound
      (Term.arrowCode (context := sourceCtx) outerLevel levelLe
        domainCodeRaw codomainCodeRaw) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atArrowCode_imp_sound outerLevel levelLe
    domainCodeRaw codomainCodeRaw strengthening result success

/-- Headline aggregator soundness at the `Term.piTyCode` arm.
One flat-scope raw + one lifted raw (codomain at `scope + 1`). -/
theorem isAggregatorSound_piTyCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm sourceScope)
    (codomainCodeRaw : RawTerm (sourceScope + 1)) :
    IsAggregatorSound
      (Term.piTyCode (context := sourceCtx) outerLevel levelLe
        domainCodeRaw codomainCodeRaw) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atPiTyCode_imp_sound outerLevel levelLe
    domainCodeRaw codomainCodeRaw strengthening result success

/-- Headline aggregator soundness at the `Term.sigmaTyCode` arm.
Structurally identical to `piTyCode`. -/
theorem isAggregatorSound_sigmaTyCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm sourceScope)
    (codomainCodeRaw : RawTerm (sourceScope + 1)) :
    IsAggregatorSound
      (Term.sigmaTyCode (context := sourceCtx) outerLevel levelLe
        domainCodeRaw codomainCodeRaw) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atSigmaTyCode_imp_sound outerLevel
    levelLe domainCodeRaw codomainCodeRaw strengthening result success

/-- Headline aggregator soundness at the `Term.productCode` arm.
Two flat-scope raw witnesses (first + second components). -/
theorem isAggregatorSound_productCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (firstCodeRaw secondCodeRaw : RawTerm sourceScope) :
    IsAggregatorSound
      (Term.productCode (context := sourceCtx) outerLevel levelLe
        firstCodeRaw secondCodeRaw) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atProductCode_imp_sound outerLevel
    levelLe firstCodeRaw secondCodeRaw strengthening result success

/-- Headline aggregator soundness at the `Term.sumCode` arm.
Binary sum: left + right summand codes. -/
theorem isAggregatorSound_sumCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm sourceScope) :
    IsAggregatorSound
      (Term.sumCode (context := sourceCtx) outerLevel levelLe
        leftCodeRaw rightCodeRaw) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atSumCode_imp_sound outerLevel levelLe
    leftCodeRaw rightCodeRaw strengthening result success

/-- Headline aggregator soundness at the `Term.listCode` arm.
Single flat-scope element-code raw. -/
theorem isAggregatorSound_listCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm sourceScope) :
    IsAggregatorSound
      (Term.listCode (context := sourceCtx) outerLevel levelLe
        elementCodeRaw) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atListCode_imp_sound outerLevel levelLe
    elementCodeRaw strengthening result success

/-- Headline aggregator soundness at the `Term.optionCode` arm.
Structurally identical to `listCode`. -/
theorem isAggregatorSound_optionCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm sourceScope) :
    IsAggregatorSound
      (Term.optionCode (context := sourceCtx) outerLevel levelLe
        elementCodeRaw) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atOptionCode_imp_sound outerLevel
    levelLe elementCodeRaw strengthening result success

/-- Headline aggregator soundness at the `Term.eitherCode` arm.
Two flat-scope summand-code raws. -/
theorem isAggregatorSound_eitherCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm sourceScope) :
    IsAggregatorSound
      (Term.eitherCode (context := sourceCtx) outerLevel levelLe
        leftCodeRaw rightCodeRaw) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atEitherCode_imp_sound outerLevel
    levelLe leftCodeRaw rightCodeRaw strengthening result success

/-- Headline aggregator soundness at the `Term.idCode` arm.
Three flat-scope raws: type-code + left + right endpoints. -/
theorem isAggregatorSound_idCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (typeCodeRaw leftRaw rightRaw : RawTerm sourceScope) :
    IsAggregatorSound
      (Term.idCode (context := sourceCtx) outerLevel levelLe
        typeCodeRaw leftRaw rightRaw) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atIdCode_imp_sound outerLevel levelLe
    typeCodeRaw leftRaw rightRaw strengthening result success

/-- Headline aggregator soundness at the `Term.equivCode` arm.
Structurally identical to `eitherCode`. -/
theorem isAggregatorSound_equivCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftTypeCodeRaw rightTypeCodeRaw : RawTerm sourceScope) :
    IsAggregatorSound
      (Term.equivCode (context := sourceCtx) outerLevel levelLe
        leftTypeCodeRaw rightTypeCodeRaw) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atEquivCode_imp_sound outerLevel
    levelLe leftTypeCodeRaw rightTypeCodeRaw strengthening result
    success

/-- Headline aggregator soundness at the `Term.universeCode` arm.
Bare universe-of-codes carrying inner/outer level + cumulativity
proof + outer-bound proof; no raw payload. -/
theorem isAggregatorSound_universeCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    IsAggregatorSound
      (Term.universeCode (context := sourceCtx) innerLevel outerLevel
        cumulOk levelLe) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atUniverseCode_imp_sound innerLevel
    outerLevel cumulOk levelLe strengthening result success

/-- Headline aggregator soundness at the `Term.funextRefl` arm.  Two
flat type witnesses + one lifted raw witness at `scope + 1`. -/
theorem isAggregatorSound_funextRefl {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (domainType codomainType : Ty level sourceScope)
    (applyRaw : RawTerm (sourceScope + 1)) :
    IsAggregatorSound
      (Term.funextRefl (context := sourceCtx) domainType codomainType
        applyRaw) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atFunextRefl_imp_sound domainType
    codomainType applyRaw strengthening result success

/-- Headline aggregator soundness at the `Term.equivReflIdAtId` arm.
Inner-universe-level pair + carrier type + flat raw witness. -/
theorem isAggregatorSound_equivReflIdAtId {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (innerLevel : UniverseLevel)
    (innerLevelLt : innerLevel.toNat + 1 ≤ level)
    (carrier : Ty level sourceScope)
    (carrierRaw : RawTerm sourceScope) :
    IsAggregatorSound
      (Term.equivReflIdAtId (context := sourceCtx) innerLevel
        innerLevelLt carrier carrierRaw) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atEquivReflIdAtId_imp_sound innerLevel
    innerLevelLt carrier carrierRaw strengthening result success

/-- Headline aggregator soundness at the `Term.funextReflAtId` arm.
Structurally identical to `funextRefl`; differs only in resulting
wrapper type (Id-typed vs canonical funext form). -/
theorem isAggregatorSound_funextReflAtId {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (domainType codomainType : Ty level sourceScope)
    (applyRaw : RawTerm (sourceScope + 1)) :
    IsAggregatorSound
      (Term.funextReflAtId (context := sourceCtx) domainType
        codomainType applyRaw) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atFunextReflAtId_imp_sound domainType
    codomainType applyRaw strengthening result success

/-- Headline aggregator soundness at the `Term.funextIntroHet` arm.
Two flat type witnesses + two lifted raw witnesses at `scope + 1`. -/
theorem isAggregatorSound_funextIntroHet {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (domainType codomainType : Ty level sourceScope)
    (applyARaw applyBRaw : RawTerm (sourceScope + 1)) :
    IsAggregatorSound
      (Term.funextIntroHet (context := sourceCtx) domainType
        codomainType applyARaw applyBRaw) := by
  intros _ _ strengthening result success
  exact partialStrengthenTyped?_atFunextIntroHet_imp_sound domainType
    codomainType applyARaw applyBRaw strengthening result success

end Term

end LeanFX2
