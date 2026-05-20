import LeanFX2.Term.StrengtheningImage.AggregatorTotalUnary

/-! # Term/StrengtheningImage/AggregatorTotalCodesRefl

Aggregator totality wrappers for parametric atoms, reflexivity, universe, cumulativity, and type-code constructors.
-/

namespace LeanFX2

namespace Term

/-! ## Wave T2: 0-IH parametric atomic totality wrappers.

These ctors have no Term recursive children but carry one or more
`Ty`/`RawTerm` payloads at the source scope.  The dispatcher inspects
each payload's `partialStrengthen?`; success comes either from
extracting the strengthening witness out of `typeStrengthens`
(when the payload appears in the source type) or from
`rawStrengthens` (when the payload appears in the source raw form). -/

/-- 0-IH parametric atomic totality: `Term.listNil`.  Source type is
`Ty.listType elementType`; the dispatcher inspects
`elementType.partialStrengthen?`.  Extract via the inner match. -/
theorem isAggregatorTotal_listNil {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {elementType : Ty level sourceScope} :
    IsAggregatorTotal
      (Term.listNil (context := sourceCtx) (elementType := elementType)) := by
  intros _ _ strengthening _ _ typeStrengthens _
  unfold Ty.partialStrengthen? at typeStrengthens
  split at typeStrengthens
  · next strengthenedElement elementSuccess =>
      unfold partialStrengthenTyped?
      split
      · next elementFails =>
          rw [elementSuccess] at elementFails
          cases elementFails
      · rfl
  · next elementFails =>
      cases typeStrengthens

/-- 0-IH parametric atomic totality: `Term.optionNone`.  Same pattern
as `listNil` — Ty.optionType payload. -/
theorem isAggregatorTotal_optionNone {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {elementType : Ty level sourceScope} :
    IsAggregatorTotal
      (Term.optionNone (context := sourceCtx) (elementType := elementType)) := by
  intros _ _ strengthening _ _ typeStrengthens _
  unfold Ty.partialStrengthen? at typeStrengthens
  split at typeStrengthens
  · next strengthenedElement elementSuccess =>
      unfold partialStrengthenTyped?
      split
      · next elementFails =>
          rw [elementSuccess] at elementFails
          cases elementFails
      · rfl
  · next elementFails =>
      cases typeStrengthens

/-! ## Wave T3: 2-IH listCons totality.

Both head (elementType) and tail (Ty.listType elementType) have types
encodable from source type's elementType.  The dispatcher recurses on
each child without splitting on the type payload.  Reconstruct
Ty.listType strengthening from typeStrengthens for the tail IH. -/

/-- 2-IH non-binder totality: `Term.listCons`.  Source type is
`Ty.listType elementType`; head type is `elementType`, tail type is
`Ty.listType elementType` (same as source). -/
theorem isAggregatorTotal_listCons {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {elementType : Ty level sourceScope}
    {headRaw tailRaw : RawTerm sourceScope}
    {headTerm : Term sourceCtx elementType headRaw}
    {tailTerm : Term sourceCtx (Ty.listType elementType) tailRaw}
    (headTotal : IsAggregatorTotal headTerm)
    (tailTotal : IsAggregatorTotal tailTerm) :
    IsAggregatorTotal
      (Term.listCons (headTerm := headTerm) (tailTerm := tailTerm)) := by
  intros _ _ strengthening _ _ typeStrengthens rawStrengthens
  -- Extract elementType strengthening from typeStrengthens.
  have elementSuccessExists : ∃ targetElement,
      elementType.partialStrengthen? strengthening.back = some targetElement := by
    rcases hElem : elementType.partialStrengthen? strengthening.back with _ | tgt
    · simp only [Ty.partialStrengthen?, hElem] at typeStrengthens
      cases typeStrengthens
    · exact ⟨tgt, rfl⟩
  obtain ⟨targetElement, elementSuccess⟩ := elementSuccessExists
  unfold partialStrengthenTyped?
  unfold RawTerm.partialStrengthen? at rawStrengthens
  unfold RawTerm.partialRename? at rawStrengthens
  -- rawStrengthens = Option.mapTwo head tail RawTerm.listCons = some _
  obtain ⟨_, _, headRawSuccess, tailRawSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  have headTotalCall :=
    headTotal strengthening elementSuccess headRawSuccess
  have tailTotalCall :=
    tailTotal strengthening typeStrengthens tailRawSuccess
  split
  · next headFails =>
      rw [headFails] at headTotalCall
      cases headTotalCall
  · next _ _ =>
      split
      · next tailFails =>
          rw [tailFails] at tailTotalCall
          cases tailTotalCall
      · rfl

/-! ## Wave T4: 2-IH non-binder totality (atomic Ty children) -/

/-- 2-IH non-binder totality: `Term.intervalMeet`.  Children have type
`Ty.interval` (atomic); both Ty strengthens are `rfl`. -/
theorem isAggregatorTotal_intervalMeet {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {leftRaw rightRaw : RawTerm sourceScope}
    {leftValue : Term sourceCtx Ty.interval leftRaw}
    {rightValue : Term sourceCtx Ty.interval rightRaw}
    (leftTotal : IsAggregatorTotal leftValue)
    (rightTotal : IsAggregatorTotal rightValue) :
    IsAggregatorTotal
      (Term.intervalMeet (leftValue := leftValue) (rightValue := rightValue)) := by
  intros _ _ strengthening _ _ _ rawStrengthens
  unfold partialStrengthenTyped?
  unfold RawTerm.partialStrengthen? at rawStrengthens
  unfold RawTerm.partialRename? at rawStrengthens
  obtain ⟨_, _, leftRawSuccess, rightRawSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  have intervalStrengthens :
      (Ty.interval : Ty level sourceScope).partialStrengthen?
          strengthening.back =
        some Ty.interval := rfl
  have leftTotalCall :=
    leftTotal strengthening intervalStrengthens leftRawSuccess
  have rightTotalCall :=
    rightTotal strengthening intervalStrengthens rightRawSuccess
  split
  · next leftFails =>
      rw [leftFails] at leftTotalCall
      cases leftTotalCall
  · next _ _ =>
      split
      · next rightFails =>
          rw [rightFails] at rightTotalCall
          cases rightTotalCall
      · rfl

/-- 2-IH non-binder totality: `Term.intervalJoin`.  Mirror of
`intervalMeet`. -/
theorem isAggregatorTotal_intervalJoin {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {leftRaw rightRaw : RawTerm sourceScope}
    {leftValue : Term sourceCtx Ty.interval leftRaw}
    {rightValue : Term sourceCtx Ty.interval rightRaw}
    (leftTotal : IsAggregatorTotal leftValue)
    (rightTotal : IsAggregatorTotal rightValue) :
    IsAggregatorTotal
      (Term.intervalJoin (leftValue := leftValue) (rightValue := rightValue)) := by
  intros _ _ strengthening _ _ _ rawStrengthens
  unfold partialStrengthenTyped?
  unfold RawTerm.partialStrengthen? at rawStrengthens
  unfold RawTerm.partialRename? at rawStrengthens
  obtain ⟨_, _, leftRawSuccess, rightRawSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  have intervalStrengthens :
      (Ty.interval : Ty level sourceScope).partialStrengthen?
          strengthening.back =
        some Ty.interval := rfl
  have leftTotalCall :=
    leftTotal strengthening intervalStrengthens leftRawSuccess
  have rightTotalCall :=
    rightTotal strengthening intervalStrengthens rightRawSuccess
  split
  · next leftFails =>
      rw [leftFails] at leftTotalCall
      cases leftTotalCall
  · next _ _ =>
      split
      · next rightFails =>
          rw [rightFails] at rightTotalCall
          cases rightTotalCall
      · rfl

/-! ## Wave T5: 0-IH parametric atomic with Ty + Raw payloads (refl-family) -/

/-- 0-IH parametric atomic totality: `Term.refl`.  Source type is
`Ty.id carrier rawWitness rawWitness`; dispatcher inspects carrier
+ rawWitness strengthens.  Extract via Option.mapThree from
typeStrengthens. -/
theorem isAggregatorTotal_refl {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (carrier : Ty level sourceScope) (rawWitness : RawTerm sourceScope) :
    IsAggregatorTotal (Term.refl (context := sourceCtx) carrier rawWitness) := by
  intros _ _ strengthening _ _ typeStrengthens _
  obtain ⟨_, _, _, carrierSuccess, witnessSuccess, _, _⟩ :=
    Option.mapThree_eq_some typeStrengthens
  unfold partialStrengthenTyped?
  split
  · next carrierFails =>
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · next _ _ =>
      split
      · next witnessFails =>
          rw [witnessSuccess] at witnessFails
          cases witnessFails
      · rfl

/-- 0-IH parametric atomic totality: `Term.oeqRefl`.  Same shape as
`refl` — source type `Ty.oeq carrier rawWitness rawWitness`. -/
theorem isAggregatorTotal_oeqRefl {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (carrier : Ty level sourceScope) (rawWitness : RawTerm sourceScope) :
    IsAggregatorTotal (Term.oeqRefl (context := sourceCtx) carrier rawWitness) := by
  intros _ _ strengthening _ _ typeStrengthens _
  obtain ⟨_, _, _, carrierSuccess, witnessSuccess, _, _⟩ :=
    Option.mapThree_eq_some typeStrengthens
  unfold partialStrengthenTyped?
  split
  · next carrierFails =>
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · next _ _ =>
      split
      · next witnessFails =>
          rw [witnessSuccess] at witnessFails
          cases witnessFails
      · rfl

/-- 0-IH parametric atomic totality: `Term.idStrictRefl`.  Source type
`Ty.idStrict carrier rawWitness rawWitness` plus a `modeIsStrict`
value-level parameter. -/
theorem isAggregatorTotal_idStrictRefl {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (modeIsStrict : mode = Mode.strict)
    (carrier : Ty level sourceScope) (rawWitness : RawTerm sourceScope) :
    IsAggregatorTotal
      (Term.idStrictRefl (context := sourceCtx) modeIsStrict carrier rawWitness) := by
  intros _ _ strengthening _ _ typeStrengthens _
  obtain ⟨_, _, _, carrierSuccess, witnessSuccess, _, _⟩ :=
    Option.mapThree_eq_some typeStrengthens
  unfold partialStrengthenTyped?
  split
  · next carrierFails =>
      rw [carrierSuccess] at carrierFails
      cases carrierFails
  · next _ _ =>
      split
      · next witnessFails =>
          rw [witnessSuccess] at witnessFails
          cases witnessFails
      · rfl

/-! ## Wave T6: 0-IH `Term.universeCode` + `cumulUp` totality. -/

/-- 0-IH totality: `Term.universeCode`.  Atomic ctor — the dispatcher
returns `some _` unconditionally because the source type
`Ty.universe outerLevel levelLe` is closed-atomic (scope-independent)
and the raw form `RawTerm.universeCode innerLevel.toNat` strengthens
trivially. -/
theorem isAggregatorTotal_universeCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    IsAggregatorTotal (Term.universeCode (context := sourceCtx)
      innerLevel outerLevel cumulOk levelLe) := by
  intros _ _ strengthening _ _ _ _
  rfl

/-- 1-IH totality: `Term.cumulUp`.  Source raw is
`RawTerm.cumulUpMarker codeRaw`; wrapped type code's type is
`Ty.universe lowerLevel levelLeLow`, closed-atomic. -/
theorem isAggregatorTotal_cumulUp {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (lowerLevel higherLevel : UniverseLevel)
    (cumulMonotone : lowerLevel.toNat ≤ higherLevel.toNat)
    (levelLeLow : lowerLevel.toNat + 1 ≤ level)
    (levelLeHigh : higherLevel.toNat + 1 ≤ level)
    {codeRaw : RawTerm sourceScope}
    {typeCode : Term sourceCtx (Ty.universe lowerLevel levelLeLow) codeRaw}
    (codeTotal : IsAggregatorTotal typeCode) :
    IsAggregatorTotal
      (Term.cumulUp lowerLevel higherLevel cumulMonotone
        levelLeLow levelLeHigh typeCode) := by
  intros _ _ strengthening _ _ _ rawStrengthens
  -- typeCode's type Ty.universe is closed-atomic; strengthening always succeeds.
  have universeStrengthens :
      (Ty.universe lowerLevel levelLeLow : Ty level sourceScope).partialStrengthen?
          strengthening.back =
        some (Ty.universe lowerLevel levelLeLow) := rfl
  -- Extract codeRaw strengthens from rawStrengthens (RawTerm.cumulUpMarker).
  unfold RawTerm.partialStrengthen? at rawStrengthens
  unfold RawTerm.partialRename? at rawStrengthens
  split at rawStrengthens
  rotate_left
  · cases rawStrengthens
  next targetCodeRaw codeRawSuccess =>
    have codeTotalCall :=
      codeTotal strengthening universeStrengthens codeRawSuccess
    unfold partialStrengthenTyped?
    split
    · next codeFails =>
        rw [codeFails] at codeTotalCall
        cases codeTotalCall
    · rfl

/-! ## Wave T7: 0-IH type codes (arrow / piTy / sigmaTy / product / sum /
    list / option / either / id / equiv / equivReflId-family / funext-family). -/

/-- 0-IH totality: `Term.arrowCode`.  Source type is
`Ty.universe outerLevel levelLe` (atomic); raw form
`RawTerm.arrowCode domainCodeRaw codomainCodeRaw`.  Dispatcher splits
on each raw payload's strengthening — both succeed via rawStrengthens
mapTwo decomposition. -/
theorem isAggregatorTotal_arrowCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel) (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw codomainCodeRaw : RawTerm sourceScope) :
    IsAggregatorTotal (Term.arrowCode (context := sourceCtx)
      outerLevel levelLe domainCodeRaw codomainCodeRaw) := by
  intros _ _ strengthening _ _ _ rawStrengthens
  -- rawStrengthens unfolds (via @[reducible]) to mapTwo form.
  change Option.mapTwo
      (domainCodeRaw.partialStrengthen? strengthening.back)
      (codomainCodeRaw.partialStrengthen? strengthening.back)
      RawTerm.arrowCode = some _ at rawStrengthens
  obtain ⟨_, _, domainSuccess, codomainSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  unfold partialStrengthenTyped?
  split
  · next domainFails =>
      rw [domainSuccess] at domainFails
      cases domainFails
  · next _ _ =>
      split
      · next codomainFails =>
          rw [codomainSuccess] at codomainFails
          cases codomainFails
      · rfl

/-- 0-IH totality: `Term.piTyCode`.  Same as arrowCode but codomain
strengthens at lifted strengthening (piTy's binder shape). -/
theorem isAggregatorTotal_piTyCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel) (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm sourceScope)
    (codomainCodeRaw : RawTerm (sourceScope + 1)) :
    IsAggregatorTotal (Term.piTyCode (context := sourceCtx)
      outerLevel levelLe domainCodeRaw codomainCodeRaw) := by
  intros _ _ strengthening _ _ _ rawStrengthens
  change Option.mapTwo
      (domainCodeRaw.partialStrengthen? strengthening.back)
      (codomainCodeRaw.partialStrengthen? strengthening.back.lift)
      RawTerm.piTyCode = some _ at rawStrengthens
  obtain ⟨_, _, domainSuccess, codomainLiftSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  unfold partialStrengthenTyped?
  split
  · next domainFails =>
      rw [domainSuccess] at domainFails
      cases domainFails
  · next _ _ =>
      split
      · next codomainFails =>
          rw [codomainLiftSuccess] at codomainFails
          cases codomainFails
      · rfl

/-- 0-IH totality: `Term.sigmaTyCode`.  Same as piTyCode. -/
theorem isAggregatorTotal_sigmaTyCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel) (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm sourceScope)
    (codomainCodeRaw : RawTerm (sourceScope + 1)) :
    IsAggregatorTotal (Term.sigmaTyCode (context := sourceCtx)
      outerLevel levelLe domainCodeRaw codomainCodeRaw) := by
  intros _ _ strengthening _ _ _ rawStrengthens
  change Option.mapTwo
      (domainCodeRaw.partialStrengthen? strengthening.back)
      (codomainCodeRaw.partialStrengthen? strengthening.back.lift)
      RawTerm.sigmaTyCode = some _ at rawStrengthens
  obtain ⟨_, _, domainSuccess, codomainLiftSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  unfold partialStrengthenTyped?
  split
  · next domainFails =>
      rw [domainSuccess] at domainFails
      cases domainFails
  · next _ _ =>
      split
      · next codomainFails =>
          rw [codomainLiftSuccess] at codomainFails
          cases codomainFails
      · rfl

/-- 0-IH totality: `Term.productCode`.  Two-arg type code without
binder lifts. -/
theorem isAggregatorTotal_productCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel) (levelLe : outerLevel.toNat + 1 ≤ level)
    (firstCodeRaw secondCodeRaw : RawTerm sourceScope) :
    IsAggregatorTotal (Term.productCode (context := sourceCtx)
      outerLevel levelLe firstCodeRaw secondCodeRaw) := by
  intros _ _ strengthening _ _ _ rawStrengthens
  change Option.mapTwo
      (firstCodeRaw.partialStrengthen? strengthening.back)
      (secondCodeRaw.partialStrengthen? strengthening.back)
      RawTerm.productCode = some _ at rawStrengthens
  obtain ⟨_, _, firstSuccess, secondSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  unfold partialStrengthenTyped?
  split
  · next firstFails =>
      rw [firstSuccess] at firstFails
      cases firstFails
  · next _ _ =>
      split
      · next secondFails =>
          rw [secondSuccess] at secondFails
          cases secondFails
      · rfl

/-- 0-IH totality: `Term.sumCode`.  Mirror of productCode. -/
theorem isAggregatorTotal_sumCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel) (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm sourceScope) :
    IsAggregatorTotal (Term.sumCode (context := sourceCtx)
      outerLevel levelLe leftCodeRaw rightCodeRaw) := by
  intros _ _ strengthening _ _ _ rawStrengthens
  change Option.mapTwo
      (leftCodeRaw.partialStrengthen? strengthening.back)
      (rightCodeRaw.partialStrengthen? strengthening.back)
      RawTerm.sumCode = some _ at rawStrengthens
  obtain ⟨_, _, leftSuccess, rightSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  unfold partialStrengthenTyped?
  split
  · next leftFails =>
      rw [leftSuccess] at leftFails
      cases leftFails
  · next _ _ =>
      split
      · next rightFails =>
          rw [rightSuccess] at rightFails
          cases rightFails
      · rfl

/-- 0-IH totality: `Term.listCode`.  Single raw payload. -/
theorem isAggregatorTotal_listCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel) (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm sourceScope) :
    IsAggregatorTotal (Term.listCode (context := sourceCtx)
      outerLevel levelLe elementCodeRaw) := by
  intros _ _ strengthening _ _ _ rawStrengthens
  change (match elementCodeRaw.partialStrengthen? strengthening.back with
          | some renamed => some (RawTerm.listCode renamed)
          | none => none) = some _ at rawStrengthens
  split at rawStrengthens
  rotate_left
  · cases rawStrengthens
  next targetElementCodeRaw elementSuccess =>
    unfold partialStrengthenTyped?
    split
    · next elementFails =>
        rw [elementSuccess] at elementFails
        cases elementFails
    · rfl

/-- 0-IH totality: `Term.optionCode`.  Single raw payload. -/
theorem isAggregatorTotal_optionCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel) (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm sourceScope) :
    IsAggregatorTotal (Term.optionCode (context := sourceCtx)
      outerLevel levelLe elementCodeRaw) := by
  intros _ _ strengthening _ _ _ rawStrengthens
  change (match elementCodeRaw.partialStrengthen? strengthening.back with
          | some renamed => some (RawTerm.optionCode renamed)
          | none => none) = some _ at rawStrengthens
  split at rawStrengthens
  rotate_left
  · cases rawStrengthens
  next targetElementCodeRaw elementSuccess =>
    unfold partialStrengthenTyped?
    split
    · next elementFails =>
        rw [elementSuccess] at elementFails
        cases elementFails
    · rfl

/-- 0-IH totality: `Term.eitherCode`.  Two raw payloads. -/
theorem isAggregatorTotal_eitherCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel) (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm sourceScope) :
    IsAggregatorTotal (Term.eitherCode (context := sourceCtx)
      outerLevel levelLe leftCodeRaw rightCodeRaw) := by
  intros _ _ strengthening _ _ _ rawStrengthens
  change Option.mapTwo
      (leftCodeRaw.partialStrengthen? strengthening.back)
      (rightCodeRaw.partialStrengthen? strengthening.back)
      RawTerm.eitherCode = some _ at rawStrengthens
  obtain ⟨_, _, leftSuccess, rightSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  unfold partialStrengthenTyped?
  split
  · next leftFails =>
      rw [leftSuccess] at leftFails
      cases leftFails
  · next _ _ =>
      split
      · next rightFails =>
          rw [rightSuccess] at rightFails
          cases rightFails
      · rfl

/-- 0-IH totality: `Term.idCode`.  Three raw payloads (type code,
left endpoint, right endpoint).  Use mapThree. -/
theorem isAggregatorTotal_idCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel) (levelLe : outerLevel.toNat + 1 ≤ level)
    (typeCodeRaw leftRaw rightRaw : RawTerm sourceScope) :
    IsAggregatorTotal (Term.idCode (context := sourceCtx)
      outerLevel levelLe typeCodeRaw leftRaw rightRaw) := by
  intros _ _ strengthening _ _ _ rawStrengthens
  change Option.mapThree
      (typeCodeRaw.partialStrengthen? strengthening.back)
      (leftRaw.partialStrengthen? strengthening.back)
      (rightRaw.partialStrengthen? strengthening.back)
      RawTerm.idCode = some _ at rawStrengthens
  obtain ⟨_, _, _, typeCodeSuccess, leftSuccess, rightSuccess, _⟩ :=
    Option.mapThree_eq_some rawStrengthens
  unfold partialStrengthenTyped?
  split
  · next typeCodeFails =>
      rw [typeCodeSuccess] at typeCodeFails
      cases typeCodeFails
  · next _ _ =>
      split
      · next leftFails =>
          rw [leftSuccess] at leftFails
          cases leftFails
      · next _ _ =>
          split
          · next rightFails =>
              rw [rightSuccess] at rightFails
              cases rightFails
          · rfl

/-- 0-IH totality: `Term.equivCode`.  Two raw payloads (left/right
type codes). -/
theorem isAggregatorTotal_equivCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel) (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftTypeCodeRaw rightTypeCodeRaw : RawTerm sourceScope) :
    IsAggregatorTotal (Term.equivCode (context := sourceCtx)
      outerLevel levelLe leftTypeCodeRaw rightTypeCodeRaw) := by
  intros _ _ strengthening _ _ _ rawStrengthens
  change Option.mapTwo
      (leftTypeCodeRaw.partialStrengthen? strengthening.back)
      (rightTypeCodeRaw.partialStrengthen? strengthening.back)
      RawTerm.equivCode = some _ at rawStrengthens
  obtain ⟨_, _, leftSuccess, rightSuccess, _⟩ :=
    Option.mapTwo_eq_some rawStrengthens
  unfold partialStrengthenTyped?
  split
  · next leftFails =>
      rw [leftSuccess] at leftFails
      cases leftFails
  · next _ _ =>
      split
      · next rightFails =>
          rw [rightSuccess] at rightFails
          cases rightFails
      · rfl

end Term

end LeanFX2
