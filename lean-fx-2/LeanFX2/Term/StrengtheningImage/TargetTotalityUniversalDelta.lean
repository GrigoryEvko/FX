import LeanFX2.Term.StrengtheningImage.AggregatorTotalCore
import LeanFX2.Term.StrengtheningImage.TargetImageTotality
import LeanFX2.Foundation.TyStrengthenInversion
import LeanFX2.Foundation.RawPartialRename.IsSomeInversion

/-! # Term/StrengtheningImage/TargetTotalityUniversalDelta

Atomic-constructor `IsAggregatorTotal` arms for the target-direction
typed image-totality cascade (Block B critical-path residual #2022).

## What this file ships

`IsAggregatorTotal sourceTerm` (defined in `AggregatorTotalCore.lean`)
quantifies over arbitrary context strengthenings and says: whenever the
*source* type and *source* raw indices strengthen through the
strengthening's `back` renaming, the typed dispatcher
`partialStrengthenTyped?` succeeds.

For the **atomic** constructors — those whose per-arm wrapper in
`TargetImageTotality.lean` takes NO recursive `∀ subValue, isSome`
inductive hypothesis — `IsAggregatorTotal` is provable directly: the
proof introduces the strengthening together with the `IsAggregatorTotal`
type-side / raw-side premises, derives whatever scalar `.isSome`
side-conditions the wrapper demands from those premises (via the
`Foundation/TyStrengthenInversion.lean` lemmas for the type side, or the
definitional reduction of `RawTerm.partialStrengthen?` for the variable
arm), and discharges the goal with the shipped wrapper.

Constructors covered here (22 atomic arms):

* `unit`, `boolTrue`, `boolFalse`, `natZero`, `interval0`, `interval1`,
  `universeCode` — closed atomics whose wrapper needs no strengthening
  side-condition at all.
* `var` — needs `(back position).isSome = true`, which the
  `IsAggregatorTotal` raw premise delivers because the source raw is
  literally `RawTerm.var position` and the dispatcher's var arm
  matches on `back position`.
* `listNil`, `optionNone` — parametric atomics whose wrapper needs the
  element type's strengthening, recovered from the source type's
  strengthening premise via `Ty.partialStrengthen?_listType_isSome` /
  `Ty.partialStrengthen?_optionType_isSome`.
* `refl`, `oeqRefl`, `idStrictRefl` — identity introducers needing a
  carrier-type strengthening (from the source-type premise via the
  `Ty.partialStrengthen?_{id,oeq,idStrict}_isSome` inversions) and a
  witness-raw strengthening (from the source-raw premise via the
  `RawTerm.partialRename?_{refl,oeqRefl,idStrictRefl}_isSome` inversions).
* `arrowCode`, `productCode`, `sumCode`, `eitherCode`, `listCode`,
  `optionCode`, `piTyCode`, `sigmaTyCode`, `equivCode`, `idCode` — the
  CUMUL-2.4 type codes.  Their source type is `Ty.universe outerLevel`
  (no recoverable sub-type), but every code payload is a syntactic part
  of the source raw, so the wrapper's per-payload strengthening side is
  recovered from the source-raw premise via the matching
  `RawTerm.partialRename?_<ctor>_isSome` inversion.  The binder-shape
  codes (`piTyCode`, `sigmaTyCode`) recover their codomain at
  `strengthening.back.lift`.

## What this file does NOT ship (honest gap)

The *compound* constructors (`app`, `appPi`, `pair`, `listCons`, the six
eliminators, and ~16 others) carry sub-term types that do NOT appear in
the source type index.  Their wrappers therefore demand a
`∀ subValue : Term sourceCtx subType subRaw, ...isSome` premise that a
plain structural `induction` IH cannot supply (the IH only ranges over
the syntactic subterm, not over every same-(type,raw) value), AND a
sub-type strengthening side-condition that the `IsAggregatorTotal` source
premise cannot recover (the sub-type is not a syntactic part of the
source type — see `ImageUnweaken.lean:496-499`, which records that 25 of
78 constructors have non-recoverable sub-type strengthening witnesses).

Consequently a universal `∀ sourceTerm, IsAggregatorTotal sourceTerm`
under THIS predicate is architecturally impossible — the renaming-image
API (`strengthenTyped?_rename_isSome`, already shipped) is the universal
surface that downstream Block B work consumes.  This file therefore
ships the atomic arms only, each as a complete zero-axiom theorem.
-/

namespace LeanFX2

namespace Term

/-- Bridge: a `partialStrengthen?` (equivalently `partialRename?`)
success equation upgrades to an `isSome` fact.  The `IsAggregatorTotal`
premises arrive as `... = some _`; the per-component inversion lemmas
consume `....isSome = true`. -/
private theorem isSomeOfEqSomeRaw {targetScope : Nat}
    {result : Option (RawTerm targetScope)} {witness : RawTerm targetScope}
    (eqWitness : result = some witness) : result.isSome = true := by
  rw [eqWitness]; rfl

/-- Type-side companion of `isSomeOfEqSomeRaw`. -/
private theorem isSomeOfEqSomeTy {level targetScope : Nat}
    {result : Option (Ty level targetScope)} {witness : Ty level targetScope}
    (eqWitness : result = some witness) : result.isSome = true := by
  rw [eqWitness]; rfl

/-! ## Closed atomics with no wrapper precondition

`unit`, `boolTrue`, `boolFalse`, `natZero`, `interval0`, `interval1`.
Each wrapper proves totality by HEq inversion to the unique
canonical-shape representative; it needs no strengthening
side-condition.  The `IsAggregatorTotal` premises are therefore
discarded and the wrapper applied directly to the given term. -/

/-- `Term.unit` is aggregator-total. -/
theorem isAggregatorTotal_unit {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope} :
    IsAggregatorTotal (Term.unit (context := sourceCtx) (level := level)) := by
  intro targetScope targetCtx strengthening _ _ _ _
  exact partialStrengthenTyped?_isSome_target_unit strengthening
    (Term.unit (context := sourceCtx) (level := level))

/-- `Term.boolTrue` is aggregator-total. -/
theorem isAggregatorTotal_boolTrue {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope} :
    IsAggregatorTotal
      (Term.boolTrue (context := sourceCtx) (level := level)) := by
  intro targetScope targetCtx strengthening _ _ _ _
  exact partialStrengthenTyped?_isSome_target_boolTrue strengthening
    (Term.boolTrue (context := sourceCtx) (level := level))

/-- `Term.boolFalse` is aggregator-total. -/
theorem isAggregatorTotal_boolFalse {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope} :
    IsAggregatorTotal
      (Term.boolFalse (context := sourceCtx) (level := level)) := by
  intro targetScope targetCtx strengthening _ _ _ _
  exact partialStrengthenTyped?_isSome_target_boolFalse strengthening
    (Term.boolFalse (context := sourceCtx) (level := level))

/-- `Term.natZero` is aggregator-total. -/
theorem isAggregatorTotal_natZero {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope} :
    IsAggregatorTotal
      (Term.natZero (context := sourceCtx) (level := level)) := by
  intro targetScope targetCtx strengthening _ _ _ _
  exact partialStrengthenTyped?_isSome_target_natZero strengthening
    (Term.natZero (context := sourceCtx) (level := level))

/-- `Term.interval0` is aggregator-total. -/
theorem isAggregatorTotal_interval0 {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope} :
    IsAggregatorTotal
      (Term.interval0 (context := sourceCtx) (level := level)) := by
  intro targetScope targetCtx strengthening _ _ _ _
  exact partialStrengthenTyped?_isSome_target_interval0 strengthening
    (Term.interval0 (context := sourceCtx) (level := level))

/-- `Term.interval1` is aggregator-total. -/
theorem isAggregatorTotal_interval1 {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope} :
    IsAggregatorTotal
      (Term.interval1 (context := sourceCtx) (level := level)) := by
  intro targetScope targetCtx strengthening _ _ _ _
  exact partialStrengthenTyped?_isSome_target_interval1 strengthening
    (Term.interval1 (context := sourceCtx) (level := level))

/-! ## Variable arm

The variable wrapper needs `(strengthening.back position).isSome = true`.
The `IsAggregatorTotal` raw premise gives
`(RawTerm.var position).partialStrengthen? strengthening.back = some _`,
and the variable arm of `RawTerm.partialStrengthen?` is
`match back position with | some t => some (RawTerm.var t) | none => none`.
A `none` value of `back position` would force the premise to read
`none = some _`, a contradiction; hence `back position` is `some _`. -/

/-- `Term.var position` is aggregator-total. -/
theorem isAggregatorTotal_var {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (position : Fin sourceScope) :
    IsAggregatorTotal (Term.var (context := sourceCtx) position) := by
  intro targetScope targetCtx strengthening _ _ _ rawStrengthens
  dsimp only [RawTerm.partialStrengthen?, RawTerm.partialRename?] at rawStrengthens
  have survives : (strengthening.back position).isSome = true := by
    match hback : strengthening.back position with
    | none => rw [hback] at rawStrengthens; cases rawStrengthens
    | some _ => rfl
  exact partialStrengthenTyped?_isSome_target_var strengthening position
    survives

/-! ## Parametric atomics: listNil, optionNone

`Term.listNil` has source type `Ty.listType elementType` and source raw
`RawTerm.listNil`; `Term.optionNone` has source type
`Ty.optionType elementType` and source raw `RawTerm.optionNone`.  Their
wrappers need `(elementType.partialStrengthen? back).isSome = true`,
recovered from the `IsAggregatorTotal` source-type premise via the
shipped `Ty` inversion lemmas. -/

/-- `Term.listNil` is aggregator-total. -/
theorem isAggregatorTotal_listNil {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {elementType : Ty level sourceScope} :
    IsAggregatorTotal
      (Term.listNil (context := sourceCtx) (elementType := elementType)) := by
  intro targetScope targetCtx strengthening _ _ typeStrengthens _
  have compositeIsSome :
      ((Ty.listType elementType).partialStrengthen? strengthening.back).isSome
        = true := by
    rw [typeStrengthens]; rfl
  have elementStrengthens :
      (elementType.partialStrengthen? strengthening.back).isSome = true :=
    Ty.partialStrengthen?_listType_isSome strengthening.back elementType
      compositeIsSome
  exact partialStrengthenTyped?_isSome_target_listNil strengthening
    elementType elementStrengthens

/-- `Term.optionNone` is aggregator-total. -/
theorem isAggregatorTotal_optionNone {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    {elementType : Ty level sourceScope} :
    IsAggregatorTotal
      (Term.optionNone (context := sourceCtx)
        (elementType := elementType)) := by
  intro targetScope targetCtx strengthening _ _ typeStrengthens _
  have compositeIsSome :
      ((Ty.optionType elementType).partialStrengthen?
          strengthening.back).isSome = true := by
    rw [typeStrengthens]; rfl
  have elementStrengthens :
      (elementType.partialStrengthen? strengthening.back).isSome = true :=
    Ty.partialStrengthen?_optionType_isSome strengthening.back elementType
      compositeIsSome
  exact partialStrengthenTyped?_isSome_target_optionNone strengthening
    elementType elementStrengthens

/-! ## Universe-code atomic

`Term.universeCode` has source type `Ty.universe outerLevel levelLe` and
source raw `RawTerm.universeCode innerLevel.toNat`.  Its wrapper proves
totality by definitional reduction (`rfl`) and needs no strengthening
side-condition. -/

/-- `Term.universeCode` is aggregator-total. -/
theorem isAggregatorTotal_universeCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (innerLevel outerLevel : UniverseLevel)
    (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
    (levelLe : outerLevel.toNat + 1 ≤ level) :
    IsAggregatorTotal
      (Term.universeCode (context := sourceCtx)
        innerLevel outerLevel cumulOk levelLe) := by
  intro targetScope targetCtx strengthening _ _ _ _
  exact partialStrengthenTyped?_isSome_target_universeCode strengthening
    innerLevel outerLevel cumulOk levelLe

/-! ## Identity introducers: refl, oeqRefl, idStrictRefl

`Term.refl carrier rawWitness` has source type `Ty.id carrier rawWitness
rawWitness` and source raw `RawTerm.refl rawWitness`.  Its wrapper needs
the carrier type's strengthening (recovered from the source-type premise
via `Ty.partialStrengthen?_id_isSome`) and the witness raw's strengthening
(recovered from the source-raw premise via
`RawTerm.partialRename?_refl_isSome`).  `oeqRefl` mirrors with `Ty.oeq` /
`RawTerm.oeqRefl`; `idStrictRefl` mirrors with `Ty.idStrict` /
`RawTerm.idStrictRefl` plus a mode-is-strict attribute. -/

/-- `Term.refl carrier rawWitness` is aggregator-total. -/
theorem isAggregatorTotal_refl {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (carrier : Ty level sourceScope) (rawWitness : RawTerm sourceScope) :
    IsAggregatorTotal
      (Term.refl (context := sourceCtx) carrier rawWitness) := by
  intro targetScope targetCtx strengthening _ _ typeStrengthens rawStrengthens
  have carrierStrengthens :
      (carrier.partialStrengthen? strengthening.back).isSome = true :=
    (Ty.partialStrengthen?_id_isSome strengthening.back carrier rawWitness
      rawWitness (isSomeOfEqSomeTy typeStrengthens)).1
  have witnessStrengthens :
      (rawWitness.partialStrengthen? strengthening.back).isSome = true :=
    RawTerm.partialRename?_refl_isSome strengthening.back rawWitness
      (isSomeOfEqSomeRaw rawStrengthens)
  exact partialStrengthenTyped?_isSome_target_refl strengthening carrier
    rawWitness carrierStrengthens witnessStrengthens

/-- `Term.oeqRefl carrier rawWitness` is aggregator-total. -/
theorem isAggregatorTotal_oeqRefl {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (carrier : Ty level sourceScope) (rawWitness : RawTerm sourceScope) :
    IsAggregatorTotal
      (Term.oeqRefl (context := sourceCtx) carrier rawWitness) := by
  intro targetScope targetCtx strengthening _ _ typeStrengthens rawStrengthens
  have carrierStrengthens :
      (carrier.partialStrengthen? strengthening.back).isSome = true :=
    (Ty.partialStrengthen?_oeq_isSome strengthening.back carrier rawWitness
      rawWitness (isSomeOfEqSomeTy typeStrengthens)).1
  have witnessStrengthens :
      (rawWitness.partialStrengthen? strengthening.back).isSome = true :=
    RawTerm.partialRename?_oeqRefl_isSome strengthening.back rawWitness
      (isSomeOfEqSomeRaw rawStrengthens)
  exact partialStrengthenTyped?_isSome_target_oeqRefl strengthening carrier
    rawWitness carrierStrengthens witnessStrengthens

/-! ## Type-code atomics (raw-side only)

The ten type-code constructors (`arrowCode`, `piTyCode`, `sigmaTyCode`,
`productCode`, `sumCode`, `listCode`, `optionCode`, `eitherCode`,
`idCode`) all share source type `Ty.universe outerLevel levelLe` (which
carries no recoverable sub-type information).  Their wrappers require
strengthening only of the *raw* code payloads, which are syntactic parts
of the source raw and so are recovered from the `IsAggregatorTotal` raw
premise via the matching `RawTerm.partialRename?_<ctor>_isSome` inversion.
The binder-shape codes (`piTyCode`, `sigmaTyCode`) recover their codomain
at `strengthening.back.lift`. -/

/-- `Term.arrowCode` is aggregator-total. -/
theorem isAggregatorTotal_arrowCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw codomainCodeRaw : RawTerm sourceScope) :
    IsAggregatorTotal
      (Term.arrowCode (context := sourceCtx)
        outerLevel levelLe domainCodeRaw codomainCodeRaw) := by
  intro targetScope targetCtx strengthening _ _ _ rawStrengthens
  obtain ⟨domainStrengthens, codomainStrengthens⟩ :=
    RawTerm.partialRename?_arrowCode_isSome strengthening.back
      domainCodeRaw codomainCodeRaw (isSomeOfEqSomeRaw rawStrengthens)
  exact partialStrengthenTyped?_isSome_target_arrowCode strengthening
    outerLevel levelLe domainCodeRaw codomainCodeRaw
    domainStrengthens codomainStrengthens

/-- `Term.productCode` is aggregator-total. -/
theorem isAggregatorTotal_productCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (firstCodeRaw secondCodeRaw : RawTerm sourceScope) :
    IsAggregatorTotal
      (Term.productCode (context := sourceCtx)
        outerLevel levelLe firstCodeRaw secondCodeRaw) := by
  intro targetScope targetCtx strengthening _ _ _ rawStrengthens
  obtain ⟨firstStrengthens, secondStrengthens⟩ :=
    RawTerm.partialRename?_productCode_isSome strengthening.back
      firstCodeRaw secondCodeRaw (isSomeOfEqSomeRaw rawStrengthens)
  exact partialStrengthenTyped?_isSome_target_productCode strengthening
    outerLevel levelLe firstCodeRaw secondCodeRaw
    firstStrengthens secondStrengthens

/-- `Term.sumCode` is aggregator-total. -/
theorem isAggregatorTotal_sumCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm sourceScope) :
    IsAggregatorTotal
      (Term.sumCode (context := sourceCtx)
        outerLevel levelLe leftCodeRaw rightCodeRaw) := by
  intro targetScope targetCtx strengthening _ _ _ rawStrengthens
  obtain ⟨leftStrengthens, rightStrengthens⟩ :=
    RawTerm.partialRename?_sumCode_isSome strengthening.back
      leftCodeRaw rightCodeRaw (isSomeOfEqSomeRaw rawStrengthens)
  exact partialStrengthenTyped?_isSome_target_sumCode strengthening
    outerLevel levelLe leftCodeRaw rightCodeRaw
    leftStrengthens rightStrengthens

/-- `Term.listCode` is aggregator-total. -/
theorem isAggregatorTotal_listCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm sourceScope) :
    IsAggregatorTotal
      (Term.listCode (context := sourceCtx)
        outerLevel levelLe elementCodeRaw) := by
  intro targetScope targetCtx strengthening _ _ _ rawStrengthens
  have elementStrengthens :
      (elementCodeRaw.partialStrengthen? strengthening.back).isSome = true :=
    RawTerm.partialRename?_listCode_isSome strengthening.back
      elementCodeRaw (isSomeOfEqSomeRaw rawStrengthens)
  exact partialStrengthenTyped?_isSome_target_listCode strengthening
    outerLevel levelLe elementCodeRaw elementStrengthens

/-- `Term.optionCode` is aggregator-total. -/
theorem isAggregatorTotal_optionCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (elementCodeRaw : RawTerm sourceScope) :
    IsAggregatorTotal
      (Term.optionCode (context := sourceCtx)
        outerLevel levelLe elementCodeRaw) := by
  intro targetScope targetCtx strengthening _ _ _ rawStrengthens
  have elementStrengthens :
      (elementCodeRaw.partialStrengthen? strengthening.back).isSome = true :=
    RawTerm.partialRename?_optionCode_isSome strengthening.back
      elementCodeRaw (isSomeOfEqSomeRaw rawStrengthens)
  exact partialStrengthenTyped?_isSome_target_optionCode strengthening
    outerLevel levelLe elementCodeRaw elementStrengthens

/-- `Term.eitherCode` is aggregator-total. -/
theorem isAggregatorTotal_eitherCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftCodeRaw rightCodeRaw : RawTerm sourceScope) :
    IsAggregatorTotal
      (Term.eitherCode (context := sourceCtx)
        outerLevel levelLe leftCodeRaw rightCodeRaw) := by
  intro targetScope targetCtx strengthening _ _ _ rawStrengthens
  obtain ⟨leftStrengthens, rightStrengthens⟩ :=
    RawTerm.partialRename?_eitherCode_isSome strengthening.back
      leftCodeRaw rightCodeRaw (isSomeOfEqSomeRaw rawStrengthens)
  exact partialStrengthenTyped?_isSome_target_eitherCode strengthening
    outerLevel levelLe leftCodeRaw rightCodeRaw
    leftStrengthens rightStrengthens

/-- `Term.piTyCode` is aggregator-total.  Codomain code lives under the
binder and strengthens at `strengthening.back.lift`. -/
theorem isAggregatorTotal_piTyCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm sourceScope)
    (codomainCodeRaw : RawTerm (sourceScope + 1)) :
    IsAggregatorTotal
      (Term.piTyCode (context := sourceCtx)
        outerLevel levelLe domainCodeRaw codomainCodeRaw) := by
  intro targetScope targetCtx strengthening _ _ _ rawStrengthens
  obtain ⟨domainStrengthens, codomainLiftedStrengthens⟩ :=
    RawTerm.partialRename?_piTyCode_isSome strengthening.back
      domainCodeRaw codomainCodeRaw (isSomeOfEqSomeRaw rawStrengthens)
  exact partialStrengthenTyped?_isSome_target_piTyCode strengthening
    outerLevel levelLe domainCodeRaw codomainCodeRaw
    domainStrengthens codomainLiftedStrengthens

/-- `Term.sigmaTyCode` is aggregator-total.  Codomain code lives under the
binder and strengthens at `strengthening.back.lift`. -/
theorem isAggregatorTotal_sigmaTyCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (domainCodeRaw : RawTerm sourceScope)
    (codomainCodeRaw : RawTerm (sourceScope + 1)) :
    IsAggregatorTotal
      (Term.sigmaTyCode (context := sourceCtx)
        outerLevel levelLe domainCodeRaw codomainCodeRaw) := by
  intro targetScope targetCtx strengthening _ _ _ rawStrengthens
  obtain ⟨domainStrengthens, codomainLiftedStrengthens⟩ :=
    RawTerm.partialRename?_sigmaTyCode_isSome strengthening.back
      domainCodeRaw codomainCodeRaw (isSomeOfEqSomeRaw rawStrengthens)
  exact partialStrengthenTyped?_isSome_target_sigmaTyCode strengthening
    outerLevel levelLe domainCodeRaw codomainCodeRaw
    domainStrengthens codomainLiftedStrengthens

/-- `Term.equivCode` is aggregator-total. -/
theorem isAggregatorTotal_equivCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (leftTypeCodeRaw rightTypeCodeRaw : RawTerm sourceScope) :
    IsAggregatorTotal
      (Term.equivCode (context := sourceCtx)
        outerLevel levelLe leftTypeCodeRaw rightTypeCodeRaw) := by
  intro targetScope targetCtx strengthening _ _ _ rawStrengthens
  obtain ⟨leftStrengthens, rightStrengthens⟩ :=
    RawTerm.partialRename?_equivCode_isSome strengthening.back
      leftTypeCodeRaw rightTypeCodeRaw (isSomeOfEqSomeRaw rawStrengthens)
  exact partialStrengthenTyped?_isSome_target_equivCode strengthening
    outerLevel levelLe leftTypeCodeRaw rightTypeCodeRaw
    leftStrengthens rightStrengthens

/-- `Term.idCode` is aggregator-total.  Ternary raw payload (type code +
both endpoints), all recovered from the source-raw premise via
`RawTerm.partialRename?_idCode_isSome`. -/
theorem isAggregatorTotal_idCode {mode : Mode} {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx mode level sourceScope}
    (outerLevel : UniverseLevel)
    (levelLe : outerLevel.toNat + 1 ≤ level)
    (typeCodeRaw leftRaw rightRaw : RawTerm sourceScope) :
    IsAggregatorTotal
      (Term.idCode (context := sourceCtx)
        outerLevel levelLe typeCodeRaw leftRaw rightRaw) := by
  intro targetScope targetCtx strengthening _ _ _ rawStrengthens
  obtain ⟨typeStrengthens, leftStrengthens, rightStrengthens⟩ :=
    RawTerm.partialRename?_idCode_isSome strengthening.back
      typeCodeRaw leftRaw rightRaw (isSomeOfEqSomeRaw rawStrengthens)
  exact partialStrengthenTyped?_isSome_target_idCode strengthening
    outerLevel levelLe typeCodeRaw leftRaw rightRaw
    typeStrengthens leftStrengthens rightStrengthens

/-! ## Strict-identity reflexivity

`Term.idStrictRefl modeIsStrict carrier rawWitness` has source type
`Ty.idStrict carrier rawWitness rawWitness` and source raw
`RawTerm.idStrictRefl rawWitness`.  The carrier strengthening is
recovered from the source-type premise via
`Ty.partialStrengthen?_idStrict_isSome`; the witness strengthening from
the source-raw premise via `RawTerm.partialRename?_idStrictRefl_isSome`.
The mode-is-strict attribute is a constructor parameter threaded
through. -/

/-- `Term.idStrictRefl` is aggregator-total. -/
theorem isAggregatorTotal_idStrictRefl {level : Nat}
    {sourceScope : Nat} {sourceCtx : Ctx Mode.strict level sourceScope}
    (modeIsStrict : Mode.strict = Mode.strict)
    (carrier : Ty level sourceScope) (rawWitness : RawTerm sourceScope) :
    IsAggregatorTotal
      (Term.idStrictRefl (context := sourceCtx)
        modeIsStrict carrier rawWitness) := by
  intro targetScope targetCtx strengthening _ _ typeStrengthens rawStrengthens
  have carrierStrengthens :
      (carrier.partialStrengthen? strengthening.back).isSome = true :=
    (Ty.partialStrengthen?_idStrict_isSome strengthening.back carrier
      rawWitness rawWitness (isSomeOfEqSomeTy typeStrengthens)).1
  have witnessStrengthens :
      (rawWitness.partialStrengthen? strengthening.back).isSome = true :=
    RawTerm.partialRename?_idStrictRefl_isSome strengthening.back rawWitness
      (isSomeOfEqSomeRaw rawStrengthens)
  exact partialStrengthenTyped?_isSome_target_idStrictRefl strengthening
    modeIsStrict carrier rawWitness carrierStrengthens witnessStrengthens

end Term

end LeanFX2
