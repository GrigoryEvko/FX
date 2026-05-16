import LeanFX2.Term.PreservesTerm
import LeanFX2.Term.SubjectReductionPar

/-! # LeanFX2.Term.PreservesTerm.UniversalChain

CONVTRANS-C Phase A1 — universal per-step dispatcher.

Assembles the per-ctor `lift_full_<ctor>` theorems shipped across
CONVTRANS-B into a universal Term-induction dispatcher.  Given a
typed source Term and a raw parallel step on its raw, produces a
typed target type + target Term + typed `Step.par` witness.

## Phase A1 deliverable

This file ships:

* **`StepParExists sourceTerm targetRaw`** — headline existential
  (`Prop`): a target type, target Term inhabiting it at the new raw,
  and a typed `Step.par` connecting source to target.
* **`DispatchAtom sourceTerm`** — inductive predicate enumerating
  the Term ctors that are **dispatchable** at the current kernel
  state (escape hatch (iv) — partial domain).
* **`RawStep.par.lift_full_term`** — universal driver theorem.
  Pattern-matches on `dispatch` and routes through the matching
  `lift_full_<ctor>` per arm.

**Dispatchable ctors enumerated by `DispatchAtom` (25 of 78):**

* Closed-leaf atoms (10): `Term.unit`, `Term.boolTrue`,
  `Term.boolFalse`, `Term.natZero`, `Term.interval0`,
  `Term.interval1`, `Term.listNil`, `Term.optionNone`,
  `Term.var`, `Term.universeCode`.
* Type-code ctors (10): `Term.arrowCode`, `Term.piTyCode`,
  `Term.sigmaTyCode`, `Term.productCode`, `Term.sumCode`,
  `Term.listCode`, `Term.optionCode`, `Term.eitherCode`,
  `Term.idCode`, `Term.equivCode`.
* Schematic-value ctors (5): `Term.oeqRefl`, `Term.refl`,
  `Term.idStrictRefl`, `Term.equivReflId`, `Term.equivReflIdAtId`.

## Phase scope

* **Phase A1 (this file)**: ship architectural shell + 25
  dispatchable ctor arms at zero axioms.
* **Phase A1 follow-up commits**: extend `DispatchAtom` to cover
  remaining clean-dispatchable ctors.  Each new ctor adds one
  inductive case + one dispatch arm; pattern is uniform.
* **Phase A2**: re-attempt wall ctors as their full lifts land.
* **Phase B (#1734 part 2)**: iterate to `parStar`.

## Wall ctors (Phase A2)

`pair`, `appPi`, `transp`, `hcomp`, `hcompPath`, `funextRefl`,
`funextReflAtId`, `funextIntroHet`, `uaToEquiv`, `equivApply`.

## Root status

Zero-axiom. -/

namespace LeanFX2

/-- Headline existential: a target type, target Term at that type
and at `targetRaw`, and a typed `Step.par` from source to target. -/
def StepParExists
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType : Ty level scope} {sourceRaw : RawTerm scope}
    (sourceTerm : Term context sourceType sourceRaw)
    (targetRaw : RawTerm scope) : Prop :=
  ∃ (targetType : Ty level scope) (targetTerm : Term context targetType targetRaw),
    Step.par sourceTerm targetTerm

/-- Per-ctor dispatchability predicate.

`DispatchAtom sourceTerm` is inhabited when `sourceTerm` is one of
the Term ctors enumerated below.  Phase A1 ships 25 ctors covering:

* Closed-leaf atoms (10) — raw form admits only `RawStep.par.refl`
  cong; typed target collapses to source.
* Type-code ctors (10) — schematic raw payloads only, no typed
  children; lift descends through `*_inv` raw inversion.
* Schematic-value ctors (5) — raw payload + Ty/UniverseLevel
  parameters, no typed children; lift uses
  free-the-type-via-suffices to destructure source.

Phase A1 follow-up commits extend this predicate with additional
ctors as their dispatch arms land. -/
inductive DispatchAtom :
    {mode : Mode} → {level scope : Nat} → {context : Ctx mode level scope} →
    {sourceType : Ty level scope} → {sourceRaw : RawTerm scope} →
    Term context sourceType sourceRaw → Prop
  | unit {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
      DispatchAtom (Term.unit (context := context) : Term context Ty.unit
                    (RawTerm.unit : RawTerm scope))
  | boolTrue {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
      DispatchAtom (Term.boolTrue (context := context) : Term context Ty.bool
                    (RawTerm.boolTrue : RawTerm scope))
  | boolFalse {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
      DispatchAtom (Term.boolFalse (context := context) : Term context Ty.bool
                    (RawTerm.boolFalse : RawTerm scope))
  | natZero {mode : Mode} {level scope : Nat} {context : Ctx mode level scope} :
      DispatchAtom (Term.natZero (context := context) : Term context Ty.nat
                    (RawTerm.natZero : RawTerm scope))
  | interval0 {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope} :
      DispatchAtom (Term.interval0 (context := context) : Term context Ty.interval
                    (RawTerm.interval0 : RawTerm scope))
  | interval1 {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope} :
      DispatchAtom (Term.interval1 (context := context) : Term context Ty.interval
                    (RawTerm.interval1 : RawTerm scope))
  | listNil {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {elementType : Ty level scope} :
      DispatchAtom (Term.listNil (context := context)
                                 (elementType := elementType)
                    : Term context (Ty.listType elementType)
                                   (RawTerm.listNil : RawTerm scope))
  | optionNone {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      {elementType : Ty level scope} :
      DispatchAtom (Term.optionNone (context := context)
                                    (elementType := elementType)
                    : Term context (Ty.optionType elementType)
                                   (RawTerm.optionNone : RawTerm scope))
  | var {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
      (position : Fin scope) :
      DispatchAtom (Term.var (context := context) position
                    : Term context (varType context position)
                                   (RawTerm.var position))
  | universeCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (innerLevel outerLevel : UniverseLevel)
      (cumulOk : innerLevel.toNat ≤ outerLevel.toNat)
      (levelLe : outerLevel.toNat + 1 ≤ level) :
      DispatchAtom (Term.universeCode (context := context) innerLevel outerLevel
                                       cumulOk levelLe
                    : Term context (Ty.universe outerLevel levelLe)
                                   (RawTerm.universeCode innerLevel.toNat))
  | arrowCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (outerLevel : UniverseLevel)
      (levelLe : outerLevel.toNat + 1 ≤ level)
      (domainCodeRaw codomainCodeRaw : RawTerm scope) :
      DispatchAtom (Term.arrowCode (context := context) outerLevel levelLe
                                    domainCodeRaw codomainCodeRaw
                    : Term context (Ty.universe outerLevel levelLe)
                                   (RawTerm.arrowCode domainCodeRaw codomainCodeRaw))
  | piTyCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (outerLevel : UniverseLevel)
      (levelLe : outerLevel.toNat + 1 ≤ level)
      (domainCodeRaw : RawTerm scope)
      (codomainCodeRaw : RawTerm (scope + 1)) :
      DispatchAtom (Term.piTyCode (context := context) outerLevel levelLe
                                   domainCodeRaw codomainCodeRaw
                    : Term context (Ty.universe outerLevel levelLe)
                                   (RawTerm.piTyCode domainCodeRaw codomainCodeRaw))
  | sigmaTyCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (outerLevel : UniverseLevel)
      (levelLe : outerLevel.toNat + 1 ≤ level)
      (domainCodeRaw : RawTerm scope)
      (codomainCodeRaw : RawTerm (scope + 1)) :
      DispatchAtom (Term.sigmaTyCode (context := context) outerLevel levelLe
                                      domainCodeRaw codomainCodeRaw
                    : Term context (Ty.universe outerLevel levelLe)
                                   (RawTerm.sigmaTyCode domainCodeRaw codomainCodeRaw))
  | productCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (outerLevel : UniverseLevel)
      (levelLe : outerLevel.toNat + 1 ≤ level)
      (firstCodeRaw secondCodeRaw : RawTerm scope) :
      DispatchAtom (Term.productCode (context := context) outerLevel levelLe
                                      firstCodeRaw secondCodeRaw
                    : Term context (Ty.universe outerLevel levelLe)
                                   (RawTerm.productCode firstCodeRaw secondCodeRaw))
  | sumCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (outerLevel : UniverseLevel)
      (levelLe : outerLevel.toNat + 1 ≤ level)
      (leftCodeRaw rightCodeRaw : RawTerm scope) :
      DispatchAtom (Term.sumCode (context := context) outerLevel levelLe
                                  leftCodeRaw rightCodeRaw
                    : Term context (Ty.universe outerLevel levelLe)
                                   (RawTerm.sumCode leftCodeRaw rightCodeRaw))
  | listCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (outerLevel : UniverseLevel)
      (levelLe : outerLevel.toNat + 1 ≤ level)
      (elementCodeRaw : RawTerm scope) :
      DispatchAtom (Term.listCode (context := context) outerLevel levelLe
                                   elementCodeRaw
                    : Term context (Ty.universe outerLevel levelLe)
                                   (RawTerm.listCode elementCodeRaw))
  | optionCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (outerLevel : UniverseLevel)
      (levelLe : outerLevel.toNat + 1 ≤ level)
      (elementCodeRaw : RawTerm scope) :
      DispatchAtom (Term.optionCode (context := context) outerLevel levelLe
                                     elementCodeRaw
                    : Term context (Ty.universe outerLevel levelLe)
                                   (RawTerm.optionCode elementCodeRaw))
  | eitherCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (outerLevel : UniverseLevel)
      (levelLe : outerLevel.toNat + 1 ≤ level)
      (leftCodeRaw rightCodeRaw : RawTerm scope) :
      DispatchAtom (Term.eitherCode (context := context) outerLevel levelLe
                                     leftCodeRaw rightCodeRaw
                    : Term context (Ty.universe outerLevel levelLe)
                                   (RawTerm.eitherCode leftCodeRaw rightCodeRaw))
  | idCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (outerLevel : UniverseLevel)
      (levelLe : outerLevel.toNat + 1 ≤ level)
      (typeCodeRaw leftRaw rightRaw : RawTerm scope) :
      DispatchAtom (Term.idCode (context := context) outerLevel levelLe
                                 typeCodeRaw leftRaw rightRaw
                    : Term context (Ty.universe outerLevel levelLe)
                                   (RawTerm.idCode typeCodeRaw leftRaw rightRaw))
  | equivCode {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (outerLevel : UniverseLevel)
      (levelLe : outerLevel.toNat + 1 ≤ level)
      (leftTypeCodeRaw rightTypeCodeRaw : RawTerm scope) :
      DispatchAtom (Term.equivCode (context := context) outerLevel levelLe
                                    leftTypeCodeRaw rightTypeCodeRaw
                    : Term context (Ty.universe outerLevel levelLe)
                                   (RawTerm.equivCode leftTypeCodeRaw rightTypeCodeRaw))
  | oeqRefl {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (carrier : Ty level scope) (rawWitness : RawTerm scope) :
      DispatchAtom (Term.oeqRefl (context := context) carrier rawWitness
                    : Term context (Ty.oeq carrier rawWitness rawWitness)
                                   (RawTerm.oeqRefl rawWitness))
  | refl {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (carrier : Ty level scope) (rawWitness : RawTerm scope) :
      DispatchAtom (Term.refl (context := context) carrier rawWitness
                    : Term context (Ty.id carrier rawWitness rawWitness)
                                   (RawTerm.refl rawWitness))
  | idStrictRefl {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (modeIsStrict : mode = Mode.strict)
      (carrier : Ty level scope) (rawWitness : RawTerm scope) :
      DispatchAtom (Term.idStrictRefl (context := context)
                                       modeIsStrict carrier rawWitness
                    : Term context (Ty.idStrict carrier rawWitness rawWitness)
                                   (RawTerm.idStrictRefl rawWitness))
  | equivReflId {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (carrier : Ty level scope) :
      DispatchAtom (Term.equivReflId (context := context) carrier
                    : Term context (Ty.equiv carrier carrier)
                                   (RawTerm.equivIntro
                                     (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
                                     (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))))
  | equivReflIdAtId {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      (innerLevel : UniverseLevel)
      (innerLevelLt : innerLevel.toNat + 1 ≤ level)
      (carrier : Ty level scope) (carrierRaw : RawTerm scope) :
      DispatchAtom (Term.equivReflIdAtId (context := context)
                                          innerLevel innerLevelLt
                                          carrier carrierRaw
                    : Term context
                        (Ty.id (Ty.universe innerLevel innerLevelLt)
                               carrierRaw carrierRaw)
                        (RawTerm.equivIntro
                          (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))
                          (RawTerm.lam (RawTerm.var ⟨0, Nat.zero_lt_succ scope⟩))))
  /-- Phase A1 follow-up: closed-type single-child compound ctor.

  `intervalOpp` takes one typed child at the closed type `Ty.interval`.
  The dispatch arm calls `lift_full_intervalOpp` with a callback
  recursively built from the inner `DispatchAtom` witness's IH —
  bridged from two-Ty `StepParExists` to fixed-Ty `Term ctx Ty.interval`
  via `Step.par.preserves_isClosedTy IsClosedTy.interval`. -/
  | intervalOpp {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {innerRaw : RawTerm scope}
      (innerValue : Term context Ty.interval innerRaw)
      (innerDispatch : DispatchAtom innerValue) :
      DispatchAtom (Term.intervalOpp (context := context) innerValue
                    : Term context Ty.interval
                                   (RawTerm.intervalOpp innerRaw))
  | intervalJoin {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {leftRaw rightRaw : RawTerm scope}
      (leftValue : Term context Ty.interval leftRaw)
      (rightValue : Term context Ty.interval rightRaw)
      (leftDispatch : DispatchAtom leftValue)
      (rightDispatch : DispatchAtom rightValue) :
      DispatchAtom (Term.intervalJoin (context := context) leftValue rightValue
                    : Term context Ty.interval
                                   (RawTerm.intervalJoin leftRaw rightRaw))
  | intervalMeet {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {leftRaw rightRaw : RawTerm scope}
      (leftValue : Term context Ty.interval leftRaw)
      (rightValue : Term context Ty.interval rightRaw)
      (leftDispatch : DispatchAtom leftValue)
      (rightDispatch : DispatchAtom rightValue) :
      DispatchAtom (Term.intervalMeet (context := context) leftValue rightValue
                    : Term context Ty.interval
                                   (RawTerm.intervalMeet leftRaw rightRaw))
  | natSucc {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {predRaw : RawTerm scope}
      (predecessor : Term context Ty.nat predRaw)
      (predDispatch : DispatchAtom predecessor) :
      DispatchAtom (Term.natSucc (context := context) predecessor
                    : Term context Ty.nat
                                   (RawTerm.natSucc predRaw))
  /-- Parametric closed-type ctor.  Requires `IsClosedTy elementType` so
  the SR bridge for both head (at `elementType`) and tail (at
  `Ty.listType elementType` via `IsClosedTy.listType`) discharges. -/
  | listCons {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {elementType : Ty level scope}
      (elementClosed : IsClosedTy elementType)
      {headRaw tailRaw : RawTerm scope}
      (headTerm : Term context elementType headRaw)
      (tailTerm : Term context (Ty.listType elementType) tailRaw)
      (headDispatch : DispatchAtom headTerm)
      (tailDispatch : DispatchAtom tailTerm) :
      DispatchAtom (Term.listCons (context := context) headTerm tailTerm
                    : Term context (Ty.listType elementType)
                                   (RawTerm.listCons headRaw tailRaw))
  /-- Parametric closed-type option ctor. -/
  | optionSome {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {elementType : Ty level scope}
      (elementClosed : IsClosedTy elementType)
      {valueRaw : RawTerm scope}
      (valueTerm : Term context elementType valueRaw)
      (valueDispatch : DispatchAtom valueTerm) :
      DispatchAtom (Term.optionSome (context := context) valueTerm
                    : Term context (Ty.optionType elementType)
                                   (RawTerm.optionSome valueRaw))
  /-- Parametric closed-type either-left ctor. -/
  | eitherInl {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {leftType rightType : Ty level scope}
      (leftClosed : IsClosedTy leftType)
      {valueRaw : RawTerm scope}
      (valueTerm : Term context leftType valueRaw)
      (valueDispatch : DispatchAtom valueTerm) :
      DispatchAtom (Term.eitherInl (context := context)
                                    (rightType := rightType) valueTerm
                    : Term context (Ty.eitherType leftType rightType)
                                   (RawTerm.eitherInl valueRaw))
  /-- Parametric closed-type either-right ctor. -/
  | eitherInr {mode : Mode} {level scope : Nat}
      {context : Ctx mode level scope}
      {leftType rightType : Ty level scope}
      (rightClosed : IsClosedTy rightType)
      {valueRaw : RawTerm scope}
      (valueTerm : Term context rightType valueRaw)
      (valueDispatch : DispatchAtom valueTerm) :
      DispatchAtom (Term.eitherInr (context := context)
                                    (leftType := leftType) valueTerm
                    : Term context (Ty.eitherType leftType rightType)
                                   (RawTerm.eitherInr valueRaw))

/-- **CONVTRANS-C Phase A1 headline** — universal per-step dispatcher
restricted to dispatchable ctors.

For each ctor enumerated by `DispatchAtom`, calls the matching
`lift_full_<ctor>` to produce the typed existential witness.

Phase A1 follow-up commits extend `DispatchAtom` and add new dispatch
arms here as additional ctors become dispatchable. -/
theorem RawStep.par.lift_full_term
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType : Ty level scope} {sourceRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    (dispatch : DispatchAtom sourceTerm)
    {targetRaw : RawTerm scope}
    (rawStep : RawStep.par sourceRaw targetRaw) :
    StepParExists sourceTerm targetRaw := by
  induction dispatch generalizing targetRaw with
  | unit =>
    exact RawStep.par.lift_full_unit Term.unit rawStep
  | boolTrue =>
    exact RawStep.par.lift_full_boolTrue Term.boolTrue rawStep
  | boolFalse =>
    exact RawStep.par.lift_full_boolFalse Term.boolFalse rawStep
  | natZero =>
    exact RawStep.par.lift_full_natZero Term.natZero rawStep
  | interval0 =>
    exact RawStep.par.lift_full_interval0 Term.interval0 rawStep
  | interval1 =>
    exact RawStep.par.lift_full_interval1 Term.interval1 rawStep
  | listNil =>
    exact RawStep.par.lift_full_listNil Term.listNil rawStep
  | optionNone =>
    exact RawStep.par.lift_full_optionNone Term.optionNone rawStep
  | var position =>
    exact RawStep.par.lift_full_var (Term.var position) rawStep
  | universeCode innerLevel outerLevel cumulOk levelLe =>
    exact RawStep.par.lift_full_universeCode
            (Term.universeCode innerLevel outerLevel cumulOk levelLe)
            rawStep
  | arrowCode outerLevel levelLe domainCodeRaw codomainCodeRaw =>
    exact RawStep.par.lift_full_arrowCode outerLevel levelLe
            domainCodeRaw codomainCodeRaw
            (Term.arrowCode outerLevel levelLe domainCodeRaw codomainCodeRaw)
            rawStep
  | piTyCode outerLevel levelLe domainCodeRaw codomainCodeRaw =>
    exact RawStep.par.lift_full_piTyCode outerLevel levelLe
            domainCodeRaw codomainCodeRaw
            (Term.piTyCode outerLevel levelLe domainCodeRaw codomainCodeRaw)
            rawStep
  | sigmaTyCode outerLevel levelLe domainCodeRaw codomainCodeRaw =>
    exact RawStep.par.lift_full_sigmaTyCode outerLevel levelLe
            domainCodeRaw codomainCodeRaw
            (Term.sigmaTyCode outerLevel levelLe domainCodeRaw codomainCodeRaw)
            rawStep
  | productCode outerLevel levelLe firstCodeRaw secondCodeRaw =>
    exact RawStep.par.lift_full_productCode outerLevel levelLe
            firstCodeRaw secondCodeRaw
            (Term.productCode outerLevel levelLe firstCodeRaw secondCodeRaw)
            rawStep
  | sumCode outerLevel levelLe leftCodeRaw rightCodeRaw =>
    exact RawStep.par.lift_full_sumCode outerLevel levelLe
            leftCodeRaw rightCodeRaw
            (Term.sumCode outerLevel levelLe leftCodeRaw rightCodeRaw)
            rawStep
  | listCode outerLevel levelLe elementCodeRaw =>
    exact RawStep.par.lift_full_listCode outerLevel levelLe
            elementCodeRaw
            (Term.listCode outerLevel levelLe elementCodeRaw)
            rawStep
  | optionCode outerLevel levelLe elementCodeRaw =>
    exact RawStep.par.lift_full_optionCode outerLevel levelLe
            elementCodeRaw
            (Term.optionCode outerLevel levelLe elementCodeRaw)
            rawStep
  | eitherCode outerLevel levelLe leftCodeRaw rightCodeRaw =>
    exact RawStep.par.lift_full_eitherCode outerLevel levelLe
            leftCodeRaw rightCodeRaw
            (Term.eitherCode outerLevel levelLe leftCodeRaw rightCodeRaw)
            rawStep
  | idCode outerLevel levelLe typeCodeRaw leftRaw rightRaw =>
    exact RawStep.par.lift_full_idCode outerLevel levelLe
            typeCodeRaw leftRaw rightRaw
            (Term.idCode outerLevel levelLe typeCodeRaw leftRaw rightRaw)
            rawStep
  | equivCode outerLevel levelLe leftTypeCodeRaw rightTypeCodeRaw =>
    exact RawStep.par.lift_full_equivCode outerLevel levelLe
            leftTypeCodeRaw rightTypeCodeRaw
            (Term.equivCode outerLevel levelLe leftTypeCodeRaw rightTypeCodeRaw)
            rawStep
  | oeqRefl carrier rawWitness =>
    exact RawStep.par.lift_full_oeqRefl carrier rawWitness
            (Term.oeqRefl carrier rawWitness) rawStep
  | refl carrier rawWitness =>
    exact RawStep.par.lift_full_refl carrier rawWitness
            (Term.refl carrier rawWitness) rawStep
  | idStrictRefl modeIsStrict carrier rawWitness =>
    exact RawStep.par.lift_full_idStrictRefl modeIsStrict carrier rawWitness
            (Term.idStrictRefl modeIsStrict carrier rawWitness) rawStep
  | equivReflId carrier =>
    exact RawStep.par.lift_full_equivReflId carrier
            (Term.equivReflId carrier) rawStep
  | equivReflIdAtId innerLevel innerLevelLt carrier carrierRaw =>
    exact RawStep.par.lift_full_equivReflIdAtId innerLevel innerLevelLt
            carrier carrierRaw
            (Term.equivReflIdAtId innerLevel innerLevelLt carrier carrierRaw)
            rawStep
  | intervalOpp innerValue _innerDispatch ihInner =>
    -- ihInner : ∀ {targetRaw}, RawStep.par innerValue.toRaw targetRaw →
    --            StepParExists innerValue targetRaw
    -- lift_full_intervalOpp wants a fixed-Ty callback
    --   ∀ {tgt}, RawStep.par innerRaw tgt → ∃ innerTarget : Term ctx Ty.interval tgt,
    --      Step.par innerValue innerTarget
    -- Bridge two-Ty → fixed-Ty via Step.par.preserves_isClosedTy IsClosedTy.interval.
    refine RawStep.par.lift_full_intervalOpp innerValue ?_ rawStep
    intro _ innerRawStep
    obtain ⟨innerTargetType, innerTarget, innerStep⟩ := ihInner innerRawStep
    have intervalEq : innerTargetType = Ty.interval :=
      Step.par.preserves_isClosedTy IsClosedTy.interval innerStep rfl
    subst intervalEq
    exact ⟨innerTarget, innerStep⟩
  | intervalJoin leftValue rightValue _ _ ihLeft ihRight =>
    refine RawStep.par.lift_full_intervalJoin leftValue rightValue ?_ ?_ rawStep
    · intro _ leftRawStep
      obtain ⟨leftTargetType, leftTarget, leftStep⟩ := ihLeft leftRawStep
      have intervalEq : leftTargetType = Ty.interval :=
        Step.par.preserves_isClosedTy IsClosedTy.interval leftStep rfl
      subst intervalEq
      exact ⟨leftTarget, leftStep⟩
    · intro _ rightRawStep
      obtain ⟨rightTargetType, rightTarget, rightStep⟩ := ihRight rightRawStep
      have intervalEq : rightTargetType = Ty.interval :=
        Step.par.preserves_isClosedTy IsClosedTy.interval rightStep rfl
      subst intervalEq
      exact ⟨rightTarget, rightStep⟩
  | intervalMeet leftValue rightValue _ _ ihLeft ihRight =>
    refine RawStep.par.lift_full_intervalMeet leftValue rightValue ?_ ?_ rawStep
    · intro _ leftRawStep
      obtain ⟨leftTargetType, leftTarget, leftStep⟩ := ihLeft leftRawStep
      have intervalEq : leftTargetType = Ty.interval :=
        Step.par.preserves_isClosedTy IsClosedTy.interval leftStep rfl
      subst intervalEq
      exact ⟨leftTarget, leftStep⟩
    · intro _ rightRawStep
      obtain ⟨rightTargetType, rightTarget, rightStep⟩ := ihRight rightRawStep
      have intervalEq : rightTargetType = Ty.interval :=
        Step.par.preserves_isClosedTy IsClosedTy.interval rightStep rfl
      subst intervalEq
      exact ⟨rightTarget, rightStep⟩
  | natSucc predecessor _predDispatch ihPred =>
    refine RawStep.par.lift_full_natSucc predecessor ?_ rawStep
    intro _ predRawStep
    obtain ⟨predTargetType, predTarget, predStep⟩ := ihPred predRawStep
    have natEq : predTargetType = Ty.nat :=
      Step.par.preserves_isClosedTy IsClosedTy.nat predStep rfl
    subst natEq
    exact ⟨predTarget, predStep⟩
  | listCons elementClosed headTerm tailTerm _ _ ihHead ihTail =>
    refine RawStep.par.lift_full_listCons headTerm tailTerm ?_ ?_ rawStep
    · intro _ headRawStep
      obtain ⟨headTargetType, headTarget, headStep⟩ := ihHead headRawStep
      have elemEq : headTargetType = _ :=
        Step.par.preserves_isClosedTy elementClosed headStep rfl
      subst elemEq
      exact ⟨headTarget, headStep⟩
    · intro _ tailRawStep
      obtain ⟨tailTargetType, tailTarget, tailStep⟩ := ihTail tailRawStep
      have listEq : tailTargetType = _ :=
        Step.par.preserves_isClosedTy (IsClosedTy.listType elementClosed)
                                      tailStep rfl
      subst listEq
      exact ⟨tailTarget, tailStep⟩
  | optionSome elementClosed valueTerm _ ihValue =>
    refine RawStep.par.lift_full_optionSome valueTerm ?_ rawStep
    intro _ valueRawStep
    obtain ⟨valueTargetType, valueTarget, valueStep⟩ := ihValue valueRawStep
    have elemEq : valueTargetType = _ :=
      Step.par.preserves_isClosedTy elementClosed valueStep rfl
    subst elemEq
    exact ⟨valueTarget, valueStep⟩
  | eitherInl leftClosed valueTerm _ ihValue =>
    refine RawStep.par.lift_full_eitherInl valueTerm ?_ rawStep
    intro _ valueRawStep
    obtain ⟨valueTargetType, valueTarget, valueStep⟩ := ihValue valueRawStep
    have leftEq : valueTargetType = _ :=
      Step.par.preserves_isClosedTy leftClosed valueStep rfl
    subst leftEq
    exact ⟨valueTarget, valueStep⟩
  | eitherInr rightClosed valueTerm _ ihValue =>
    refine RawStep.par.lift_full_eitherInr valueTerm ?_ rawStep
    intro _ valueRawStep
    obtain ⟨valueTargetType, valueTarget, valueStep⟩ := ihValue valueRawStep
    have rightEq : valueTargetType = _ :=
      Step.par.preserves_isClosedTy rightClosed valueStep rfl
    subst rightEq
    exact ⟨valueTarget, valueStep⟩

end LeanFX2
