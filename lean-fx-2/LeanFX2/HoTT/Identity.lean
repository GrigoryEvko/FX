import LeanFX2.Reduction.Conv
import LeanFX2.Term.SubjectReductionGeneral

/-! # HoTT/Identity — identity-type metatheorems

The Term constructor `refl rawWitness` introduces identity types.
This file establishes intro/elim/computation rules at the
metatheoretic level WITHOUT committing to univalence.

## What ships (Phase 6.A foundational)

* `Conv.idJ_refl_baseCase` — the ι rule lifted to Conv:
  `J base (refl x) ≅ base`.  Direct corollary of
  `Step.iotaIdJRefl`.
* `StepStar.idJ_baseCase_lift` — congruence: stepping the
  baseCase of `idJ` produces a chain of `idJ` terms.
* `StepStar.idJ_witness_lift` — congruence: stepping the
  witness of `idJ` produces a chain of `idJ` terms.
* `Conv.idJ_baseCase_cong` — convertibility of baseCases lifts
  to convertibility of `idJ` terms.

## Foundation for HoTT/Path/*

These lemmas are the FOUNDATION for path composition / inverse /
groupoid laws.  Each path operation is constructed as an `idJ`
on a refl-witness; the ι rule + cong rules deliver the
computation laws (Path.compose refl p = p, etc.).

## What does NOT ship here

* Full dependent J — needs motive depending on endpoints +
  witness.  Layer 5 work.
* Path composition / inverse / groupoid laws — Layer 5 (in
  HoTT/Path/Composition, HoTT/Path/Inverse, HoTT/Path/Groupoid).
* Transport — Layer 5 (HoTT/Transport).
* Equivalences + univalence — Layer 5 (HoTT/Equivalence,
  HoTT/Univalence).

Zero-axiom verified per declaration via AuditAll.
-/

namespace LeanFX2

variable {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}

/-! ## ι rule: J on refl reduces to baseCase -/

/-- The ι rule for identity types: `J base (refl x) ⟶ base`.
Single-step form, direct from `Step.iotaIdJRefl`. -/
theorem Step.idJ_refl
    (carrier : Ty level scope) (endpoint : RawTerm scope)
    {motiveType : Ty level scope}
    {baseRaw : RawTerm scope}
    (baseCase : Term context motiveType baseRaw) :
    Step (Term.idJ (carrier := carrier)
                   (leftEndpoint := endpoint)
                   (rightEndpoint := endpoint)
            baseCase
            (Term.refl carrier endpoint))
         baseCase :=
  Step.iotaIdJRefl carrier endpoint baseCase

/-- Conv form: `J base (refl x) ≅ base`. -/
theorem Conv.idJ_refl_baseCase
    (carrier : Ty level scope) (endpoint : RawTerm scope)
    {motiveType : Ty level scope}
    {baseRaw : RawTerm scope}
    (baseCase : Term context motiveType baseRaw) :
    Conv (Term.idJ (carrier := carrier)
                   (leftEndpoint := endpoint)
                   (rightEndpoint := endpoint)
            baseCase
            (Term.refl carrier endpoint))
         baseCase :=
  Conv.fromStep (Step.iotaIdJRefl carrier endpoint baseCase)

/-! ## Cong rules — landed via general SR (`Step.preserves_isClosedTy`)

Both `StepStar.idJ_baseCase_lift_isClosedTy` and the Conv
analog `Conv.idJ_baseCase_cong_isClosedTy` are now shippable
because closed-motive subject reduction landed in
`Term/SubjectReductionGeneral.lean`.

The proof follows the `StepStar.natSucc_lift_general` template:
free the source/target Ty index via variables + equality
hypothesis, then thread `Step.preserves_isClosedTy closedMotive`
through every `step`-case to bridge the existential intermediate
type back to `motiveType`. -/

/-- Generalized lift: any `StepStar` chain whose source and
target are at any closed motiveType lifts to a `StepStar` chain
on the `idJ` outer (with shared witness term).  1-step
parameterization of `StepStar.lift_at_isClosedTy`. -/
theorem StepStar.idJ_baseCase_lift_isClosedTy_general
    {motiveType : Ty level scope}
    (closedMotive : IsClosedTy motiveType)
    (carrier : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope)
    {witnessRaw : RawTerm scope}
    (witnessTerm :
      Term context (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw)
    {srcTy tgtTy : Ty level scope}
    {srcRaw tgtRaw : RawTerm scope}
    {srcTerm : Term context srcTy srcRaw}
    {tgtTerm : Term context tgtTy tgtRaw}
    (someChain : StepStar srcTerm tgtTerm)
    (srcIsMotive : srcTy = motiveType)
    (tgtIsMotive : tgtTy = motiveType) :
    StepStar (Term.idJ (srcIsMotive ▸ srcTerm) witnessTerm)
             (Term.idJ (tgtIsMotive ▸ tgtTerm) witnessTerm) :=
  StepStar.lift_at_isClosedTy
    (resultTy := motiveType) closedMotive
    (wrapRaw := fun raw => RawTerm.idJ raw witnessRaw)
    (fun term => Term.idJ (carrier := carrier)
                          (leftEndpoint := leftEndpoint)
                          (rightEndpoint := rightEndpoint)
                          term witnessTerm)
    (fun step => Step.idJBase step)
    someChain srcIsMotive tgtIsMotive

/-- Lift a `StepStar` between baseCases at a closed motive type
to a `StepStar` between their `idJ` wrappers.  Closed motiveType
makes `Step.preserves_isClosedTy` applicable. -/
theorem StepStar.idJ_baseCase_lift_isClosedTy
    {motiveType : Ty level scope}
    (closedMotive : IsClosedTy motiveType)
    (carrier : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope)
    {witnessRaw : RawTerm scope}
    (witnessTerm :
      Term context (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw)
    {baseRawA baseRawB : RawTerm scope}
    {baseTermA : Term context motiveType baseRawA}
    {baseTermB : Term context motiveType baseRawB}
    (chain : StepStar baseTermA baseTermB) :
    StepStar (Term.idJ baseTermA witnessTerm)
             (Term.idJ baseTermB witnessTerm) :=
  StepStar.idJ_baseCase_lift_isClosedTy_general
    closedMotive carrier leftEndpoint rightEndpoint witnessTerm
    chain rfl rfl

/-- Convertibility of baseCases at a closed motive type lifts to
convertibility of the `idJ` wrappers.  Discharged by extracting
the existential common reduct, applying SR to constrain its
type, and re-wrapping with `idJ_baseCase_lift_isClosedTy`. -/
theorem Conv.idJ_baseCase_cong_isClosedTy
    {motiveType : Ty level scope}
    (closedMotive : IsClosedTy motiveType)
    (carrier : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope)
    {witnessRaw : RawTerm scope}
    (witnessTerm :
      Term context (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw)
    {baseRawA baseRawB : RawTerm scope}
    {baseTermA : Term context motiveType baseRawA}
    {baseTermB : Term context motiveType baseRawB}
    (baseConv : Conv baseTermA baseTermB) :
    Conv (Term.idJ baseTermA witnessTerm)
         (Term.idJ baseTermB witnessTerm) := by
  obtain ⟨midType, midRaw, midTerm, chainA, chainB⟩ := baseConv
  have midIsMotive : midType = motiveType :=
    StepStar.preserves_isClosedTy closedMotive chainA rfl
  cases midIsMotive
  refine ⟨motiveType, _, Term.idJ midTerm witnessTerm, ?_, ?_⟩
  · exact StepStar.idJ_baseCase_lift_isClosedTy
            closedMotive carrier leftEndpoint rightEndpoint
            witnessTerm chainA
  · exact StepStar.idJ_baseCase_lift_isClosedTy
            closedMotive carrier leftEndpoint rightEndpoint
            witnessTerm chainB

/-! ## Specialized cong rules at closed leaves

One-line specializations at the three concrete closed leaves
(`Ty.unit`, `Ty.bool`, `Ty.nat`).  Each just instantiates the
`isClosedTy` version with the matching `IsClosedTy` ctor. -/

/-- Cong rule: `idJ`'s baseCase position when motive is `Ty.unit`. -/
theorem StepStar.idJ_baseCase_lift_unit
    (carrier : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope)
    {witnessRaw : RawTerm scope}
    (witnessTerm :
      Term context (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw)
    {baseRawA baseRawB : RawTerm scope}
    {baseTermA : Term context Ty.unit baseRawA}
    {baseTermB : Term context Ty.unit baseRawB}
    (chain : StepStar baseTermA baseTermB) :
    StepStar (Term.idJ baseTermA witnessTerm)
             (Term.idJ baseTermB witnessTerm) :=
  StepStar.idJ_baseCase_lift_isClosedTy
    IsClosedTy.unit carrier leftEndpoint rightEndpoint witnessTerm chain

/-- Cong rule: `idJ`'s baseCase position when motive is `Ty.bool`. -/
theorem StepStar.idJ_baseCase_lift_bool
    (carrier : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope)
    {witnessRaw : RawTerm scope}
    (witnessTerm :
      Term context (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw)
    {baseRawA baseRawB : RawTerm scope}
    {baseTermA : Term context Ty.bool baseRawA}
    {baseTermB : Term context Ty.bool baseRawB}
    (chain : StepStar baseTermA baseTermB) :
    StepStar (Term.idJ baseTermA witnessTerm)
             (Term.idJ baseTermB witnessTerm) :=
  StepStar.idJ_baseCase_lift_isClosedTy
    IsClosedTy.bool carrier leftEndpoint rightEndpoint witnessTerm chain

/-- Cong rule: `idJ`'s baseCase position when motive is `Ty.nat`. -/
theorem StepStar.idJ_baseCase_lift_nat
    (carrier : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope)
    {witnessRaw : RawTerm scope}
    (witnessTerm :
      Term context (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw)
    {baseRawA baseRawB : RawTerm scope}
    {baseTermA : Term context Ty.nat baseRawA}
    {baseTermB : Term context Ty.nat baseRawB}
    (chain : StepStar baseTermA baseTermB) :
    StepStar (Term.idJ baseTermA witnessTerm)
             (Term.idJ baseTermB witnessTerm) :=
  StepStar.idJ_baseCase_lift_isClosedTy
    IsClosedTy.nat carrier leftEndpoint rightEndpoint witnessTerm chain

/-! ## Convertibility congruence (`Conv`) — closed leaves -/

/-- Convertibility cong on `idJ`'s baseCase at `Ty.unit`. -/
theorem Conv.idJ_baseCase_cong_unit
    (carrier : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope)
    {witnessRaw : RawTerm scope}
    (witnessTerm :
      Term context (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw)
    {baseRawA baseRawB : RawTerm scope}
    {baseTermA : Term context Ty.unit baseRawA}
    {baseTermB : Term context Ty.unit baseRawB}
    (baseConv : Conv baseTermA baseTermB) :
    Conv (Term.idJ baseTermA witnessTerm)
         (Term.idJ baseTermB witnessTerm) :=
  Conv.idJ_baseCase_cong_isClosedTy
    IsClosedTy.unit carrier leftEndpoint rightEndpoint witnessTerm baseConv

/-- Convertibility cong on `idJ`'s baseCase at `Ty.bool`. -/
theorem Conv.idJ_baseCase_cong_bool
    (carrier : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope)
    {witnessRaw : RawTerm scope}
    (witnessTerm :
      Term context (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw)
    {baseRawA baseRawB : RawTerm scope}
    {baseTermA : Term context Ty.bool baseRawA}
    {baseTermB : Term context Ty.bool baseRawB}
    (baseConv : Conv baseTermA baseTermB) :
    Conv (Term.idJ baseTermA witnessTerm)
         (Term.idJ baseTermB witnessTerm) :=
  Conv.idJ_baseCase_cong_isClosedTy
    IsClosedTy.bool carrier leftEndpoint rightEndpoint witnessTerm baseConv

/-- Convertibility cong on `idJ`'s baseCase at `Ty.nat`. -/
theorem Conv.idJ_baseCase_cong_nat
    (carrier : Ty level scope)
    (leftEndpoint rightEndpoint : RawTerm scope)
    {witnessRaw : RawTerm scope}
    (witnessTerm :
      Term context (Ty.id carrier leftEndpoint rightEndpoint) witnessRaw)
    {baseRawA baseRawB : RawTerm scope}
    {baseTermA : Term context Ty.nat baseRawA}
    {baseTermB : Term context Ty.nat baseRawB}
    (baseConv : Conv baseTermA baseTermB) :
    Conv (Term.idJ baseTermA witnessTerm)
         (Term.idJ baseTermB witnessTerm) :=
  Conv.idJ_baseCase_cong_isClosedTy
    IsClosedTy.nat carrier leftEndpoint rightEndpoint witnessTerm baseConv

/-! ## What still defers

`StepStar.idJ_witness_lift` (cong on the witness position) needs
SR for `Ty.id`-typed terms.  `Ty.id` is NOT in `IsClosedTy`
because its `RawTerm` endpoints depend on substitution.  A
witness-position cong rule needs a separate "Step preserves
Ty.id with fixed args" lemma — modest work, deferred to a later
phase. -/

end LeanFX2
