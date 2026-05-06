import LeanFX2.Confluence.ConvBridge

/-! # Confluence/ChurchRosser — multi-step Church-Rosser corollaries

Multi-step confluence at the raw level (`RawStep.parStar.confluence`,
shipped in `Confluence/RawDiamond.lean`) lifts to typed corollaries
via the typed→raw bridge `Step.parStar.toRawBridge`.

## Typed-input, raw-output Church-Rosser

```lean
theorem Step.parStar.churchRosserRaw
    {sourceTerm leftTarget rightTarget : ...}
    (leftChain : Step.parStar sourceTerm leftTarget)
    (rightChain : Step.parStar sourceTerm rightTarget) :
    ∃ commonRaw,
      RawStep.parStar leftRaw commonRaw ∧
      RawStep.parStar rightRaw commonRaw
```

The proof projects each typed chain to a raw chain via
`Step.parStar.toRawBridge`, then applies
`RawStep.parStar.confluence`.  This headline corollary already
ships in `ParStarBridge.lean` as `Step.parStar.toRawConfluence` —
this file re-exposes it under the canonical Church-Rosser name and
adds a `StepStar` variant that goes through `StepStar.toParStar`.

## StepStar variant

`StepStar` is the RT closure of single-step `Step`; `Step.parStar`
is the RT closure of `Step.par`.  Every `Step` is a `Step.par`
(via `Step.toPar`), so `StepStar` chains lift to `Step.parStar`
chains via `StepStar.toParStar`.  Multi-step confluence on
`StepStar` is therefore a one-line corollary of
`Step.parStar.churchRosserRaw`.

## Why not a typed-output Church-Rosser?

Same reason as `Diamond.lean`: lifting the raw common reduct back
to a typed `Term context commonType commonRaw` requires subject
reduction for `Step.par` (and hence for `StepStar` via the
embedding).  Subject reduction is M05/M06 work (Phase 7).  Until
then, the raw form is the strongest typed-input join shippable.

`Algo/DecConv.lean` and the elaborator's coherence proofs consume
the raw join: typed convertibility is preserved by typing
(elaboration-time invariant), so once two reducts agree at the
raw level, their typed terms are convertible by construction.

## What this file ships (zero axioms)

* `Step.parStar.churchRosserRaw` — typed inputs, raw common reduct,
  multi-step parallel reduction (alias of
  `Step.parStar.toRawConfluence` from `ParStarBridge.lean`)
* `StepStar.churchRosserRaw` — typed inputs, raw common reduct,
  multi-step `Step` via `StepStar.toParStar` lift
* `Conv.canonicalRaw` — definitional content of `Conv` as raw
  join (alias of `Conv.toRawJoin` from `ConvBridge.lean`)
* `Conv.transRaw` — typed Conv composition expressed at raw level

## Conv.trans — typed version requires SR

The classical `Conv.trans` requires a typed common reduct from
two typed convergence triangles: given `Conv s t` and `Conv t u`,
need a typed midpoint reachable from both `s` and `u`.  This
needs subject reduction to lift the raw confluence join back to
a typed Term.  Until SR ships, the raw analog `Conv.transRaw`
suffices for the elaborator's needs.

## Dependencies

* `Confluence/ParStarBridge.lean` — `Step.parStar.toRawConfluence`
* `Confluence/ConvBridge.lean` — `Conv.toRawJoin`
* `Reduction/StepStarToPar.lean` — `StepStar.toParStar`

## Downstream consumers

* `Confluence/CanonicalForm.lean` — canonical form via Conv
* `Algo/DecConv.lean` — decidable conversion
-/

namespace LeanFX2

/-- **Typed-input, raw-output Church-Rosser** for parallel reduction.
Two typed multi-step parallel chains from a common source produce
raw projections that converge to a common raw reduct.

Alias of `Step.parStar.toRawConfluence` (which lives in
`ParStarBridge.lean`).  Re-exported here under the canonical
Church-Rosser name so downstream consumers reach for it through
the confluence module hierarchy.

Lifting the raw common reduct to a typed Term requires subject
reduction (Phase 7); see file docstring. -/
theorem Step.parStar.churchRosserRaw
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType leftType rightType : Ty level scope}
    {sourceRaw leftRaw rightRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {leftTarget : Term context leftType leftRaw}
    {rightTarget : Term context rightType rightRaw}
    (leftChain : Step.parStar sourceTerm leftTarget)
    (rightChain : Step.parStar sourceTerm rightTarget) :
    ∃ commonRaw,
      RawStep.parStar leftRaw commonRaw ∧
      RawStep.parStar rightRaw commonRaw :=
  Step.parStar.toRawConfluence leftChain rightChain

/-- **Typed-input, raw-output Church-Rosser** for `StepStar` (RT
closure of single-step `Step`).  Lifts each `StepStar` chain to a
`Step.parStar` chain via `StepStar.toParStar`, then applies
`Step.parStar.churchRosserRaw`. -/
theorem StepStar.churchRosserRaw
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType leftType rightType : Ty level scope}
    {sourceRaw leftRaw rightRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {leftTarget : Term context leftType leftRaw}
    {rightTarget : Term context rightType rightRaw}
    (leftChain : StepStar sourceTerm leftTarget)
    (rightChain : StepStar sourceTerm rightTarget) :
    ∃ commonRaw,
      RawStep.parStar leftRaw commonRaw ∧
      RawStep.parStar rightRaw commonRaw :=
  Step.parStar.churchRosserRaw leftChain.toParStar rightChain.toParStar

/-- **Typed Conv as raw join** — alias of `Conv.toRawJoin`.

A typed convertibility witness IS a raw join (definitionally),
since `Conv := ∃-StepStar` and the typed midpoint's raw projection
is reachable from both endpoints' raw projections via
`StepStar.toParStar` + `Step.parStar.toRawBridge`.  This is the
content of "canonical form" in lean-fx-2's design: Conv unpacks
to a raw join. -/
theorem Conv.canonicalRaw
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar sourceRaw commonRaw ∧
      RawStep.parStar targetRaw commonRaw :=
  Conv.toRawJoin convertibility

/-- **Raw-level transitivity** for typed Conv.  Given two typed
Conv triangles meeting at `middleTerm`, produce a raw common
reduct reachable from both `sourceRaw` and `farRaw`.

Pipeline:
1. Project each Conv to a raw join via `Conv.canonicalRaw`.
2. The middle endpoint's raw projection is the common point of
   the two raw joins.
3. Apply `RawStep.parStar.confluence` at the middle to combine
   the two raw triangles into a single raw join over
   `sourceRaw`/`farRaw`.

A typed `Conv.trans` would lift this raw join to a typed common
reduct via subject reduction; that step deferred to Phase 7. -/
theorem Conv.transRaw
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType middleType farType : Ty level scope}
    {sourceRaw middleRaw farRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {middleTerm : Term context middleType middleRaw}
    {farTerm : Term context farType farRaw}
    (firstConvertibility : Conv sourceTerm middleTerm)
    (secondConvertibility : Conv middleTerm farTerm) :
    ∃ commonRaw,
      RawStep.parStar sourceRaw commonRaw ∧
      RawStep.parStar farRaw commonRaw := by
  obtain ⟨firstJoinRaw, sourceToFirstJoin, middleToFirstJoin⟩ :=
    Conv.canonicalRaw firstConvertibility
  obtain ⟨secondJoinRaw, middleToSecondJoin, farToSecondJoin⟩ :=
    Conv.canonicalRaw secondConvertibility
  obtain ⟨commonReduct, firstJoinToCommon, secondJoinToCommon⟩ :=
    RawStep.parStar.confluence middleToFirstJoin middleToSecondJoin
  exact ⟨commonReduct,
    RawStep.parStar.append sourceToFirstJoin firstJoinToCommon,
    RawStep.parStar.append farToSecondJoin secondJoinToCommon⟩

end LeanFX2
