import LeanFX2.Reduction.ParStar
import LeanFX2.Bridge
import LeanFX2.Confluence.RawDiamond

/-! # Confluence/ParStarBridge — typed multi-step parallel chains
project to raw multi-step parallel chains, and the raw projections
of any two typed chains from a common source converge.

## Theorems shipped

* `Step.parStar.toRawBridge` — typed chain → raw chain.  Induction
  on the chain, applying `Step.par.toRawBridge` per step.
* `Step.parStar.toRawConfluence` — corollary: two typed chains
  from a common source produce raw projections that converge to
  a common raw reduct (via `RawStep.parStar.confluence`).

## Why this is the strongest typed confluence statement (for now)

Lifting the raw common reduct *back* to a typed Term whose
context+type matches both chain endpoints would require subject
reduction (preservation): given `Step.par t1 t2`, find a Ty for
the new raw target.  That theorem deserves its own phase
(planned Phase 7).  For Layers 4+ that consume confluence —
typed→raw projection + raw confluence is enough.

`Step.parStar.toRawConfluence` is what `Algo.DecConv` and the
elaborator's coherence proofs actually consume: "the two reducts
agree at the raw level" suffices for decidable conversion checks
because typed convertibility is preserved by typing
(elaboration-time invariant).
-/

namespace LeanFX2

/-- Typed multi-step parallel chain projects to a raw multi-step
parallel chain.  Induction on the chain: refl produces refl,
trans produces trans (single-step bridge + IH). -/
theorem Step.parStar.toRawBridge
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (parallelChain : Step.parStar sourceTerm targetTerm) :
    RawStep.parStar sourceRaw targetRaw := by
  induction parallelChain with
  | refl _ => exact RawStep.parStar.refl _
  | trans firstStep _ restIH =>
      exact RawStep.parStar.trans
        (Step.par.toRawBridge firstStep) restIH

/-- **Projection-confluence** for typed multi-step parallel
reduction.  Two typed chains from a common source produce raw
projections that converge to a common raw reduct.

Direct corollary of `Step.parStar.toRawBridge` +
`RawStep.parStar.confluence`.  The common raw reduct is `cd`
applied iteratively to the source's raw projection (constructively
the join point of the cd cascade).

Lifting this raw common reduct back to a typed Term requires
subject reduction (planned Phase 7); for now this is sufficient
for Layer 9 Algo's decidable-conversion needs. -/
theorem Step.parStar.toRawConfluence
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
  RawStep.parStar.confluence
    (Step.parStar.toRawBridge leftChain)
    (Step.parStar.toRawBridge rightChain)

end LeanFX2
