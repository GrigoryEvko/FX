import LeanFX2.Reduction.Conv
import LeanFX2.Reduction.StepStarToPar
import LeanFX2.Confluence.ParStarBridge

/-! # Confluence/ConvBridge — raw projection of typed Conv

Combines Phase 6.D's `Step.parStar.toRawConfluence` with Phase
6.E's `StepStar.toParStar` to give the headline corollary:

`Conv.toRawConfluence`: a typed `Conv sourceTerm targetTerm`
witnesses that the raw projections `sourceRaw` and `targetRaw`
converge to a common raw reduct.

This is the strongest typed Conv corollary available without
subject reduction (Phase 7).  Sufficient for elaborator
coherence and Layer 9 Algo's decidable conversion checks: the
raw form is canonical, so once two elaborated terms agree on
the raw projection, their types must be convertible (typing is
preserved by the elaborator).
-/

namespace LeanFX2

/-- **Raw-projection corollary** of typed `Conv`.

A typed convertibility witness directly produces a raw-side
join: the typed midpoint's raw projection IS the common reduct,
reachable from both endpoints' raw projections via single-step
StepStar-bridge composition.

Pipeline:
1. `Conv` unpacks to two `StepStar` chains converging at typed
   midTerm with raw projection midRaw.
2. `StepStar.toParStar` lifts each chain to `Step.parStar`.
3. `Step.parStar.toRawBridge` projects each to raw chains
   landing at midRaw — which IS the common reduct.

No `Step.parStar.toRawConfluence` needed because the typed Conv
already provides the join (unlike "given two chains FROM a
common source", here we have "two chains TO a common target"). -/
theorem Conv.toRawJoin
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (convertibility : Conv sourceTerm targetTerm) :
    ∃ commonRaw,
      RawStep.parStar sourceRaw commonRaw ∧
      RawStep.parStar targetRaw commonRaw := by
  obtain ⟨_, midRaw, _, sourceChain, targetChain⟩ := convertibility
  exact ⟨midRaw,
    Step.parStar.toRawBridge sourceChain.toParStar,
    Step.parStar.toRawBridge targetChain.toParStar⟩

end LeanFX2
