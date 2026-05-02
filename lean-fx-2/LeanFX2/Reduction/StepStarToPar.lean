import LeanFX2.Reduction.ParStar

/-! # Reduction/StepStarToPar — lift StepStar to Step.parStar

Each `Step` lifts to `Step.par` via `Step.toPar`.  Each
`StepStar` chain therefore lifts to a `Step.parStar` chain:
map `Step.toPar` per step, prepend with `Step.parStar.trans`.

Used by Layer 4 / Layer 9 to apply Phase 6.D's typed
projection-confluence to plain `Conv` (which is defined over
`StepStar`).
-/

namespace LeanFX2

/-- Lift a single-step chain into a parallel-step chain.  Each
`Step` becomes a `Step.par` with refl in unchanging positions
(`Step.toPar`); the chain structure is preserved. -/
theorem StepStar.toParStar
    {mode : Mode} {level scope : Nat} {context : Ctx mode level scope}
    {sourceType targetType : Ty level scope}
    {sourceRaw targetRaw : RawTerm scope}
    {sourceTerm : Term context sourceType sourceRaw}
    {targetTerm : Term context targetType targetRaw}
    (chain : StepStar sourceTerm targetTerm) :
    Step.parStar sourceTerm targetTerm := by
  induction chain with
  | refl _ => exact Step.parStar.refl _
  | step single _ restIH =>
      exact Step.parStar.trans (Step.toPar single) restIH

end LeanFX2
