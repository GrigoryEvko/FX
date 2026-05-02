import LeanFX2.Reduction.StepStarToPar

/-! Phase 6.E StepStar → Step.parStar lift zero-axiom audit.

Bridges `StepStar` (used by `Conv`) into `Step.parStar` (used by
Phase 6.D's `toRawConfluence`).  The lift is a 4-line induction
(refl → refl, step → trans (Step.toPar single) restIH).

This is the missing piece for `Conv.toRawConfluence`: combine
`StepStar.toParStar` with `Step.parStar.toRawConfluence` and
`Conv` becomes a corollary at the raw projection level.

Phase 7 (subject reduction) will lift the raw common reduct back
to a typed Term, completing typed Conv.trans.
-/

#print axioms LeanFX2.StepStar.toParStar
