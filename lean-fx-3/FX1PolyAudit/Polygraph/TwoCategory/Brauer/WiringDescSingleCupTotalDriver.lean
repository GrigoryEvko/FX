import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescSingleCupTotalDriver

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescSingleCupTotalDriver — zero-axiom gate

Per-declaration zero-axiom gate for the BRAUER r45 recursive total driver (R1) + the JAM-B loop-with-suffix (R2): the
loops-monotonicity engine, the loop-with-suffix positivity / non-emptiness / typed outcome, the single-slide one-step
reducer, the driven dispatch + fuel driver, the census / JAM-B / deep-tail fires, the honesty markers, and the
machine-checked terminal state.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega` — the loops-monotonicity is
`Nat.le_add_right`/`Nat.le_trans`, the non-emptiness refutation is `Nat.not_succ_le_zero` (not `Nat.succ_ne_zero`), the
driver is fuel-STRUCTURAL (no `WellFounded.fix` / `termination_by`), and the outcome transports are the shipped
explicit-motive `RegionCupOutcome.prepend` / `.transportByRegionEq`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stepBrauerAtomLoopsNonDecreasing
#assert_no_axioms FX1Poly.Polygraph.processFoldLoopsNonDecreasing
#assert_no_axioms FX1Poly.Polygraph.loopWithSuffixLoopsPositive
#assert_no_axioms FX1Poly.Polygraph.loopWithSuffixNotEmpty
#assert_no_axioms FX1Poly.Polygraph.outcomeLoopWithSuffix
#assert_no_axioms FX1Poly.Polygraph.outcomeLoopWithSuffixFate
#assert_no_axioms FX1Poly.Polygraph.slidDistantStepAtom
#assert_no_axioms FX1Poly.Polygraph.distantStepSlideConv
#assert_no_axioms FX1Poly.Polygraph.reduceLeadingDistantSlide
#assert_no_axioms FX1Poly.Polygraph.flatRegionDispatchLoopSuffix
#assert_no_axioms FX1Poly.Polygraph.flatRegionDispatchDriven
#assert_no_axioms FX1Poly.Polygraph.driveRegion
#assert_no_axioms FX1Poly.Polygraph.driverFuel
#assert_no_axioms FX1Poly.Polygraph.flatRegionDrive
#assert_no_axioms FX1Poly.Polygraph.driveRegionFiresOnCensus
#assert_no_axioms FX1Poly.Polygraph.flatRegionDriveFiresOnJamB
#assert_no_axioms FX1Poly.Polygraph.reduceLeadingDistantSlideFiresOnDeepTail
#assert_no_axioms FX1Poly.Polygraph.reduceLeadingDistantSlideDropsMeasure
#assert_no_axioms FX1Poly.Polygraph.flatRegionDriveDeepTailStaysNone
#assert_no_axioms FX1Poly.Polygraph.flatRegionDriveOutOfScopeStaysNone
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasRecursiveTotalDriver
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasDeepTailReachabilityShape
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_singleCupTotalDriverTerminalState

end FX1PolyAudit
