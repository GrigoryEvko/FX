import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescSingleCupTotalDriver

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescSingleCupTotalDriverAxiomWitness — independent #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the fuel-based
`#assert_no_axioms` gate in the per-file twin) over every headline declaration of the BRAUER r45 recursive total driver
(R1) + JAM-B loop-with-suffix (R2) — the loops-monotonicity engine, the loop-with-suffix outcome, the single-slide
reducer, the driven dispatch + fuel driver, the census / JAM-B / deep-tail fires, and the machine-checked terminal
state.  Each must print "does not depend on any axioms".  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.stepBrauerAtomLoopsNonDecreasing
#print axioms FX1Poly.Polygraph.processFoldLoopsNonDecreasing
#print axioms FX1Poly.Polygraph.loopWithSuffixLoopsPositive
#print axioms FX1Poly.Polygraph.loopWithSuffixNotEmpty
#print axioms FX1Poly.Polygraph.outcomeLoopWithSuffix
#print axioms FX1Poly.Polygraph.reduceLeadingDistantSlide
#print axioms FX1Poly.Polygraph.flatRegionDispatchLoopSuffix
#print axioms FX1Poly.Polygraph.flatRegionDispatchDriven
#print axioms FX1Poly.Polygraph.driveRegion
#print axioms FX1Poly.Polygraph.flatRegionDrive
#print axioms FX1Poly.Polygraph.driveRegionFiresOnCensus
#print axioms FX1Poly.Polygraph.flatRegionDriveFiresOnJamB
#print axioms FX1Poly.Polygraph.reduceLeadingDistantSlideFiresOnDeepTail
#print axioms FX1Poly.Polygraph.flatRegionDriveDeepTailStaysNone
#print axioms FX1Poly.Polygraph.fxBrauer_hasRecursiveTotalDriver
#print axioms FX1Poly.Polygraph.fxBrauer_hasDeepTailReachabilityShape
#print axioms FX1Poly.Polygraph.fxBrauer_singleCupTotalDriverTerminalState

end FX1PolyAudit
