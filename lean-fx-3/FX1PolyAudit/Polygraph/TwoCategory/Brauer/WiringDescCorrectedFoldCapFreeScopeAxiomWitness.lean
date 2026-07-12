import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCorrectedFoldCapFreeScope

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescCorrectedFoldCapFreeScopeAxiomWitness —
independent #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the fuel-based
`#assert_no_axioms` gate in the per-file twin) over every headline declaration of the BRAUER r52 corrected-fold
cap-free scoping: the positionsFit guard machinery, the scoped fold target, the free-vs-genuine relation architectural
gap (the machine-checked refutation `not_brauerConvFree8_diagramInvariant`), the census-extension enumerators, the
cap-side defect autopsy, the structural idempotence corollary, the honesty markers, and the machine-checked terminal
state.  Each must print "does not depend on any axioms".  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.maxAtomPosition
#print axioms FX1Poly.Polygraph.hasBoundaryRoomForPositions
#print axioms FX1Poly.Polygraph.BrauerExt5CorrectedFoldReachesCapFree
#print axioms FX1Poly.Polygraph.cupSlide_diagram_soundAtBoundaryOne
#print axioms FX1Poly.Polygraph.cupSlide_diagram_notSoundAtBoundaryZero
#print axioms FX1Poly.Polygraph.not_brauerConvFree8_diagramInvariant
#print axioms FX1Poly.Polygraph.capFreeGuardHoldsRealizeFailCount
#print axioms FX1Poly.Polygraph.withCapRepresentativeFailCount
#print axioms FX1Poly.Polygraph.capSideDefect_atCapSlot0
#print axioms FX1Poly.Polygraph.capSideDefect_atCapSlot1
#print axioms FX1Poly.Polygraph.capSideDefect_atCapSlot2
#print axioms FX1Poly.Polygraph.representativeIdempotent_ofDiagramEq
#print axioms FX1Poly.Polygraph.fxBrauer_hasCorrectedFoldCapFreeScope
#print axioms FX1Poly.Polygraph.fxBrauer_hasCorrectedFoldCapFreeDischarged
#print axioms FX1Poly.Polygraph.fxBrauer_correctedFoldCapFreeScopeTerminalState

end FX1PolyAudit
