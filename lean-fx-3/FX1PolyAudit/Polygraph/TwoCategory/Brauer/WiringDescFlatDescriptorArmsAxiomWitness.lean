import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescFlatDescriptorArms

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescFlatDescriptorArmsAxiomWitness — independent #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the fuel-based
`#assert_no_axioms` gate in the per-file twin) over every headline declaration of the BRAUER r44 deferred flat→descriptor
ARMS — the two SNAKE arms, the extended head-cup / working-region extractors, the flat synthesis, the coverage upgrade,
the dispatch firing, and the machine-checked terminal state.  Each must print "does not depend on any axioms".
Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.extractCupHeadWithSnakes
#print axioms FX1Poly.Polygraph.extractWorkingRegionWithSnakes
#print axioms FX1Poly.Polygraph.flatRegionDispatchWithSnakes
#print axioms FX1Poly.Polygraph.extractWorkingRegionWithSnakes_coverage
#print axioms FX1Poly.Polygraph.flatDispatchWithSnakes_firesOnSnakes
#print axioms FX1Poly.Polygraph.fxBrauer_hasFlatSnakeArms
#print axioms FX1Poly.Polygraph.fxBrauer_flatSnakeArmsTerminalState

end FX1PolyAudit
