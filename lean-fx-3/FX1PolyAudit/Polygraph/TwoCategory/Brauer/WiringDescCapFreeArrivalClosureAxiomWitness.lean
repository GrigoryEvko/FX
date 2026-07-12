import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCapFreeArrivalClosure

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescCapFreeArrivalClosureAxiomWitness — independent #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the fuel-based
`#assert_no_axioms` gate in the per-file twin) over every headline declaration of the BRAUER cap-free arrival closure —
the cap-free-right lemma, the generic cap-free arrival provider, the result-word projector, the cap-free-stripped driver,
the four-class fires / fates, the r47 census subsumption, the out-of-scope guard, the honest reflexive-not-canonical wall
pin, the markers, and the machine-checked terminal state.  Each must print "does not depend on any axioms".  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.capFreeRight_of_hasNoCap
#print axioms FX1Poly.Polygraph.outcomeCapFreeArrival
#print axioms FX1Poly.Polygraph.RegionCupOutcome.resultWord
#print axioms FX1Poly.Polygraph.flatRegionDriveArrivalStripped
#print axioms FX1Poly.Polygraph.capFreeArrivalFiresOnFourClasses
#print axioms FX1Poly.Polygraph.capFreeArrivalFates
#print axioms FX1Poly.Polygraph.capFreeArrivalSubsumesR47Census
#print axioms FX1Poly.Polygraph.capFreeArrivalOutOfScopeStaysNone
#print axioms FX1Poly.Polygraph.flatRegionDriveArrivalReflexiveNotCanonical
#print axioms FX1Poly.Polygraph.fxBrauer_hasCapFreeArrivalClosure
#print axioms FX1Poly.Polygraph.fxBrauer_hasCanonicalCapFreeSink
#print axioms FX1Poly.Polygraph.fxBrauer_capFreeArrivalClosureTerminalState

end FX1PolyAudit
