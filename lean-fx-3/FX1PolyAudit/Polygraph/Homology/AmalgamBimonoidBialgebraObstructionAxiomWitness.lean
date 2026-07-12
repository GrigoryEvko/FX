import FX1Poly.Polygraph.Homology.AmalgamBimonoidBialgebraObstruction

/-! # FX1PolyAudit.Polygraph.Homology.AmalgamBimonoidBialgebraObstructionAxiomWitness — independent
    #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the
fuel-based `#assert_no_axioms` gate in the per-file twin) over every headline declaration of TOWER-MV
r3 — the bimonoid amalgamation obstruction in the PROP grading: the without-law and with-law chain
complexes, the two-complex Smith comparison, and the probe-decided degree-1 class that is nontrivial
without the bialgebra law and killed with it.  Each must print "does not depend on any axioms".
Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.Homology.bimonoidArityBoundaryIsR1Regrade
#print axioms FX1Poly.Polygraph.Homology.bimonoidWithoutLawIsChainComplex
#print axioms FX1Poly.Polygraph.Homology.bimonoidWithLawIsChainComplex
#print axioms FX1Poly.Polygraph.Homology.bimonoidBialgebraColumnIsLastWithLawColumn
#print axioms FX1Poly.Polygraph.Homology.bimonoidArityBoundaryReducesToSmith
#print axioms FX1Poly.Polygraph.Homology.bimonoidWithoutLawReducesToSmith
#print axioms FX1Poly.Polygraph.Homology.bimonoidWithLawReducesToSmith
#print axioms FX1Poly.Polygraph.Homology.bimonoidTwoComplexComparison

end FX1PolyAudit
