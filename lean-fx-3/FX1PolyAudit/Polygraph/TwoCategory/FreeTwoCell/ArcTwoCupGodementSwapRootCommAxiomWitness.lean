import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcTwoCupGodementSwapRootComm

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcTwoCupGodementSwapRootCommAxiomWitness — independent #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the fuel-based
`#assert_no_axioms` gate in the per-file twin) over every headline declaration of the pure two-cup Godement block
swap's `rootComm` automorphism and count bundle.  Each must print "does not depend on any axioms".  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.unionFindJoin_cons_of_roots
#print axioms FX1Poly.Polygraph.stepCupArc_links_cons
#print axioms FX1Poly.Polygraph.twoCupArcLinks_cons
#print axioms FX1Poly.Polygraph.twoCupGodement_rootComm

end FX1PolyAudit
