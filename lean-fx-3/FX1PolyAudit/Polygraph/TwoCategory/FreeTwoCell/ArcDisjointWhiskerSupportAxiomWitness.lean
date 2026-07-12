import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcDisjointWhiskerSupport

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcDisjointWhiskerSupportAxiomWitness — independent #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the
fuel-based `#assert_no_axioms` gate in the per-file twin) over every declaration of the r23
whisker-support renaming levers (MODE-COMMUTE r23, honest BRANCH (b)): the two per-atom cup/cap
renaming levers, their compound-sigma instances, the identity structural base, the identity-corner
base case, the concrete cup-lever fire, the step-lever marker, the r23-open honesty pin, and the
refuted-keystone honesty pin.

Each must print "does not depend on any axioms".  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.renameLinks_stepCupArc
#print axioms FX1Poly.Polygraph.renameLinks_stepCapArc
#print axioms FX1Poly.Polygraph.renameLinks_compoundTransposition_stepCupArc
#print axioms FX1Poly.Polygraph.renameLinks_compoundTransposition_stepCapArc
#print axioms FX1Poly.Polygraph.runArcCell_id
#print axioms FX1Poly.Polygraph.disjointWhiskerSupport_id_id
#print axioms FX1Poly.Polygraph.renameLinks_stepCupArc_probe
#print axioms FX1Poly.Polygraph.fxMode_hasDisjointWhiskerStepLevers
#print axioms FX1Poly.Polygraph.fxMode_hasDisjointWhiskerSupport
#print axioms FX1Poly.Polygraph.arcDisjointWhiskerSupport_samePartitionFresh_stays_open

end FX1PolyAudit
