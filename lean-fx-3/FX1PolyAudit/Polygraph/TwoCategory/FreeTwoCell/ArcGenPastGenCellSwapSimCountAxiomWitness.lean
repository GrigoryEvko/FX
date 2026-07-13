import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcGenPastGenCellSwapSimCount

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcGenPastGenCellSwapSimCountAxiomWitness — independent #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the
fuel-based `#assert_no_axioms` gate in the per-file twin) over every declaration of the r27
gen-past-gen cell-granularity base case.  Each must print "does not depend on any axioms".
Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.arcGenPastGenSwapSimCount_capCap
#print axioms FX1Poly.Polygraph.fxMode_hasGenPastGenCellSwapBaseCase
#print axioms FX1Poly.Polygraph.arcGenPastGenCellSwap_disjointWhiskerSupport_stays_false
#print axioms FX1Poly.Polygraph.arcGenPastGenCellSwap_swapRenameableProof2_stays_false
#print axioms FX1Poly.Polygraph.arcGenPastGenCellSwap_partitionCommute_stays_false
#print axioms FX1Poly.Polygraph.arcGenPastGenCellSwap_samePartitionFresh_stays_false

end FX1PolyAudit
