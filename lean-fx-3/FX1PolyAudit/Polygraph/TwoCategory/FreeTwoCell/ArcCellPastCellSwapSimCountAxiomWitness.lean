import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcCellPastCellSwapSimCount

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcCellPastCellSwapSimCountAxiomWitness — independent #print axioms (MODE-COMMUTE r28)

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the
fuel-based `#assert_no_axioms` gate in the per-file twin) over every declaration of the r28
`cellPastCell` brick.  Each must print "does not depend on any axioms".  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.isSameComponentFalse_symm
#print axioms FX1Poly.Polygraph.arcWindowsComponentDisjoint
#print axioms FX1Poly.Polygraph.arcCellPastCellSwapSimCount
#print axioms FX1Poly.Polygraph.arcThreeAtomCellPastThreeAtomCell_fired
#print axioms FX1Poly.Polygraph.arcCellPastCellCapFireSeed
#print axioms FX1Poly.Polygraph.arcCellPastCellCapFireSeed_isWellFormed
#print axioms FX1Poly.Polygraph.arcCounitCellPastThreeAtomCell_fired
#print axioms FX1Poly.Polygraph.fxMode_hasArcCellPastCellSwapSimCount
#print axioms FX1Poly.Polygraph.arcCellPastCell_disjointWhiskerSupport_stays_false
#print axioms FX1Poly.Polygraph.arcCellPastCell_swapRenameableProof2_stays_false
#print axioms FX1Poly.Polygraph.arcCellPastCell_partitionCommute_stays_false
#print axioms FX1Poly.Polygraph.arcCellPastCell_samePartitionFresh_stays_false

end FX1PolyAudit
