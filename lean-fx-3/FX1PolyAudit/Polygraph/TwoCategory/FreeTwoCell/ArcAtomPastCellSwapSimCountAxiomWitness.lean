import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcAtomPastCellSwapSimCount

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcAtomPastCellSwapSimCountAxiomWitness — independent #print axioms (MODE-COMMUTE r28)

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the
fuel-based `#assert_no_axioms` gate in the per-file twin) over every declaration of the r28
`atomPastCell` brick.  Each must print "does not depend on any axioms".  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.ArcBoundedSwapCarrier
#print axioms FX1Poly.Polygraph.arcBoundedSwapCarrier_identity
#print axioms FX1Poly.Polygraph.arcBoundedSwapCarrier_weaken
#print axioms FX1Poly.Polygraph.arcBoundedSwapCarrier_comp
#print axioms FX1Poly.Polygraph.arcBoundedSwapCarrier_blockRotate
#print axioms FX1Poly.Polygraph.arcStepSimCount_extendByCommonCell
#print axioms FX1Poly.Polygraph.natListGetAt_memOfBelow
#print axioms FX1Poly.Polygraph.arcCapAtomPastCellSwapSimCount
#print axioms FX1Poly.Polygraph.arcCupAtomPastCellSwapSimCount
#print axioms FX1Poly.Polygraph.arcAtomPastCellFireSeed
#print axioms FX1Poly.Polygraph.arcAtomPastCellFireSeed_isWellFormed
#print axioms FX1Poly.Polygraph.arcCapAtomPastThreeAtomCell_fired
#print axioms FX1Poly.Polygraph.arcCupPastCellFireSeed
#print axioms FX1Poly.Polygraph.arcCupPastCellFireSeed_isWellFormed
#print axioms FX1Poly.Polygraph.arcCupAtomPastThreeAtomCell_fired
#print axioms FX1Poly.Polygraph.fxMode_hasArcAtomPastCellSwapSimCount
#print axioms FX1Poly.Polygraph.arcAtomPastCell_disjointWhiskerSupport_stays_false
#print axioms FX1Poly.Polygraph.arcAtomPastCell_swapRenameableProof2_stays_false
#print axioms FX1Poly.Polygraph.arcAtomPastCell_partitionCommute_stays_false
#print axioms FX1Poly.Polygraph.arcAtomPastCell_samePartitionFresh_stays_false

end FX1PolyAudit
