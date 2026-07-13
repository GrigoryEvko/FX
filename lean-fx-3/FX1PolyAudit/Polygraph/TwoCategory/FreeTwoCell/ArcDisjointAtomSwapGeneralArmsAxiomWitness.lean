import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcDisjointAtomSwapGeneralArms

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcDisjointAtomSwapGeneralArmsAxiomWitness — independent #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the fuel-based
`#assert_no_axioms` gate in the per-file twin) over every public declaration of the r27 general
disjoint atom-swap arms: the list read/splice lemmas, the block-rotation value read-offs, the three
general full-sim swap arms, their fires, the marker, and the honesty pins.

Each must print "does not depend on any axioms".  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.natListGetAt_consSucc
#print axioms FX1Poly.Polygraph.natListGetAt_removeTwoAt_shift
#print axioms FX1Poly.Polygraph.natListGetAt_removeTwoAt_below
#print axioms FX1Poly.Polygraph.natListInsertAt_succ
#print axioms FX1Poly.Polygraph.natListGetAt_insertAt_shift
#print axioms FX1Poly.Polygraph.natListGetAt_insertAt_below
#print axioms FX1Poly.Polygraph.blockRotate_oneOne_base
#print axioms FX1Poly.Polygraph.blockRotate_oneOne_succ
#print axioms FX1Poly.Polygraph.blockRotate_threeOne_cup
#print axioms FX1Poly.Polygraph.blockRotate_threeOne_cap
#print axioms FX1Poly.Polygraph.blockRotate_oneThree_cap
#print axioms FX1Poly.Polygraph.blockRotate_oneThree_cup
#print axioms FX1Poly.Polygraph.arcDisjointCapCapSwapSimCount_ofWellFormed
#print axioms FX1Poly.Polygraph.arcDisjointCupCapSwapSimCount_ofWellFormed
#print axioms FX1Poly.Polygraph.arcDisjointCapCupSwapSimCount_ofWellFormed
#print axioms FX1Poly.Polygraph.capCapDisjointSwap_fullSimCount
#print axioms FX1Poly.Polygraph.mixedCupCapSwap_fullSimCount
#print axioms FX1Poly.Polygraph.mixedCapCupSwap_fullSimCount
#print axioms FX1Poly.Polygraph.fxMode_hasDisjointAtomSwapGeneralArms
#print axioms FX1Poly.Polygraph.arcDisjointAtomSwapGeneralArms_disjointWhiskerSupport_stays_false
#print axioms FX1Poly.Polygraph.arcDisjointAtomSwapGeneralArms_swapRenameableProof2_stays_false
#print axioms FX1Poly.Polygraph.arcDisjointAtomSwapGeneralArms_partitionCommute_stays_false
#print axioms FX1Poly.Polygraph.arcDisjointAtomSwapGeneralArms_samePartitionFresh_stays_false

end FX1PolyAudit
