import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcTwoBlockRootTransposition

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcTwoBlockRootTranspositionAxiomWitness — independent #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the fuel-based
`#assert_no_axioms` gate in the per-file twin) over every declaration of the r27 uniform two-block
root-transposition engine: the locality bricks, the uniform `twoJoinBlock` shape with its definitional
bridges and forest preservation, the closed forms, the guarded-if transposition, the sigma-twisted
two-block transposition (BRICK X, general form), its fire, the marker, and the honesty pins.

Each must print "does not depend on any axioms".  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.unionFindRootOf_of_unmentioned
#print axioms FX1Poly.Polygraph.blockRotate_preservesAtOrAboveBase
#print axioms FX1Poly.Polygraph.rootComm_of_windowPermutation
#print axioms FX1Poly.Polygraph.twoJoinBlock
#print axioms FX1Poly.Polygraph.stepCupArc_links_twoJoinBlock
#print axioms FX1Poly.Polygraph.stepCapArc_links_twoJoinBlock
#print axioms FX1Poly.Polygraph.isUnionFindForest_twoJoinBlock
#print axioms FX1Poly.Polygraph.rootOf_twoJoinBlock
#print axioms FX1Poly.Polygraph.rootOf_twoJoinBlock_untouched
#print axioms FX1Poly.Polygraph.isSameComponent_twoJoinBlock_untouched
#print axioms FX1Poly.Polygraph.rootOf_twoBlocks_flat
#print axioms FX1Poly.Polygraph.flatIfPair_transpose
#print axioms FX1Poly.Polygraph.twoBlocksSigma_rootComm
#print axioms FX1Poly.Polygraph.twoBlocksSigma_rootComm_capCapFire
#print axioms FX1Poly.Polygraph.fxMode_hasTwoBlockRootTranspositionEngine
#print axioms FX1Poly.Polygraph.arcTwoBlockRootTransposition_disjointWhiskerSupport_stays_false
#print axioms FX1Poly.Polygraph.arcTwoBlockRootTransposition_swapRenameableProof2_stays_false
#print axioms FX1Poly.Polygraph.arcTwoBlockRootTransposition_samePartitionFresh_stays_false

end FX1PolyAudit
