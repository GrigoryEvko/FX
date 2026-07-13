import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcTwoBlockRootTransposition

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcTwoBlockRootTransposition — zero-axiom gate (MODE-COMMUTE r27)

Per-declaration zero-axiom gate for the r27 uniform two-block root-transposition engine: the locality
bricks (unmentioned own-root, the window-rotation zone preservation, the base root conjugation), the
uniform `twoJoinBlock` shape with its cup/cap definitional bridges and forest preservation, the block
root-map closed form with its untouched-probe and same-component locality corollaries, the flat
two-block closed form, the guarded-if transposition, the sigma-twisted two-block transposition
`twoBlocksSigma_rootComm` (r26's BRICK X, general form), its cap x cap fire, the shipped marker, and
the three untouched-false honesty pins.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.
Registered in `AuditAll` (paired with the independent `#print axioms` witness). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.unionFindRootOf_of_unmentioned
#assert_no_axioms FX1Poly.Polygraph.blockRotate_preservesAtOrAboveBase
#assert_no_axioms FX1Poly.Polygraph.rootComm_of_windowPermutation
#assert_no_axioms FX1Poly.Polygraph.twoJoinBlock
#assert_no_axioms FX1Poly.Polygraph.stepCupArc_links_twoJoinBlock
#assert_no_axioms FX1Poly.Polygraph.stepCapArc_links_twoJoinBlock
#assert_no_axioms FX1Poly.Polygraph.isUnionFindForest_twoJoinBlock
#assert_no_axioms FX1Poly.Polygraph.rootOf_twoJoinBlock
#assert_no_axioms FX1Poly.Polygraph.rootOf_twoJoinBlock_untouched
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_twoJoinBlock_untouched
#assert_no_axioms FX1Poly.Polygraph.rootOf_twoBlocks_flat
#assert_no_axioms FX1Poly.Polygraph.flatIfPair_transpose
#assert_no_axioms FX1Poly.Polygraph.twoBlocksSigma_rootComm
#assert_no_axioms FX1Poly.Polygraph.twoBlocksSigma_rootComm_capCapFire
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasTwoBlockRootTranspositionEngine
#assert_no_axioms FX1Poly.Polygraph.arcTwoBlockRootTransposition_disjointWhiskerSupport_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcTwoBlockRootTransposition_swapRenameableProof2_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcTwoBlockRootTransposition_samePartitionFresh_stays_false

end FX1PolyAudit
