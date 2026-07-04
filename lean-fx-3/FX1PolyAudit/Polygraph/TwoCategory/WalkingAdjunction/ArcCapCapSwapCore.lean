import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapCapSwapCore

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCapCapSwapCore — zero-axiom gate

Per-declaration zero-axiom gate for the cap-cap partition-simulation core's wire leg.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.capCapSwap_openMap
#assert_no_axioms FX1Poly.Polygraph.natBeq_self
#assert_no_axioms FX1Poly.Polygraph.natBeq_comm
#assert_no_axioms FX1Poly.Polygraph.boolFalseAnd
#assert_no_axioms FX1Poly.Polygraph.boolOrFalse
#assert_no_axioms FX1Poly.Polygraph.boolTrueOr
#assert_no_axioms FX1Poly.Polygraph.boolFalseOr
#assert_no_axioms FX1Poly.Polygraph.boolTrueAnd
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_unionFindJoin_split
#assert_no_axioms FX1Poly.Polygraph.boolEqOfIff
#assert_no_axioms FX1Poly.Polygraph.orElimBit
#assert_no_axioms FX1Poly.Polygraph.orIntroLeftBit
#assert_no_axioms FX1Poly.Polygraph.orIntroRightBit
#assert_no_axioms FX1Poly.Polygraph.andElimBit
#assert_no_axioms FX1Poly.Polygraph.andIntroBit
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_true_iff_rootsEqual
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_true_symm
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_unionFindJoin_true_iff
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_join_cross_swap
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_two_joins_swap
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_two_joins_comm
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_unionFindJoin_congr
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_join_blocks_comm
#assert_no_axioms FX1Poly.Polygraph.renameLinks_ofFixedEntries
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_renameLinks
#assert_no_axioms FX1Poly.Polygraph.arcFreshBlockTransposition_atBase
#assert_no_axioms FX1Poly.Polygraph.arcFreshBlockTransposition_atSuccessor
#assert_no_axioms FX1Poly.Polygraph.capCapSwap_componentsCorr
#assert_no_axioms FX1Poly.Polygraph.boolAndComm
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_freshAttach_transparent
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_unionFindJoin_ofMerged
#assert_no_axioms FX1Poly.Polygraph.capCapSwap_loopsEq

end FX1PolyAudit
