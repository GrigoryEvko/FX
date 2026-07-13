import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcDisjointAtomSwapGeneralArms

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcDisjointAtomSwapGeneralArms — zero-axiom gate (MODE-COMMUTE r27)

Per-declaration zero-axiom gate for the r27 GENERAL disjoint atom-swap arms: the read-shift /
read-stability list lemmas, the splice successor/companion unfoldings, the six block-rotation value
read-offs, the three general full-`ArcStepSimCount` swap arms (cap x cap under the sharp
three-disequality guard, cup-then-cap, cap-then-cup), the three full-sim fires on the r26 concrete
seeds, the shipped marker, and the four untouched-false honesty pins.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.
Registered in `AuditAll` (paired with the independent `#print axioms` witness). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.natListGetAt_consSucc
#assert_no_axioms FX1Poly.Polygraph.natListGetAt_removeTwoAt_shift
#assert_no_axioms FX1Poly.Polygraph.natListGetAt_removeTwoAt_below
#assert_no_axioms FX1Poly.Polygraph.natListInsertAt_succ
#assert_no_axioms FX1Poly.Polygraph.natListGetAt_insertAt_shift
#assert_no_axioms FX1Poly.Polygraph.natListGetAt_insertAt_below
#assert_no_axioms FX1Poly.Polygraph.blockRotate_oneOne_base
#assert_no_axioms FX1Poly.Polygraph.blockRotate_oneOne_succ
#assert_no_axioms FX1Poly.Polygraph.blockRotate_threeOne_cup
#assert_no_axioms FX1Poly.Polygraph.blockRotate_threeOne_cap
#assert_no_axioms FX1Poly.Polygraph.blockRotate_oneThree_cap
#assert_no_axioms FX1Poly.Polygraph.blockRotate_oneThree_cup
#assert_no_axioms FX1Poly.Polygraph.arcDisjointCapCapSwapSimCount_ofWellFormed
#assert_no_axioms FX1Poly.Polygraph.arcDisjointCupCapSwapSimCount_ofWellFormed
#assert_no_axioms FX1Poly.Polygraph.arcDisjointCapCupSwapSimCount_ofWellFormed
#assert_no_axioms FX1Poly.Polygraph.capCapDisjointSwap_fullSimCount
#assert_no_axioms FX1Poly.Polygraph.mixedCupCapSwap_fullSimCount
#assert_no_axioms FX1Poly.Polygraph.mixedCapCupSwap_fullSimCount
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasDisjointAtomSwapGeneralArms
#assert_no_axioms FX1Poly.Polygraph.arcDisjointAtomSwapGeneralArms_disjointWhiskerSupport_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcDisjointAtomSwapGeneralArms_swapRenameableProof2_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcDisjointAtomSwapGeneralArms_partitionCommute_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcDisjointAtomSwapGeneralArms_samePartitionFresh_stays_false

end FX1PolyAudit
