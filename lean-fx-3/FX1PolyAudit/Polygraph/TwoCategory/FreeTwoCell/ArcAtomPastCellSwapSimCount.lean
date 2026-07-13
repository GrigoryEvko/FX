import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcAtomPastCellSwapSimCount

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcAtomPastCellSwapSimCount — zero-axiom gate (MODE-COMMUTE r28)

Per-declaration zero-axiom gate for the r28 `atomPastCell` brick: the bounded swap carrier and
its algebra (identity / weaken / comp / block rotation / common-suffix extension), the
read-membership brick, the two `atomPastCell` master theorems (cap guarded, cup unguarded), the
three-atom-cell fires from two seeds, the shipped marker, and the four untouched-false pins.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.
Registered in `AuditAll` (paired with the independent `#print axioms` witness). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.ArcBoundedSwapCarrier
#assert_no_axioms FX1Poly.Polygraph.arcBoundedSwapCarrier_identity
#assert_no_axioms FX1Poly.Polygraph.arcBoundedSwapCarrier_weaken
#assert_no_axioms FX1Poly.Polygraph.arcBoundedSwapCarrier_comp
#assert_no_axioms FX1Poly.Polygraph.arcBoundedSwapCarrier_blockRotate
#assert_no_axioms FX1Poly.Polygraph.arcStepSimCount_extendByCommonCell
#assert_no_axioms FX1Poly.Polygraph.natListGetAt_memOfBelow
#assert_no_axioms FX1Poly.Polygraph.arcCapAtomPastCellSwapSimCount
#assert_no_axioms FX1Poly.Polygraph.arcCupAtomPastCellSwapSimCount
#assert_no_axioms FX1Poly.Polygraph.arcAtomPastCellFireSeed
#assert_no_axioms FX1Poly.Polygraph.arcAtomPastCellFireSeed_isWellFormed
#assert_no_axioms FX1Poly.Polygraph.arcCapAtomPastThreeAtomCell_fired
#assert_no_axioms FX1Poly.Polygraph.arcCupPastCellFireSeed
#assert_no_axioms FX1Poly.Polygraph.arcCupPastCellFireSeed_isWellFormed
#assert_no_axioms FX1Poly.Polygraph.arcCupAtomPastThreeAtomCell_fired
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcAtomPastCellSwapSimCount
#assert_no_axioms FX1Poly.Polygraph.arcAtomPastCell_disjointWhiskerSupport_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcAtomPastCell_swapRenameableProof2_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcAtomPastCell_partitionCommute_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcAtomPastCell_samePartitionFresh_stays_false

end FX1PolyAudit
