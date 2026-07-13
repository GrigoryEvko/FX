import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcCellPastCellSwapSimCount

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcCellPastCellSwapSimCount — zero-axiom gate (MODE-COMMUTE r28)

Per-declaration zero-axiom gate for the r28 `cellPastCell` brick: the disjointness symmetry
helper, the two-window invariant, the whole-cell double-induction master theorem, the two
multi-cell fires, the shipped marker, and the four untouched-false pins.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.
Registered in `AuditAll` (paired with the independent `#print axioms` witness). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.isSameComponentFalse_symm
#assert_no_axioms FX1Poly.Polygraph.arcWindowsComponentDisjoint
#assert_no_axioms FX1Poly.Polygraph.arcCellPastCellSwapSimCount
#assert_no_axioms FX1Poly.Polygraph.arcThreeAtomCellPastThreeAtomCell_fired
#assert_no_axioms FX1Poly.Polygraph.arcCellPastCellCapFireSeed
#assert_no_axioms FX1Poly.Polygraph.arcCellPastCellCapFireSeed_isWellFormed
#assert_no_axioms FX1Poly.Polygraph.arcCounitCellPastThreeAtomCell_fired
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCellPastCellSwapSimCount
#assert_no_axioms FX1Poly.Polygraph.arcCellPastCell_disjointWhiskerSupport_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcCellPastCell_swapRenameableProof2_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcCellPastCell_partitionCommute_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcCellPastCell_samePartitionFresh_stays_false

end FX1PolyAudit
