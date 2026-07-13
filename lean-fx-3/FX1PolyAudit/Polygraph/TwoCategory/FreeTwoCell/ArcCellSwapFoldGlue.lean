import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcCellSwapFoldGlue

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcCellSwapFoldGlue — zero-axiom gate (MODE-COMMUTE r27)

Per-declaration zero-axiom gate for the r27 whole-cell fold glue: the map-composition helper, the
simulation reflexivity/composition algebra, the four `runArcCell` cell-shape decomposition
equations, the shipped marker, and the four untouched-false honesty pins.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.
Registered in `AuditAll` (paired with the independent `#print axioms` witness). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.mapComposition
#assert_no_axioms FX1Poly.Polygraph.arcStepSimCount_refl
#assert_no_axioms FX1Poly.Polygraph.arcStepSimCount_comp
#assert_no_axioms FX1Poly.Polygraph.runArcCell_vcomp
#assert_no_axioms FX1Poly.Polygraph.runArcCell_whiskerLeft
#assert_no_axioms FX1Poly.Polygraph.runArcCell_whiskerRight
#assert_no_axioms FX1Poly.Polygraph.runArcCell_gen
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCellSwapFoldGlue
#assert_no_axioms FX1Poly.Polygraph.arcCellSwapFoldGlue_disjointWhiskerSupport_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcCellSwapFoldGlue_swapRenameableProof2_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcCellSwapFoldGlue_partitionCommute_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcCellSwapFoldGlue_samePartitionFresh_stays_false

end FX1PolyAudit
