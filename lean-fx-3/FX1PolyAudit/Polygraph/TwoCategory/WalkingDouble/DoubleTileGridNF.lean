import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingDouble.DoubleTileGridNF

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingDouble.DoubleTileGridNF — zero-axiom gate (the unit-free grid DECISION)

Per-declaration zero-axiom gate for WP-DOUBLE brick 2 — the unit-free grid normal-form decision of the
walking-square double category: the `IsUnitFreeGrid` well-formedness predicate, the canonical row / grid /
direct-count grid, the shape smokes, the positivity lemmas, the three merges (`hRowMerge`, the interchange star
`hMerge`, `vMerge`) and their direct-count bridges, the reconstruction `conv_toGridNF`, COMPLETENESS
`doubleTileConv_of_sameShape_of_wf`, the total decider `decideDoubleTileConv`, the well-formedness witnesses, the
non-vacuity / decider smokes, and the markers.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.IsUnitFreeGrid
#assert_no_axioms FX1Poly.Polygraph.hRow
#assert_no_axioms FX1Poly.Polygraph.gridNF
#assert_no_axioms FX1Poly.Polygraph.canonicalGrid
#assert_no_axioms FX1Poly.Polygraph.tileWidth_hRow
#assert_no_axioms FX1Poly.Polygraph.tileHeight_hRow
#assert_no_axioms FX1Poly.Polygraph.tileWidth_gridNF
#assert_no_axioms FX1Poly.Polygraph.tileHeight_gridNF
#assert_no_axioms FX1Poly.Polygraph.isUnitFreeGrid_width_succ
#assert_no_axioms FX1Poly.Polygraph.isUnitFreeGrid_height_succ
#assert_no_axioms FX1Poly.Polygraph.hRowMerge
#assert_no_axioms FX1Poly.Polygraph.hMerge
#assert_no_axioms FX1Poly.Polygraph.vMerge
#assert_no_axioms FX1Poly.Polygraph.canonicalHMerge
#assert_no_axioms FX1Poly.Polygraph.canonicalVMerge
#assert_no_axioms FX1Poly.Polygraph.conv_toGridNF
#assert_no_axioms FX1Poly.Polygraph.doubleTileConv_of_sameShape_of_wf
#assert_no_axioms FX1Poly.Polygraph.decideDoubleTileConv
#assert_no_axioms FX1Poly.Polygraph.wfSquare
#assert_no_axioms FX1Poly.Polygraph.wfHcompSquareSquare
#assert_no_axioms FX1Poly.Polygraph.wfVcompSquareSquare
#assert_no_axioms FX1Poly.Polygraph.wfGridInterchangeLeft
#assert_no_axioms FX1Poly.Polygraph.wfGridInterchangeRight
#assert_no_axioms FX1Poly.Polygraph.doubleConv_gridInterchange_viaCompleteness
#assert_no_axioms FX1Poly.Polygraph.conv_hcompSquareSquare_toGrid
#assert_no_axioms FX1Poly.Polygraph.doubleDecide_true_on_gridInterchange
#assert_no_axioms FX1Poly.Polygraph.doubleDecide_false_on_hcomp_vcomp
#assert_no_axioms FX1Poly.Polygraph.doubleDecide_false_on_square_hcomp
#assert_no_axioms FX1Poly.Polygraph.fxDouble_hasUnitFreeGridDecision
#assert_no_axioms FX1Poly.Polygraph.fxDouble_hasUnitBearingGridDecided

/-! ## Independent `#print axioms` on the headline decl(s) — should report "does not depend on any axioms". -/

#print axioms FX1Poly.Polygraph.decideDoubleTileConv
#print axioms FX1Poly.Polygraph.doubleTileConv_of_sameShape_of_wf
#print axioms FX1Poly.Polygraph.conv_toGridNF
#print axioms FX1Poly.Polygraph.hMerge

end FX1PolyAudit
