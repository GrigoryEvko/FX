import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineBoundaryChain

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/SpineBoundaryChain — zero-axiom gate

Per-declaration zero-axiom gate for the spine boundary-chain discipline: the atom boundary
widths, the chain predicate's cons inversion, boundary-silence of generator-free cells, the
production / inversion / pinning lemmas for spine difference-lists, the initial-state seed, and
the honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.SpineAtom.domBoundaryLength
#assert_no_axioms FX1Poly.Polygraph.SpineAtom.codBoundaryLength
#assert_no_axioms FX1Poly.Polygraph.spineBoundaryChained_tail
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.sourcePath_eq_targetPath_of_generatorCount_zero
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.spineDiff_eq_rest_of_generatorCount_zero
#assert_no_axioms FX1Poly.Polygraph.spineBoundaryChained_spineDiff
#assert_no_axioms FX1Poly.Polygraph.spineBoundaryChained_rest_of_spineDiff
#assert_no_axioms FX1Poly.Polygraph.spineBoundaryChained_pinsBoundary_of_generatorCount_ne_zero
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.spineBoundaryChained_spine
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSpineBoundaryChainSubstrate

end FX1PolyAudit
