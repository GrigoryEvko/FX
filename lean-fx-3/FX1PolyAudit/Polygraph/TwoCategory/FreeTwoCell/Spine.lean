import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.Spine

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.Spine — zero-axiom gate (mode-3 floor)

Per-declaration zero-axiom gate for the free 2-cell spine: the cons-only difference-list flattening, its
invariance under the structural rewrite, and its length = generator count.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.spineDiff
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.spine
#assert_no_axioms FX1Poly.Polygraph.TwoCellStepInterchangeFree.spineDiff_eq
#assert_no_axioms FX1Poly.Polygraph.TwoCellStepInterchangeFree.spine_eq
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.spineDiff_length
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.spine_length

end FX1PolyAudit
