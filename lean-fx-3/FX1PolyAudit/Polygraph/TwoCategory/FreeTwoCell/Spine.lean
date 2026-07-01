import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.Spine

/-! # FX1PolyAudit.Tier0.Mode.FreeTwoCellSpine — zero-axiom gate (mode-3 floor)

Per-declaration zero-axiom gate for the free 2-cell spine: the cons-only difference-list flattening, its
invariance under the structural rewrite, and its length = generator count.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Tier0.RawTwoCellExpr.spineDiff
#assert_no_axioms FX1Poly.Tier0.RawTwoCellExpr.spine
#assert_no_axioms FX1Poly.Tier0.TwoCellStepInterchangeFree.spineDiff_eq
#assert_no_axioms FX1Poly.Tier0.TwoCellStepInterchangeFree.spine_eq
#assert_no_axioms FX1Poly.Tier0.RawTwoCellExpr.spineDiff_length
#assert_no_axioms FX1Poly.Tier0.RawTwoCellExpr.spine_length

end FX1PolyAudit
