import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ExprDecidableEq

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ExprDecidableEq — zero-axiom gate (mode-3 floor)

Per-declaration zero-axiom gate for decidable syntactic equality of free 2-cell expressions: the path-monoid
cancellation lemmas, the per-head packed extractors and reconstruction views, and the headline
`RawTwoCellExpr.decEq` / `decidableEq`.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- ★ Path-monoid cancellation
#assert_no_axioms FX1Poly.Polygraph.composePathLeftCancel
#assert_no_axioms FX1Poly.Polygraph.natAddRightCancel
#assert_no_axioms FX1Poly.Polygraph.lengthComposePath
#assert_no_axioms FX1Poly.Polygraph.rightFactorNeConsExtension
#assert_no_axioms FX1Poly.Polygraph.composePathRightCancel

-- ★ Identity-head extraction
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.eq_id_of_isIdentityCell

-- ★ Packed head extractors (cast-free, for the negative directions)
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.genPacked
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.vcompMiddlePacked
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.whiskerLeftPackedOneCell
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.whiskerRightPackedOneCell

-- ★ The single-recursion reconstruction views
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.asGen
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.asVcomp
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.asWhiskerLeft
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.asWhiskerRight

-- ★ Decidable equality of free 2-cell expressions
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.decEq
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.decidableEq

end FX1PolyAudit
