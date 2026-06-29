import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.FreeTwoCellExprDecidableEq

/-! # FX1PolyAudit.Tier0.Mode.FreeTwoCellExprDecidableEq — zero-axiom gate (mode-3 floor)

Per-declaration zero-axiom gate for decidable syntactic equality of free 2-cell expressions: the path-monoid
cancellation lemmas, the per-head packed extractors and reconstruction views, and the headline
`RawTwoCellExpr.decEq` / `decidableEq`.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- ★ Path-monoid cancellation
#assert_no_axioms FX1Poly.Tier0.composePathLeftCancel
#assert_no_axioms FX1Poly.Tier0.natAddRightCancel
#assert_no_axioms FX1Poly.Tier0.lengthComposePath
#assert_no_axioms FX1Poly.Tier0.rightFactorNeConsExtension
#assert_no_axioms FX1Poly.Tier0.composePathRightCancel

-- ★ Identity-head extraction
#assert_no_axioms FX1Poly.Tier0.RawTwoCellExpr.eq_id_of_isIdentityCell

-- ★ Packed head extractors (cast-free, for the negative directions)
#assert_no_axioms FX1Poly.Tier0.RawTwoCellExpr.genPacked
#assert_no_axioms FX1Poly.Tier0.RawTwoCellExpr.vcompMiddlePacked
#assert_no_axioms FX1Poly.Tier0.RawTwoCellExpr.whiskerLeftPackedOneCell
#assert_no_axioms FX1Poly.Tier0.RawTwoCellExpr.whiskerRightPackedOneCell

-- ★ The single-recursion reconstruction views
#assert_no_axioms FX1Poly.Tier0.RawTwoCellExpr.asGen
#assert_no_axioms FX1Poly.Tier0.RawTwoCellExpr.asVcomp
#assert_no_axioms FX1Poly.Tier0.RawTwoCellExpr.asWhiskerLeft
#assert_no_axioms FX1Poly.Tier0.RawTwoCellExpr.asWhiskerRight

-- ★ Decidable equality of free 2-cell expressions
#assert_no_axioms FX1Poly.Tier0.RawTwoCellExpr.decEq
#assert_no_axioms FX1Poly.Tier0.RawTwoCellExpr.decidableEq

end FX1PolyAudit
