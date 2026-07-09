import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadWhiskerNormalizeCases

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingMonad.MonadWhiskerNormalizeCases — zero-axiom gate (whisker normalizeCell cases)

Per-declaration zero-axiom gate for the two WHISKER `normalizeCell` cases (`whiskerLeft/Right W body ≈ canon`): the
whisker 1-cell transports, the double-cast collapse, and the two headline normalization cases.  Must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.whiskerLeft_pathCongr
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.whiskerRight_pathCongr
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.castBoundary_double_collapse
#assert_no_axioms FX1Poly.Polygraph.monadNormalize_whiskerLeft
#assert_no_axioms FX1Poly.Polygraph.monadNormalize_whiskerRight
#assert_no_axioms FX1Poly.Polygraph.fxMonad_hasWhiskerNormalizeCases

end FX1PolyAudit
