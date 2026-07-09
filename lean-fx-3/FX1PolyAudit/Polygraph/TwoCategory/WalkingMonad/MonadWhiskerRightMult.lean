import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadWhiskerRightMult

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingMonad.MonadWhiskerRightMult — zero-axiom gate (RIGHT-whisker word multiplicativity)

Per-declaration zero-axiom gate for the RIGHT-whisker word multiplicativity (the r11 named blocker, closed): the
signature-generic boundary-cast merge / extrusion lemmas, the `whiskerRight_hcomp` distributivity, and
`wordMul_whiskerRight : t^k ▷ (canonical word) ≈ (canonical word of the ones-appended counts)`.  Must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.vcomp_castBoundary_merge
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.vcomp_castBoundaryRight
#assert_no_axioms FX1Poly.Polygraph.RawTwoCellExpr.hcomp_castBoundaryRight
#assert_no_axioms FX1Poly.Polygraph.whiskerRight_hcomp
#assert_no_axioms FX1Poly.Polygraph.wordMul_whiskerRight
#assert_no_axioms FX1Poly.Polygraph.fxMonad_hasWordMulWhiskerRight

end FX1PolyAudit
