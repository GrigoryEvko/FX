import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadNormalizeCases

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingMonad.MonadNormalizeCases — zero-axiom gate (normalize base cases)

Per-declaration zero-axiom gate for the two GENERATOR base cases of the cell-level normalization `normalize :
MonadNormalizesToCanon`: `gen eta ≈ canon (gen eta)` and `gen mu ≈ canon (gen mu)`, each convertible to the
canonical Eilenberg–Zilber word of its own fold by the completed free-strict-2-category laws (no monad law), plus
the two honesty markers.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.monadNormalize_genEta
#assert_no_axioms FX1Poly.Polygraph.monadNormalize_genMu
#assert_no_axioms FX1Poly.Polygraph.fxMonad_hasNormalizeGeneratorBaseCases
#assert_no_axioms FX1Poly.Polygraph.fxMonad_hasNormalizeIdWhiskerVcompCases

end FX1PolyAudit
