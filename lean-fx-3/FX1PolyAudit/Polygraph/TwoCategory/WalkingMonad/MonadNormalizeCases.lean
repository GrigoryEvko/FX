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
-- The `id`-cell case + its supporting ones-word collapse and boundary-cast algebra (all zero-axiom).
#assert_no_axioms FX1Poly.Polygraph.monadOnes
#assert_no_axioms FX1Poly.Polygraph.length_monadOnes
#assert_no_axioms FX1Poly.Polygraph.countsDomainPath_monadOnes
#assert_no_axioms FX1Poly.Polygraph.runLengthAt_ascendingFrom_succ
#assert_no_axioms FX1Poly.Polygraph.dropRunAt_ascendingFrom_succ
#assert_no_axioms FX1Poly.Polygraph.countsOf_ascendingFrom_ones
#assert_no_axioms FX1Poly.Polygraph.MonadSaturatedTwoCellConv.castBoundaryCongr
#assert_no_axioms FX1Poly.Polygraph.monadWhiskerLeft_castBoundary
#assert_no_axioms FX1Poly.Polygraph.monadCastBoundary_castBoundary
#assert_no_axioms FX1Poly.Polygraph.monadCastBoundary_id
#assert_no_axioms FX1Poly.Polygraph.wordFromCounts_monadOnes_succ_conv
#assert_no_axioms FX1Poly.Polygraph.wordFromCounts_monadOnes_conv
#assert_no_axioms FX1Poly.Polygraph.monadNormalize_id
#assert_no_axioms FX1Poly.Polygraph.fxMonad_hasNormalizeIdCase
#assert_no_axioms FX1Poly.Polygraph.fxMonad_hasNormalizeIdWhiskerVcompCases

end FX1PolyAudit
