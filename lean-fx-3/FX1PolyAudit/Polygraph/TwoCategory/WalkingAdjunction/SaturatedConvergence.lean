import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedConvergence

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.SaturatedConvergence — zero-axiom gate

Per-declaration zero-axiom gate for the COMBINED both-triangle saturated rewrite: the relation, its soundness
into `SaturatedTwoCellConv`, the unconditional strong normalization, the generator-count monovariant + count-
preserving-is-structural characterization, the Newman confluence reduction, and the four triangle-layer
`vcompAssoc` critical-pair joins.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.natAddLeftCancel
#assert_no_axioms FX1Poly.Polygraph.SaturatedTwoCellStep
#assert_no_axioms FX1Poly.Polygraph.SaturatedTwoCellStep.toSaturatedConv
#assert_no_axioms FX1Poly.Polygraph.saturatedTwoCellReduces_toSaturatedConv
#assert_no_axioms FX1Poly.Polygraph.SaturatedTwoCellStep.generatorCount_le
#assert_no_axioms FX1Poly.Polygraph.SaturatedTwoCellStep.generatorCountPreserving_isStructural
#assert_no_axioms FX1Poly.Polygraph.saturatedTwoCellStep_isStronglyNormalizing
#assert_no_axioms FX1Poly.Polygraph.SaturatedTwoCellLocallyConfluent
#assert_no_axioms FX1Poly.Polygraph.saturatedTwoCellStep_isConfluent
#assert_no_axioms FX1Poly.Polygraph.saturatedLeftBareSnakeAssocCriticalPair_joins
#assert_no_axioms FX1Poly.Polygraph.saturatedRightBareSnakeAssocCriticalPair_joins
#assert_no_axioms FX1Poly.Polygraph.saturatedLeftPrefixAssocCriticalPair_joins
#assert_no_axioms FX1Poly.Polygraph.saturatedRightPrefixAssocCriticalPair_joins
#assert_no_axioms FX1Poly.Polygraph.saturatedLeftBareSnakeAssocPeak_diverges
#assert_no_axioms FX1Poly.Polygraph.saturatedRightBareSnakeAssocPeak_diverges
#assert_no_axioms FX1Poly.Polygraph.saturatedLeftPrefixAssocPeak_diverges
#assert_no_axioms FX1Poly.Polygraph.saturatedRightPrefixAssocPeak_diverges
#assert_no_axioms FX1Poly.Polygraph.saturatedLeftSnakeUnderWhisker_step
#assert_no_axioms FX1Poly.Polygraph.saturatedLeftSnakeUnderWhisker_conv
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasCombinedSaturatedTriangleRewrite
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSaturatedTwoCellConfluence

end FX1PolyAudit
