import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedConvergence

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.SaturatedConvergence — zero-axiom gate

Per-declaration zero-axiom gate for the COMBINED both-triangle saturated rewrite: the relation, its soundness
into `SaturatedTwoCellConv`, the unconditional strong normalization, the generator-count monovariant + count-
preserving-is-structural characterization, the Newman confluence reduction, and the four triangle-layer
`vcompAssoc` critical-pair joins.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Tier0.natAddLeftCancel
#assert_no_axioms FX1Poly.Tier0.SaturatedTwoCellStep
#assert_no_axioms FX1Poly.Tier0.SaturatedTwoCellStep.toSaturatedConv
#assert_no_axioms FX1Poly.Tier0.saturatedTwoCellReduces_toSaturatedConv
#assert_no_axioms FX1Poly.Tier0.SaturatedTwoCellStep.generatorCount_le
#assert_no_axioms FX1Poly.Tier0.SaturatedTwoCellStep.generatorCountPreserving_isStructural
#assert_no_axioms FX1Poly.Tier0.saturatedTwoCellStep_isStronglyNormalizing
#assert_no_axioms FX1Poly.Tier0.SaturatedTwoCellLocallyConfluent
#assert_no_axioms FX1Poly.Tier0.saturatedTwoCellStep_isConfluent
#assert_no_axioms FX1Poly.Tier0.saturatedLeftBareSnakeAssocCriticalPair_joins
#assert_no_axioms FX1Poly.Tier0.saturatedRightBareSnakeAssocCriticalPair_joins
#assert_no_axioms FX1Poly.Tier0.saturatedLeftPrefixAssocCriticalPair_joins
#assert_no_axioms FX1Poly.Tier0.saturatedRightPrefixAssocCriticalPair_joins
#assert_no_axioms FX1Poly.Tier0.saturatedLeftBareSnakeAssocPeak_diverges
#assert_no_axioms FX1Poly.Tier0.saturatedRightBareSnakeAssocPeak_diverges
#assert_no_axioms FX1Poly.Tier0.saturatedLeftPrefixAssocPeak_diverges
#assert_no_axioms FX1Poly.Tier0.saturatedRightPrefixAssocPeak_diverges
#assert_no_axioms FX1Poly.Tier0.saturatedLeftSnakeUnderWhisker_step
#assert_no_axioms FX1Poly.Tier0.saturatedLeftSnakeUnderWhisker_conv
#assert_no_axioms FX1Poly.Tier0.fxMode_hasCombinedSaturatedTriangleRewrite
#assert_no_axioms FX1Poly.Tier0.fxMode_hasSaturatedTwoCellConfluence

end FX1PolyAudit
