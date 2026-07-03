import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedDecision

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingAdjunction.SaturatedDecision — zero-axiom gate (the saturated adjunction decision)

Per-declaration zero-axiom gate for the SATURATED walking-adjunction 2-cell convertibility: the relation, its
embeddings, the two triangle witnesses, the bubble-collapse crux (saturated-but-not-free), the derived
snake-prefix completions, the KB-rewrite soundness bridge, the "generator count is dead" finding, and the
Schanuel–Street monotone-map decision-modulo-canonicalization assembly.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.SaturatedTwoCellConv
#assert_no_axioms FX1Poly.Polygraph.SaturatedTwoCellConv.ofConv
#assert_no_axioms FX1Poly.Polygraph.triangleLeftHolds
#assert_no_axioms FX1Poly.Polygraph.triangleRightHolds
#assert_no_axioms FX1Poly.Polygraph.saturatedCollapsesLeftBubble
#assert_no_axioms FX1Poly.Polygraph.saturatedCollapsesRightBubble
#assert_no_axioms FX1Poly.Polygraph.leftSnakeSaturatedButNotFree
#assert_no_axioms FX1Poly.Polygraph.rightSnakeSaturatedButNotFree
#assert_no_axioms FX1Poly.Polygraph.leftSnakeWhiskeredCollapses
#assert_no_axioms FX1Poly.Polygraph.leftDoubleBubbleCollapses
#assert_no_axioms FX1Poly.Polygraph.leftSnakePrefixHolds
#assert_no_axioms FX1Poly.Polygraph.rightSnakePrefixHolds
#assert_no_axioms FX1Poly.Polygraph.AdjunctionLeftSaturatedStep.toSaturatedConv
#assert_no_axioms FX1Poly.Polygraph.AdjunctionLeftSaturatedReduces.toSaturatedConv
#assert_no_axioms FX1Poly.Polygraph.AdjunctionRightSaturatedStep.toSaturatedConv
#assert_no_axioms FX1Poly.Polygraph.AdjunctionRightSaturatedReduces.toSaturatedConv
#assert_no_axioms FX1Poly.Polygraph.saturatedConv_doesNotPreserveGeneratorCount
#assert_no_axioms FX1Poly.Polygraph.AdjunctionSaturatedCanonicalization
#assert_no_axioms FX1Poly.Polygraph.adjunctionDecideSaturatedConvViaMonotoneMap
#assert_no_axioms FX1Poly.Polygraph.adjunctionSaturatedWordProblemModuloCanonicalization
#assert_no_axioms FX1Poly.Polygraph.adjunctionDecideSaturated_leftSnake_isTrue
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSaturatedTwoCellConvRelation
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasSaturatedTwoCellMonotoneMapDecision

end FX1PolyAudit
