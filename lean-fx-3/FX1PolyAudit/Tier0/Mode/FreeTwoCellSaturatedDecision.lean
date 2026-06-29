import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.FreeTwoCellSaturatedDecision

/-! # FX1PolyAudit.Tier0.Mode.FreeTwoCellSaturatedDecision — zero-axiom gate (the saturated adjunction decision)

Per-declaration zero-axiom gate for the SATURATED walking-adjunction 2-cell convertibility: the relation, its
embeddings, the two triangle witnesses, the bubble-collapse crux (saturated-but-not-free), the derived
snake-prefix completions, the KB-rewrite soundness bridge, the "generator count is dead" finding, and the
Schanuel–Street monotone-map decision-modulo-canonicalization assembly.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Tier0.SaturatedTwoCellConv
#assert_no_axioms FX1Poly.Tier0.SaturatedTwoCellConv.ofConv
#assert_no_axioms FX1Poly.Tier0.triangleLeftHolds
#assert_no_axioms FX1Poly.Tier0.triangleRightHolds
#assert_no_axioms FX1Poly.Tier0.saturatedCollapsesLeftBubble
#assert_no_axioms FX1Poly.Tier0.saturatedCollapsesRightBubble
#assert_no_axioms FX1Poly.Tier0.leftSnakeSaturatedButNotFree
#assert_no_axioms FX1Poly.Tier0.rightSnakeSaturatedButNotFree
#assert_no_axioms FX1Poly.Tier0.leftSnakeWhiskeredCollapses
#assert_no_axioms FX1Poly.Tier0.leftDoubleBubbleCollapses
#assert_no_axioms FX1Poly.Tier0.leftSnakePrefixHolds
#assert_no_axioms FX1Poly.Tier0.rightSnakePrefixHolds
#assert_no_axioms FX1Poly.Tier0.AdjunctionLeftSaturatedStep.toSaturatedConv
#assert_no_axioms FX1Poly.Tier0.AdjunctionLeftSaturatedReduces.toSaturatedConv
#assert_no_axioms FX1Poly.Tier0.AdjunctionRightSaturatedStep.toSaturatedConv
#assert_no_axioms FX1Poly.Tier0.AdjunctionRightSaturatedReduces.toSaturatedConv
#assert_no_axioms FX1Poly.Tier0.saturatedConv_doesNotPreserveGeneratorCount
#assert_no_axioms FX1Poly.Tier0.AdjunctionSaturatedCanonicalization
#assert_no_axioms FX1Poly.Tier0.adjunctionDecideSaturatedConvViaMonotoneMap
#assert_no_axioms FX1Poly.Tier0.adjunctionSaturatedWordProblemModuloCanonicalization
#assert_no_axioms FX1Poly.Tier0.adjunctionDecideSaturated_leftSnake_isTrue
#assert_no_axioms FX1Poly.Tier0.fxMode_hasSaturatedTwoCellConvRelation
#assert_no_axioms FX1Poly.Tier0.fxMode_hasSaturatedTwoCellMonotoneMapDecision

end FX1PolyAudit
