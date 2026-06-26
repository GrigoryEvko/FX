import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Mode.AdjunctionTriangleObstruction

/-! # FX1PolyAudit.Tier0.Mode.AdjunctionTriangleObstruction — zero-axiom gate (the fib-3 dim-2 obstruction)

Per-declaration zero-axiom gate for the rigorous adjunction-triangle obstruction: the two snakes, their generator
counts, the identity count, the two non-convertibility obstruction theorems, the termination-direction fact, and
the confluence-direction structural-normality of the snakes (the triangle is their sole redex).
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Tier0.adjunctionSeedLeftSnake
#assert_no_axioms FX1Poly.Tier0.adjunctionSeedRightSnake
#assert_no_axioms FX1Poly.Tier0.adjunctionSeedLeftSnake_generatorCount
#assert_no_axioms FX1Poly.Tier0.adjunctionSeedRightSnake_generatorCount
#assert_no_axioms FX1Poly.Tier0.leftIdentityCell_generatorCount
#assert_no_axioms FX1Poly.Tier0.adjunctionSeedLeftSnake_not_conv_id
#assert_no_axioms FX1Poly.Tier0.adjunctionSeedRightSnake_not_conv_id
#assert_no_axioms FX1Poly.Tier0.adjunctionSeedLeftSnake_classGeneratorCount
#assert_no_axioms FX1Poly.Tier0.adjunctionSeedRightSnake_classGeneratorCount
#assert_no_axioms FX1Poly.Tier0.adjunctionSeedTriangleReductionDecreasesCount
#assert_no_axioms FX1Poly.Tier0.adjunctionSeedLeftSnake_isInterchangeNormal
#assert_no_axioms FX1Poly.Tier0.adjunctionSeedRightSnake_isInterchangeNormal
#assert_no_axioms FX1Poly.Tier0.adjunctionSeedLeftSnake_no_structuralStep
#assert_no_axioms FX1Poly.Tier0.adjunctionSeedRightSnake_no_structuralStep
#assert_no_axioms FX1Poly.Tier0.AdjunctionLeftSaturatedStep
#assert_no_axioms FX1Poly.Tier0.AdjunctionLeftSaturatedReduces
#assert_no_axioms FX1Poly.Tier0.adjunctionSeedLeftSnake_vcompContinuation_reducesToContinuation
#assert_no_axioms FX1Poly.Tier0.adjunctionSeedLeftSnake_assocCriticalPair_joins

end FX1PolyAudit
