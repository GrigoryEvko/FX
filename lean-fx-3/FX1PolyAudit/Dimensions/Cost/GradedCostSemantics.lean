import FX1PolyAudit.DependencyAudit
import FX1Poly.Dimensions.Cost.GradedCostSemantics

/-! # FX1PolyAudit.Dimensions.Cost.GradedCostSemantics — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Modal.GradedLambda.ReducesInSteps
#assert_no_axioms FX1Poly.Modal.GradedLambda.ReducesInSteps.toStar
#assert_no_axioms FX1Poly.Modal.GradedLambda.ReducesStar.existsStepCount
#assert_no_axioms FX1Poly.Modal.GradedLambda.memMapOfMem
#assert_no_axioms FX1Poly.Modal.GradedLambda.memAppendLeft
#assert_no_axioms FX1Poly.Modal.GradedLambda.memAppendRight
#assert_no_axioms FX1Poly.Modal.GradedLambda.memMapInv
#assert_no_axioms FX1Poly.Modal.GradedLambda.memAppendInv
#assert_no_axioms FX1Poly.Modal.GradedLambda.oneStepReducts
#assert_no_axioms FX1Poly.Modal.GradedLambda.oneStepReducts_complete
#assert_no_axioms FX1Poly.Modal.GradedLambda.oneStepReducts_sound
#assert_no_axioms FX1Poly.Modal.GradedLambda.costBoundOverReducts
#assert_no_axioms FX1Poly.Modal.GradedLambda.costBoundOverReducts_boundsElement
#assert_no_axioms FX1Poly.Modal.GradedLambda.costBound
#assert_no_axioms FX1Poly.Modal.GradedLambda.costBound_isSound
#assert_no_axioms FX1Poly.Modal.GradedLambda.normalizeWithCost
#assert_no_axioms FX1Poly.Modal.GradedLambda.normalizeCost
#assert_no_axioms FX1Poly.Modal.GradedLambda.normalizeCost_isExact
#assert_no_axioms FX1Poly.Modal.GradedLambda.normalizeWithCost_reachesNormalize
#assert_no_axioms FX1Poly.Modal.GradedLambda.normalizeCost_le_costBound
#assert_no_axioms FX1Poly.Modal.GradedLambda.identityRedex_costsOneStep
#assert_no_axioms FX1Poly.Modal.HasGradeOver.costCalculator
#assert_no_axioms FX1Poly.Modal.HasGradeOver.costCalculator_isSound
#assert_no_axioms FX1Poly.Modal.HasGradeOver.canonicalEvaluationCost
#assert_no_axioms FX1Poly.Modal.HasGradeOver.canonicalEvaluationCost_isExact
#assert_no_axioms FX1Poly.Modal.complexityGraded_costIsCalculable

end FX1PolyAudit
