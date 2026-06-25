import FX1PolyAudit.DependencyAudit
import FX1Poly.Dimensions.Cost.GradedLinearTime

/-! # FX1PolyAudit.Dimensions.Cost.GradedLinearTime — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Modal.GradeVectorOver.lookupGrade
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.lookupGrade_zero
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.lookupGrade_single_self
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.lookupGrade_single_other
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.lookupGrade_add_usage
#assert_no_axioms FX1Poly.Modal.UsageGrade.one_mul_eq
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.lookupGrade_scale_one
#assert_no_axioms FX1Poly.Modal.UsageGrade.boundsCount
#assert_no_axioms FX1Poly.Modal.UsageGrade.boundsCount_add
#assert_no_axioms FX1Poly.Modal.HasStrictLinearGrade
#assert_no_axioms FX1Poly.Modal.HasStrictLinearGrade.toGraded
#assert_no_axioms FX1Poly.Modal.HasStrictLinearGrade.countBound
#assert_no_axioms FX1Poly.Modal.HasStrictLinearGrade.lamBodyCountBound
#assert_no_axioms FX1Poly.Modal.HasStrictLinearGrade.betaShrinks
#assert_no_axioms FX1Poly.Modal.linearIdentity_strictlyLinear
#assert_no_axioms FX1Poly.Modal.identityApplication_strictlyShrinks
#assert_no_axioms FX1Poly.Modal.affineDuplicatorBody
#assert_no_axioms FX1Poly.Modal.zeroScalingFunctionType
#assert_no_axioms FX1Poly.Modal.affineDuplicatorLam_typedAtGradeZero
#assert_no_axioms FX1Poly.Modal.affineDuplicatorBody_countsTwice
#assert_no_axioms FX1Poly.Modal.affineGradeZero_doesNotBoundCount

end FX1PolyAudit
