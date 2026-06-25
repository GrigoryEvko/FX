import FX1PolyAudit.DependencyAudit
import FX1Poly.Dimensions.Security.UsageDiscipline

/-! # FX1PolyAudit.Dimensions.Security.UsageDiscipline — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Modal.GradedLambda.usage
#assert_no_axioms FX1Poly.Modal.GradedLambda.WellGraded
#assert_no_axioms FX1Poly.Modal.atkeyClosure
#assert_no_axioms FX1Poly.Modal.linearClosure
#assert_no_axioms FX1Poly.Modal.linearContext
#assert_no_axioms FX1Poly.Modal.atkey_usage
#assert_no_axioms FX1Poly.Modal.linear_usage
#assert_no_axioms FX1Poly.Modal.atkey_rejected
#assert_no_axioms FX1Poly.Modal.linear_accepted
#assert_no_axioms FX1Poly.Modal.GradedLambda.wellGradedCheck
#assert_no_axioms FX1Poly.Modal.GradedLambda.wellGradedCheck_correct
#assert_no_axioms FX1Poly.Modal.atkey_check_false
#assert_no_axioms FX1Poly.Modal.linear_check_true
#assert_no_axioms FX1Poly.Modal.GradedLambda.BetaStep
#assert_no_axioms FX1Poly.Modal.dupRedex
#assert_no_axioms FX1Poly.Modal.dupReduct
#assert_no_axioms FX1Poly.Modal.linearG
#assert_no_axioms FX1Poly.Modal.dupRedex_beta
#assert_no_axioms FX1Poly.Modal.dupRedex_wellGraded
#assert_no_axioms FX1Poly.Modal.dupReduct_illGraded
#assert_no_axioms FX1Poly.Modal.usage_check_fails_subject_reduction

end FX1PolyAudit
