import FX1PolyAudit.DependencyAudit
import FX1Poly.Dimensions.Graded.GradedNormalization

/-! # FX1PolyAudit.Dimensions.Graded.GradedNormalization — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Modal.GradedLambda.lam_isNormalForm
#assert_no_axioms FX1Poly.Modal.GradedLambda.var_app_isNormalForm
#assert_no_axioms FX1Poly.Modal.GradedLambda.app_app_isNormalForm
#assert_no_axioms FX1Poly.Modal.GradedLambda.stepOrNormal
#assert_no_axioms FX1Poly.Modal.GradedLambda.normalizeWithProof
#assert_no_axioms FX1Poly.Modal.GradedLambda.normalize
#assert_no_axioms FX1Poly.Modal.GradedLambda.normalize_reducesStar
#assert_no_axioms FX1Poly.Modal.GradedLambda.normalize_isNormalForm
#assert_no_axioms FX1Poly.Modal.GradedLambda.IsStronglyNormalizing.ofReducesStar
#assert_no_axioms FX1Poly.Modal.GradedLambda.normalize_of_isNormalForm
#assert_no_axioms FX1Poly.Modal.GradedLambda.joinable_iff_normalize_eq
#assert_no_axioms FX1Poly.Modal.GradedLambda.decidableJoinable
#assert_no_axioms FX1Poly.Modal.HasSimpleType.decidableConv
#assert_no_axioms FX1Poly.Modal.GradedLambda.var_notJoinable_of_ne
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reduces.joinable_refl
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reduces.joinable_symm
#assert_no_axioms FX1Poly.Modal.GradedLambda.ReducesStar.joinable
#assert_no_axioms FX1Poly.Modal.GradedLambda.IsStronglyNormalizing.joinable_trans
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reduces.beta_joinable
#assert_no_axioms FX1Poly.Modal.HasSimpleType.joinable_trans

end FX1PolyAudit
