import FX1PolyAudit.DependencyAudit
import FX1Poly.Dimensions.Graded.GradedReductionConfluence

/-! # FX1PolyAudit.Dimensions.Graded.GradedReductionConfluence — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Modal.GradedLambda.renameTerm_eq_applySubstitution_var
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reduces.renameTerm
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reduces.shift
#assert_no_axioms FX1Poly.Modal.GradedLambda.ReducesStar.congLam
#assert_no_axioms FX1Poly.Modal.GradedLambda.ReducesStar.congAppLeft
#assert_no_axioms FX1Poly.Modal.GradedLambda.ReducesStar.congAppRight
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reduces.substReducedArg
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reduces.localConfluent
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reduces.weaklyConfluent
#assert_no_axioms FX1Poly.Modal.GradedLambda.IsStronglyNormalizing.confluent
#assert_no_axioms FX1Poly.Modal.HasSimpleType.confluent
#assert_no_axioms FX1Poly.Modal.GradedLambda.IsNormalForm
#assert_no_axioms FX1Poly.Modal.GradedLambda.var_isNormalForm
#assert_no_axioms FX1Poly.Modal.GradedLambda.IsNormalForm.eq_of_reducesStar
#assert_no_axioms FX1Poly.Modal.GradedLambda.IsStronglyNormalizing.uniqueNormalForm
#assert_no_axioms FX1Poly.Modal.HasSimpleType.uniqueNormalForm

end FX1PolyAudit
