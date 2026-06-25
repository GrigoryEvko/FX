import FX1PolyAudit.DependencyAudit
import FX1Poly.Dimensions.Graded.GradedReductionSubstitution

/-! # FX1PolyAudit.Dimensions.Graded.GradedReductionSubstitution — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Modal.shiftRenaming
#assert_no_axioms FX1Poly.Modal.shift_eq_renameTerm
#assert_no_axioms FX1Poly.Modal.shift_zero_eq_renameTerm
#assert_no_axioms FX1Poly.Modal.singleSubstitution
#assert_no_axioms FX1Poly.Modal.substAt_eq_applySubstitution
#assert_no_axioms FX1Poly.Modal.consSubstitution
#assert_no_axioms FX1Poly.Modal.substAt_zero_applySubstitution_lift
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reduces.applySubstitution
#assert_no_axioms FX1Poly.Modal.GradedLambda.Reduces.substAt
#assert_no_axioms FX1Poly.Modal.GradedLambda.IsStronglyNormalizing.ofSubstAt

end FX1PolyAudit
