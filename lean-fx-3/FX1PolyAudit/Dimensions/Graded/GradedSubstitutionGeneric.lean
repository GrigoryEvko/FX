import FX1PolyAudit.DependencyAudit
import FX1Poly.Dimensions.Graded.GradedSubstitutionGeneric

/-! # FX1PolyAudit.Dimensions.Graded.GradedSubstitutionGeneric — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Modal.removeTypeAtOver
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.removeAt
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.gradeAt
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.substInto
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.substInto_succ_cons
#assert_no_axioms FX1Poly.Modal.removeTypeAtOver_length
#assert_no_axioms FX1Poly.Modal.lookup_removeTypeAtOver_lt
#assert_no_axioms FX1Poly.Modal.lookup_removeTypeAtOver_ge
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.gradeAt_nil
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.gradeAt_zero
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.removeAt_zero
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.gradeAt_single_self
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.gradeAt_single_ne
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.removeAt_single_self
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.removeAt_single_lt
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.removeAt_single_gt
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.removeAt_add
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.removeAt_scale
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.gradeAt_scale
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.gradeAt_add
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.add_interchange
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.substInto_single_self
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.substInto_single_lt
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.substInto_single_gt
#assert_no_axioms FX1Poly.Modal.GradeVectorOver.substInto_appGrade

end FX1PolyAudit
