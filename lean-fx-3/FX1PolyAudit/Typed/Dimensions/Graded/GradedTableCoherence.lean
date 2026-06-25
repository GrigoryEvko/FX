import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Dimensions.Graded.GradedTableCoherence

/-! # FX1PolyAudit.Typed.Dimensions.Graded.GradedTableCoherence — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.natToUsageGrade_ofZero
#assert_no_axioms FX1Poly.Typed.natToUsageGrade_addHom
#assert_no_axioms FX1Poly.Typed.usageBoundsCount_iff_gradeLe
#assert_no_axioms FX1Poly.Typed.gradedBinderChecks_iff_gradeSubsumption
#assert_no_axioms FX1Poly.Typed.strictLinearLam_meetsAffineDiscipline
#assert_no_axioms FX1Poly.Typed.fullJudgmentLamGrade_doesNotMeetDiscipline
#assert_no_axioms FX1Poly.Typed.identityMeetsDisciplineAtOmega
#assert_no_axioms FX1Poly.Typed.identityNotGradeableAtOmega
#assert_no_axioms FX1Poly.Typed.gradeTableCoherenceVerdict

end FX1PolyAudit
