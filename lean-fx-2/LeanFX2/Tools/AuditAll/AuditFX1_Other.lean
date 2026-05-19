import LeanFX2.Tools.DependencyAudit
import LeanFX2.FX1.Core.Soundness

namespace LeanFX2.Tools

/-! ## AuditFX1_Other — 17 `#assert_no_axioms` checks. -/

#assert_no_axioms LeanFX2.FX1.Boolean.and_true_left
#assert_no_axioms LeanFX2.FX1.Boolean.and_true_right
#assert_no_axioms LeanFX2.FX1.Boolean.eqResult
#assert_no_axioms LeanFX2.FX1.ListPayload.eqResult
#assert_no_axioms LeanFX2.FX1.EqualityResult
#assert_no_axioms LeanFX2.FX1.EqualityResult.equal
#assert_no_axioms LeanFX2.FX1.EqualityResult.notEqual
#assert_no_axioms LeanFX2.FX1.StepStar
#assert_no_axioms LeanFX2.FX1.StepStar.refl
#assert_no_axioms LeanFX2.FX1.StepStar.step
#assert_no_axioms LeanFX2.FX1.StepStar.single
#assert_no_axioms LeanFX2.FX1.StepStar.trans
#assert_no_axioms LeanFX2.FX1.DefEq
#assert_no_axioms LeanFX2.FX1.DefEq.common
#assert_no_axioms LeanFX2.FX1.DefEq.refl
#assert_no_axioms LeanFX2.FX1.DefEq.symm
#assert_no_axioms LeanFX2.FX1.DefEq.weaken_environment
#assert_no_axioms LeanFX2.FX1.check_sound
#assert_no_axioms LeanFX2.FX1.checkCore_sound

end LeanFX2.Tools
