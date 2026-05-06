import LeanFX2.Tools.DependencyAudit
import LeanFX2.Tools.AuditGen
import LeanFX2.Tools.StrictHarness
import LeanFX2
import LeanFX2.FX1.LeanKernel.Name
import LeanFX2.FX1.LeanKernel.Level
import LeanFX2.FX1.LeanKernel.Expr
import LeanFX2.FX1.LeanKernel.Substitution
import LeanFX2.FX1.LeanKernel.Reduction
import LeanFX2.FX1.LeanKernel.Inductive
import LeanFX2.FX1.LeanKernel.HasType
import LeanFX2.FX1.LeanKernel.Check
import LeanFX2.FX1.LeanKernel.Soundness
import LeanFX2.FX1.LeanKernel.Audit
import LeanFX2.FX1
import LeanFX2.FX1Bridge

namespace LeanFX2.Tools

/-! ## AuditFX1_Other — 17 `#assert_no_axioms` checks. -/

#assert_no_axioms LeanFX2.FX1.Boolean.and_true_left
#assert_no_axioms LeanFX2.FX1.Boolean.and_true_right
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
