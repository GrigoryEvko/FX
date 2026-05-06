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

/-! ## AuditFX1LeanKernel_Env — 14 `#assert_no_axioms` checks. -/

#assert_no_axioms LeanFX2.FX1.LeanKernel.Environment
#assert_no_axioms LeanFX2.FX1.LeanKernel.Environment.empty
#assert_no_axioms LeanFX2.FX1.LeanKernel.Environment.findConstant?
#assert_no_axioms LeanFX2.FX1.LeanKernel.Environment.findInductive?
#assert_no_axioms LeanFX2.FX1.LeanKernel.Environment.findConstant?_empty
#assert_no_axioms LeanFX2.FX1.LeanKernel.Environment.findInductive?_empty
#assert_no_axioms LeanFX2.FX1.LeanKernel.Environment.HasConstantInList
#assert_no_axioms LeanFX2.FX1.LeanKernel.Environment.HasConstantInList.newest
#assert_no_axioms LeanFX2.FX1.LeanKernel.Environment.HasConstantInList.older
#assert_no_axioms LeanFX2.FX1.LeanKernel.Environment.HasConstant
#assert_no_axioms LeanFX2.FX1.LeanKernel.Environment.HasConstantInList.weaken
#assert_no_axioms LeanFX2.FX1.LeanKernel.Environment.ConstantLookupResult
#assert_no_axioms LeanFX2.FX1.LeanKernel.Environment.findConstantResultInList?
#assert_no_axioms LeanFX2.FX1.LeanKernel.Environment.findConstantResult?

end LeanFX2.Tools
