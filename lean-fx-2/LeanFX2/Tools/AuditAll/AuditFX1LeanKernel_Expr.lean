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

/-! ## AuditFX1LeanKernel_Expr — 20 `#assert_no_axioms` checks. -/

#assert_no_axioms LeanFX2.FX1.LeanKernel.Expr
#assert_no_axioms LeanFX2.FX1.LeanKernel.Expr.recontextualize
#assert_no_axioms LeanFX2.FX1.LeanKernel.Expr.nodeCount
#assert_no_axioms LeanFX2.FX1.LeanKernel.Expr.nodeCount_app
#assert_no_axioms LeanFX2.FX1.LeanKernel.Expr.nodeCount_mdata
#assert_no_axioms LeanFX2.FX1.LeanKernel.Expr.renameWith
#assert_no_axioms LeanFX2.FX1.LeanKernel.Expr.weaken
#assert_no_axioms LeanFX2.FX1.LeanKernel.Expr.subst
#assert_no_axioms LeanFX2.FX1.LeanKernel.Expr.instantiate
#assert_no_axioms LeanFX2.FX1.LeanKernel.Expr.instantiate_bvar_zero
#assert_no_axioms LeanFX2.FX1.LeanKernel.Expr.instantiate_bvar_succ
#assert_no_axioms LeanFX2.FX1.LeanKernel.Expr.weaken_bvar
#assert_no_axioms LeanFX2.FX1.LeanKernel.Expr.InferResult
#assert_no_axioms LeanFX2.FX1.LeanKernel.Expr.inferTypeFromResult?
#assert_no_axioms LeanFX2.FX1.LeanKernel.Expr.inferResult?
#assert_no_axioms LeanFX2.FX1.LeanKernel.Expr.infer?
#assert_no_axioms LeanFX2.FX1.LeanKernel.Expr.inferTypeFromResult?_sound
#assert_no_axioms LeanFX2.FX1.LeanKernel.Expr.infer?_sound
#assert_no_axioms LeanFX2.FX1.LeanKernel.Expr.check?
#assert_no_axioms LeanFX2.FX1.LeanKernel.Expr.check?_sound

end LeanFX2.Tools
