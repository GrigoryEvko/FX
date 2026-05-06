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

/-! ## AuditSessions — 26 `#assert_no_axioms` checks. -/

#assert_no_axioms LeanFX2.SessionProtocol
#assert_no_axioms LeanFX2.SessionProtocol.depth
#assert_no_axioms LeanFX2.SessionProtocol.isFinite
#assert_no_axioms LeanFX2.SessionProtocol.isFinite_of_tree
#assert_no_axioms LeanFX2.SessionProtocol.isFiniteDecidable
#assert_no_axioms LeanFX2.SessionProtocol.isFinite.decidable
#assert_no_axioms LeanFX2.SessionProtocol.dual
#assert_no_axioms LeanFX2.SessionProtocol.dual_end
#assert_no_axioms LeanFX2.SessionProtocol.dual_involutive
#assert_no_axioms LeanFX2.SessionProtocol.Action
#assert_no_axioms LeanFX2.SessionProtocol.Action.dual
#assert_no_axioms LeanFX2.SessionProtocol.Action.dual_involutive
#assert_no_axioms LeanFX2.SessionProtocol.Action.dual_injective
#assert_no_axioms LeanFX2.SessionProtocol.Step
#assert_no_axioms LeanFX2.SessionProtocol.Step.preserves_isFinite
#assert_no_axioms LeanFX2.SessionProtocol.Step.dual
#assert_no_axioms LeanFX2.SessionProtocol.Step.not_from_end
#assert_no_axioms LeanFX2.SessionProtocol.Step.target_deterministic
#assert_no_axioms LeanFX2.SessionProtocol.Step.of_dual
#assert_no_axioms LeanFX2.SessionProtocol.Step.dual_iff
#assert_no_axioms LeanFX2.SessionGlobal
#assert_no_axioms LeanFX2.SessionGlobal.isWellFormed
#assert_no_axioms LeanFX2.SessionGlobal.transmit_self_not_isWellFormed
#assert_no_axioms LeanFX2.SessionGlobal.choice_self_not_isWellFormed
#assert_no_axioms LeanFX2.SessionGlobal.Projects
#assert_no_axioms LeanFX2.SessionGlobal.Projects.local_isFinite

end LeanFX2.Tools
