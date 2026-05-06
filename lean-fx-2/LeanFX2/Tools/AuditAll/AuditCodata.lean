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

/-! ## AuditCodata — 31 `#assert_no_axioms` checks. -/

#assert_no_axioms LeanFX2.Codata.Stream
#assert_no_axioms LeanFX2.Codata.Stream.head
#assert_no_axioms LeanFX2.Codata.Stream.tail
#assert_no_axioms LeanFX2.Codata.Stream.iterateState
#assert_no_axioms LeanFX2.Codata.Stream.unfold
#assert_no_axioms LeanFX2.Codata.Stream.Bisim
#assert_no_axioms LeanFX2.Codata.Stream.bisim_refl
#assert_no_axioms LeanFX2.Codata.Stream.bisim_symm
#assert_no_axioms LeanFX2.Codata.Stream.bisim_trans
#assert_no_axioms LeanFX2.Codata.Stream.head_unfold
#assert_no_axioms LeanFX2.Codata.Stream.tail_unfold
#assert_no_axioms LeanFX2.Codata.Stream.bisim_head
#assert_no_axioms LeanFX2.Codata.Stream.bisim_tail
#assert_no_axioms LeanFX2.Codata.Stream.productive
#assert_no_axioms LeanFX2.Codata.constantZero
#assert_no_axioms LeanFX2.Codata.naturals
#assert_no_axioms LeanFX2.Codata.Stream.Destructor
#assert_no_axioms LeanFX2.Codata.Stream.Destructor.Result
#assert_no_axioms LeanFX2.Codata.Stream.Step
#assert_no_axioms LeanFX2.Codata.Stream.Step.head_deterministic
#assert_no_axioms LeanFX2.Codata.Stream.Step.tail_deterministic
#assert_no_axioms LeanFX2.Codata.Stream.Step.head_respects_bisim
#assert_no_axioms LeanFX2.Codata.Stream.Step.tail_respects_bisim
#assert_no_axioms LeanFX2.Codata.Stream.Step.head_unfold
#assert_no_axioms LeanFX2.Codata.Stream.Step.tail_unfold_bisim
#assert_no_axioms LeanFX2.Codata.Stream.Productive
#assert_no_axioms LeanFX2.Codata.Stream.productive_of_stream
#assert_no_axioms LeanFX2.Codata.Stream.productive_head
#assert_no_axioms LeanFX2.Codata.Stream.productive_tail
#assert_no_axioms LeanFX2.Codata.Stream.productive_unfold
#assert_no_axioms LeanFX2.Codata.Stream.productive_of_bisim

end LeanFX2.Tools
