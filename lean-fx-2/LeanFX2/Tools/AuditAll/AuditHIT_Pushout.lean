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

/-! ## AuditHIT_Pushout — 15 `#assert_no_axioms` checks. -/

#assert_no_axioms LeanFX2.HoTT.HIT.PushoutCarrier
#assert_no_axioms LeanFX2.HoTT.HIT.PushoutHIT
#assert_no_axioms LeanFX2.HoTT.HIT.PushoutHIT.evaluate
#assert_no_axioms LeanFX2.HoTT.HIT.PushoutHIT.dependentEvaluate
#assert_no_axioms LeanFX2.HoTT.HIT.PushoutHIT.left
#assert_no_axioms LeanFX2.HoTT.HIT.PushoutHIT.right
#assert_no_axioms LeanFX2.HoTT.HIT.PushoutHIT.glue
#assert_no_axioms LeanFX2.HoTT.HIT.PushoutHIT.rec
#assert_no_axioms LeanFX2.HoTT.HIT.PushoutHIT.rec_left
#assert_no_axioms LeanFX2.HoTT.HIT.PushoutHIT.rec_right
#assert_no_axioms LeanFX2.HoTT.HIT.PushoutHIT.rec_glue
#assert_no_axioms LeanFX2.HoTT.HIT.PushoutHIT.dependentInductor
#assert_no_axioms LeanFX2.HoTT.HIT.PushoutHIT.dependentInductor_left
#assert_no_axioms LeanFX2.HoTT.HIT.PushoutHIT.dependentInductor_right
#assert_no_axioms LeanFX2.HoTT.HIT.PushoutHIT.dependentInductor_glue

end LeanFX2.Tools
