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

/-! ## AuditHIT_S1 — 27 `#assert_no_axioms` checks. -/

#assert_no_axioms LeanFX2.HoTT.HIT.S1PointLabel
#assert_no_axioms LeanFX2.HoTT.HIT.S1PathLabel
#assert_no_axioms LeanFX2.HoTT.HIT.S1Spec
#assert_no_axioms LeanFX2.HoTT.HIT.S1.S1Loop
#assert_no_axioms LeanFX2.HoTT.HIT.S1.S1Loop.relation
#assert_no_axioms LeanFX2.HoTT.HIT.S1.S1Loop.relation_refl
#assert_no_axioms LeanFX2.HoTT.HIT.S1.S1Loop.relation_symm
#assert_no_axioms LeanFX2.HoTT.HIT.S1.S1Loop.relation_trans
#assert_no_axioms LeanFX2.HoTT.HIT.S1.loopSpec
#assert_no_axioms LeanFX2.HoTT.HIT.S1.setoid
#assert_no_axioms LeanFX2.HoTT.HIT.S1.base
#assert_no_axioms LeanFX2.HoTT.HIT.S1.forwardLoop
#assert_no_axioms LeanFX2.HoTT.HIT.S1.backwardLoop
#assert_no_axioms LeanFX2.HoTT.HIT.S1.loop
#assert_no_axioms LeanFX2.HoTT.HIT.S1.loopForward
#assert_no_axioms LeanFX2.HoTT.HIT.S1.loopBackward
#assert_no_axioms LeanFX2.HoTT.HIT.S1.loopBetween
#assert_no_axioms LeanFX2.HoTT.HIT.S1.rec
#assert_no_axioms LeanFX2.HoTT.HIT.S1.recFromWinding
#assert_no_axioms LeanFX2.HoTT.HIT.S1.rec_base
#assert_no_axioms LeanFX2.HoTT.HIT.S1.rec_loop
#assert_no_axioms LeanFX2.HoTT.HIT.S1.recFromWinding_base
#assert_no_axioms LeanFX2.HoTT.HIT.S1.recFromWinding_loopBetween
#assert_no_axioms LeanFX2.HoTT.HIT.S1.dependentInductor
#assert_no_axioms LeanFX2.HoTT.HIT.S1.dependentInductor_base
#assert_no_axioms LeanFX2.HoTT.HIT.S1.dependentInductor_loop
#assert_no_axioms LeanFX2.HoTT.HIT.S1.dependentInductor_loopBetween

end LeanFX2.Tools
