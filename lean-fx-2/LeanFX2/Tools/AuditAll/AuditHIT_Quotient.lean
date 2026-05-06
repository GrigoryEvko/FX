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

/-! ## AuditHIT_Quotient — 21 `#assert_no_axioms` checks. -/

#assert_no_axioms LeanFX2.HoTT.HIT.QuotientHIT
#assert_no_axioms LeanFX2.HoTT.HIT.QuotientHIT.equality
#assert_no_axioms LeanFX2.HoTT.HIT.QuotientHIT.intro
#assert_no_axioms LeanFX2.HoTT.HIT.QuotientHIT.sound
#assert_no_axioms LeanFX2.HoTT.HIT.QuotientHIT.rec
#assert_no_axioms LeanFX2.HoTT.HIT.QuotientHIT.rec_intro
#assert_no_axioms LeanFX2.HoTT.HIT.QuotientHIT.rec_sound
#assert_no_axioms LeanFX2.HoTT.HIT.QuotientHIT.dependentInductor
#assert_no_axioms LeanFX2.HoTT.HIT.QuotientHIT.dependentInductor_intro
#assert_no_axioms LeanFX2.HoTT.HIT.QuotientHIT.dependentInductor_sound
#assert_no_axioms LeanFX2.HoTT.HIT.QuotientHIT.recConstant
#assert_no_axioms LeanFX2.HoTT.HIT.QuotientHIT.recConstant_intro
#assert_no_axioms LeanFX2.HoTT.HIT.CoequalizerHIT
#assert_no_axioms LeanFX2.HoTT.HIT.CoequalizerHIT.point
#assert_no_axioms LeanFX2.HoTT.HIT.CoequalizerHIT.equalize
#assert_no_axioms LeanFX2.HoTT.HIT.CoequalizerHIT.rec
#assert_no_axioms LeanFX2.HoTT.HIT.CoequalizerHIT.rec_point
#assert_no_axioms LeanFX2.HoTT.HIT.CoequalizerHIT.rec_equalize
#assert_no_axioms LeanFX2.HoTT.HIT.CoequalizerHIT.dependentInductor
#assert_no_axioms LeanFX2.HoTT.HIT.CoequalizerHIT.dependentInductor_point
#assert_no_axioms LeanFX2.HoTT.HIT.CoequalizerHIT.dependentInductor_equalize

end LeanFX2.Tools
