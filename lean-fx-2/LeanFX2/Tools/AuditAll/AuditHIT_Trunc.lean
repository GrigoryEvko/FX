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

/-! ## AuditHIT_Trunc — 28 `#assert_no_axioms` checks. -/

#assert_no_axioms LeanFX2.HoTT.HIT.PropTruncRel
#assert_no_axioms LeanFX2.HoTT.HIT.PropTruncRel.relation_refl
#assert_no_axioms LeanFX2.HoTT.HIT.PropTruncRel.relation_symm
#assert_no_axioms LeanFX2.HoTT.HIT.PropTruncRel.relation_trans
#assert_no_axioms LeanFX2.HoTT.HIT.PropTrunc
#assert_no_axioms LeanFX2.HoTT.HIT.PropTrunc.intro
#assert_no_axioms LeanFX2.HoTT.HIT.PropTrunc.squash
#assert_no_axioms LeanFX2.HoTT.HIT.PropTrunc.rec
#assert_no_axioms LeanFX2.HoTT.HIT.PropTrunc.rec_intro
#assert_no_axioms LeanFX2.HoTT.HIT.PropTrunc.rec_squash
#assert_no_axioms LeanFX2.HoTT.HIT.PropTrunc.dependentInductor
#assert_no_axioms LeanFX2.HoTT.HIT.PropTrunc.dependentInductor_intro
#assert_no_axioms LeanFX2.HoTT.HIT.PropTrunc.dependentInductor_squash
#assert_no_axioms LeanFX2.HoTT.HIT.PropTrunc.recConstant
#assert_no_axioms LeanFX2.HoTT.HIT.PropTrunc.recConstant_intro
#assert_no_axioms LeanFX2.HoTT.HIT.SetTruncRel
#assert_no_axioms LeanFX2.HoTT.HIT.SetTruncRel.relation_refl
#assert_no_axioms LeanFX2.HoTT.HIT.SetTruncRel.relation_symm
#assert_no_axioms LeanFX2.HoTT.HIT.SetTruncRel.relation_trans
#assert_no_axioms LeanFX2.HoTT.HIT.SetTrunc
#assert_no_axioms LeanFX2.HoTT.HIT.SetTrunc.intro
#assert_no_axioms LeanFX2.HoTT.HIT.SetTrunc.path
#assert_no_axioms LeanFX2.HoTT.HIT.SetTrunc.rec
#assert_no_axioms LeanFX2.HoTT.HIT.SetTrunc.rec_intro
#assert_no_axioms LeanFX2.HoTT.HIT.SetTrunc.rec_path
#assert_no_axioms LeanFX2.HoTT.HIT.SetTrunc.dependentInductor
#assert_no_axioms LeanFX2.HoTT.HIT.SetTrunc.dependentInductor_intro
#assert_no_axioms LeanFX2.HoTT.HIT.SetTrunc.dependentInductor_path

end LeanFX2.Tools
