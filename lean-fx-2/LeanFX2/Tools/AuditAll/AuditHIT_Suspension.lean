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

/-! ## AuditHIT_Suspension — 21 `#assert_no_axioms` checks. -/

#assert_no_axioms LeanFX2.HoTT.HIT.SuspensionPoint
#assert_no_axioms LeanFX2.HoTT.HIT.SuspensionRel
#assert_no_axioms LeanFX2.HoTT.HIT.SuspensionRel.relation_refl
#assert_no_axioms LeanFX2.HoTT.HIT.SuspensionRel.relation_symm
#assert_no_axioms LeanFX2.HoTT.HIT.SuspensionRel.relation_trans
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.relation
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.relation_refl
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.relation_symm
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.relation_trans
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.setoid
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.north
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.south
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.meridian
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.rec
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.rec_north
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.rec_south
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.rec_meridian
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.dependentInductor
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.dependentInductor_north
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.dependentInductor_south
#assert_no_axioms LeanFX2.HoTT.HIT.Suspension.dependentInductor_meridian

end LeanFX2.Tools
