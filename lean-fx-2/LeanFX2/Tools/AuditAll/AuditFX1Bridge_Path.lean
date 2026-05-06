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

/-! ## AuditFX1Bridge_Path — path bridge `#assert_no_axioms` checks. -/

#assert_no_axioms LeanFX2.FX1Bridge.encodeTy_path
#assert_no_axioms LeanFX2.FX1Bridge.encodeRawTerm_pathLam
#assert_no_axioms LeanFX2.FX1Bridge.encodeRawTerm_pathApp
#assert_no_axioms LeanFX2.FX1Bridge.decodeTy_interval_encodeTy_interval
#assert_no_axioms LeanFX2.FX1Bridge.subst0_weaken
#assert_no_axioms LeanFX2.FX1Bridge.decodeTy_path
#assert_no_axioms LeanFX2.FX1Bridge.decodeRawTerm_pathLam
#assert_no_axioms LeanFX2.FX1Bridge.decodeRawTerm_pathApp
#assert_no_axioms LeanFX2.FX1Bridge.encodeTy_path_eq_pi
#assert_no_axioms LeanFX2.FX1Bridge.encodeRawTerm_pathLam_eq_lam
#assert_no_axioms LeanFX2.FX1Bridge.encodeRawTerm_pathApp_eq_app
#assert_no_axioms LeanFX2.FX1Bridge.encodedPathType_has_sort
#assert_no_axioms LeanFX2.FX1Bridge.encodedPathLam_has_type
#assert_no_axioms LeanFX2.FX1Bridge.encodedPathApp_has_type
#assert_no_axioms LeanFX2.FX1Bridge.encodeTermSound_pathLam
#assert_no_axioms LeanFX2.FX1Bridge.encodeTermSound_pathLam_roundTrip
#assert_no_axioms LeanFX2.FX1Bridge.encodeTermSound_pathApp
#assert_no_axioms LeanFX2.FX1Bridge.encodeTermSound_pathApp_roundTrip

end LeanFX2.Tools
