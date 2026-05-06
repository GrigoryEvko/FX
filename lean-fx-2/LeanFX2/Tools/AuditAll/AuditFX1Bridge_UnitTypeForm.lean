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

/-! ## AuditFX1Bridge_UnitTypeForm — 16 `#assert_no_axioms` checks. -/

#assert_no_axioms LeanFX2.FX1Bridge.unitPiIdentityRaw
#assert_no_axioms LeanFX2.FX1Bridge.unitPiIdentityType
#assert_no_axioms LeanFX2.FX1Bridge.unitPiIdentityTerm
#assert_no_axioms LeanFX2.FX1Bridge.encodeTy_unitPiIdentity
#assert_no_axioms LeanFX2.FX1Bridge.encodeRawTerm_unitPiIdentity
#assert_no_axioms LeanFX2.FX1Bridge.encodedUnitPiIdentityType_has_sort
#assert_no_axioms LeanFX2.FX1Bridge.encodedUnitPiIdentity_has_type
#assert_no_axioms LeanFX2.FX1Bridge.encodeTermSound_unitPiIdentity
#assert_no_axioms LeanFX2.FX1Bridge.encodeTermSound_unitPiIdentity_roundTrip
#assert_no_axioms LeanFX2.FX1Bridge.unitPiIdentityAppRaw
#assert_no_axioms LeanFX2.FX1Bridge.unitPiIdentityAppTerm
#assert_no_axioms LeanFX2.FX1Bridge.encodeRawTerm_unitPiIdentityApp
#assert_no_axioms LeanFX2.FX1Bridge.encodedUnitPiIdentityApp_has_type
#assert_no_axioms LeanFX2.FX1Bridge.encodedUnitPiIdentityApp_betaStep
#assert_no_axioms LeanFX2.FX1Bridge.encodeTermSound_unitPiIdentityApp
#assert_no_axioms LeanFX2.FX1Bridge.encodeTermSound_unitPiIdentityApp_roundTrip

end LeanFX2.Tools
