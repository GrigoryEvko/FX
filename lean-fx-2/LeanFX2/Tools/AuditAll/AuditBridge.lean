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

/-! ## AuditBridge — 22 `#assert_no_axioms` checks. -/

#assert_no_axioms LeanFX2.Bridge.constantPathToId
#assert_no_axioms LeanFX2.Bridge.constantPathToId_toRaw
#assert_no_axioms LeanFX2.Bridge.constantPathToId_onCanonical
#assert_no_axioms LeanFX2.Bridge.reflIdToConstantPath
#assert_no_axioms LeanFX2.Bridge.reflIdToConstantPath_toRaw
#assert_no_axioms LeanFX2.Bridge.reflIdToConstantPath_onRefl
#assert_no_axioms LeanFX2.Bridge.constantPath_roundTrip_onCanonical
#assert_no_axioms LeanFX2.Bridge.reflId_roundTrip_onRefl
#assert_no_axioms LeanFX2.Bridge.constantPath_roundTrip_toRaw
#assert_no_axioms LeanFX2.Bridge.reflId_roundTrip_toRaw
#assert_no_axioms LeanFX2.Bridge.pathToIdMeta
#assert_no_axioms LeanFX2.Bridge.idToPathMeta
#assert_no_axioms LeanFX2.Bridge.idToPathMeta_pathToIdMeta
#assert_no_axioms LeanFX2.Bridge.pathToIdMeta_idToPathMeta
#assert_no_axioms LeanFX2.Bridge.pathIdEquivMeta
#assert_no_axioms LeanFX2.Bridge.pathIdEquivMeta_toFun
#assert_no_axioms LeanFX2.Bridge.pathIdEquivMeta_invFun
#assert_no_axioms LeanFX2.Bridge.idEqTypeRefl
#assert_no_axioms LeanFX2.Bridge.idEqTypeHet
#assert_no_axioms LeanFX2.Bridge.constantTypePathToEquivRefl
#assert_no_axioms LeanFX2.Bridge.constantTypePathToEquivRefl_toRaw
#assert_no_axioms LeanFX2.Bridge.constantTypePathToEquivRefl_onCanonical

end LeanFX2.Tools
