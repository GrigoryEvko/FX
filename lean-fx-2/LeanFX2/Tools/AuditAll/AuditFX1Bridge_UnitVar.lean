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

/-! ## AuditFX1Bridge_UnitVar — 10 `#assert_no_axioms` checks. -/

#assert_no_axioms LeanFX2.FX1Bridge.unitVarPosition
#assert_no_axioms LeanFX2.FX1Bridge.unitVarRaw
#assert_no_axioms LeanFX2.FX1Bridge.unitVarContext
#assert_no_axioms LeanFX2.FX1Bridge.encodeCtx_unitVar
#assert_no_axioms LeanFX2.FX1Bridge.encodeRawTerm_unitVar
#assert_no_axioms LeanFX2.FX1Bridge.unitVarType_eq_unit
#assert_no_axioms LeanFX2.FX1Bridge.unitVarTerm
#assert_no_axioms LeanFX2.FX1Bridge.encodedUnitVarContext_wellFormed
#assert_no_axioms LeanFX2.FX1Bridge.encodedNewestUnitVar_has_type
#assert_no_axioms LeanFX2.FX1Bridge.encodeTermSound_newestUnitVar

end LeanFX2.Tools
