import LeanFX2.Tools.DependencyAudit
import LeanFX2.FX1Bridge.Unit

namespace LeanFX2.Tools

/-! ## AuditFX1Bridge_UnitValue — 7 `#assert_no_axioms` checks. -/

#assert_no_axioms LeanFX2.FX1Bridge.unitValueAtomId
#assert_no_axioms LeanFX2.FX1Bridge.unitValueName
#assert_no_axioms LeanFX2.FX1Bridge.unitValueExpr
#assert_no_axioms LeanFX2.FX1Bridge.unitValueDeclaration
#assert_no_axioms LeanFX2.FX1Bridge.encodeRawTerm_unit_eq_unitValueExpr
#assert_no_axioms LeanFX2.FX1Bridge.unitValueDeclaration_wellTyped
#assert_no_axioms LeanFX2.FX1Bridge.unitValueName_fresh

end LeanFX2.Tools
