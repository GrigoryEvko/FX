import LeanFX2.Tools.DependencyAudit
import LeanFX2.FX1Bridge.Lambda
import LeanFX2.FX1Bridge.Unit

namespace LeanFX2.Tools

/-! ## AuditFX1Bridge_UnitType — 11 `#assert_no_axioms` checks. -/

#assert_no_axioms LeanFX2.FX1Bridge.unitTypeAtomId
#assert_no_axioms LeanFX2.FX1Bridge.unitTypeName
#assert_no_axioms LeanFX2.FX1Bridge.unitTypeExpr
#assert_no_axioms LeanFX2.FX1Bridge.unitTypeDeclaration
#assert_no_axioms LeanFX2.FX1Bridge.unitTypeEnvironment
#assert_no_axioms LeanFX2.FX1Bridge.encodeTy_unit_eq_unitTypeExpr
#assert_no_axioms LeanFX2.FX1Bridge.unitTypeDeclaration_wellTyped
#assert_no_axioms LeanFX2.FX1Bridge.unitTypeEnvironment_wellFormed
#assert_no_axioms LeanFX2.FX1Bridge.unitValueName_ne_unitTypeName
#assert_no_axioms LeanFX2.FX1Bridge.unitTypeExpr_has_sort_in_unitEnvironment
#assert_no_axioms LeanFX2.FX1Bridge.unitTypeExpr_has_sort_in_encodedUnitVarContext

end LeanFX2.Tools
