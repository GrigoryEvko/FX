import LeanFX2.Tools.DependencyAudit
import LeanFX2.FX1Bridge.Var

namespace LeanFX2.Tools

/-! ## AuditFX1Bridge_UnitVar — 11 `#assert_no_axioms` checks. -/

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
#assert_no_axioms LeanFX2.FX1Bridge.encodeTermSound_newestUnitVar_roundTrip

end LeanFX2.Tools
