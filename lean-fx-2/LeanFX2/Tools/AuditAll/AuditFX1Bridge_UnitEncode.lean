import LeanFX2.Tools.DependencyAudit
import LeanFX2.FX1Bridge.Unit

namespace LeanFX2.Tools

/-! ## AuditFX1Bridge_UnitEncode — 4 `#assert_no_axioms` checks. -/

#assert_no_axioms LeanFX2.FX1Bridge.encodeTy_unit
#assert_no_axioms LeanFX2.FX1Bridge.encodeRawTerm_unit
#assert_no_axioms LeanFX2.FX1Bridge.encodeTermSound_unit
#assert_no_axioms LeanFX2.FX1Bridge.encodeTermSound_unit_roundTrip

end LeanFX2.Tools
