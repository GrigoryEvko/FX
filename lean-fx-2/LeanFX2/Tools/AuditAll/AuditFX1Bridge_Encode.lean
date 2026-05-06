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

/-! ## AuditFX1Bridge_Encode — 14 `#assert_no_axioms` checks. -/

#assert_no_axioms LeanFX2.FX1Bridge.encodeEmptyCtx
#assert_no_axioms LeanFX2.FX1Bridge.encodeUniverseLevel
#assert_no_axioms LeanFX2.FX1Bridge.encodeRawTerm_universeCodeSameLevel
#assert_no_axioms LeanFX2.FX1Bridge.encodeTy_universeSameLevel
#assert_no_axioms LeanFX2.FX1Bridge.encodeUniverseLevel_beq_self
#assert_no_axioms LeanFX2.FX1Bridge.decodeTy_universeSameLevel
#assert_no_axioms LeanFX2.FX1Bridge.decodeRawTerm_universeCodeSameLevel
#assert_no_axioms LeanFX2.FX1Bridge.decodeTy_universeSameLevel_encode
#assert_no_axioms LeanFX2.FX1Bridge.decodeRawTerm_universeCodeSameLevel_encode
#assert_no_axioms LeanFX2.FX1Bridge.encodeRawTerm_universeCodeSameLevel_eq_sort
#assert_no_axioms LeanFX2.FX1Bridge.encodeTy_universeSameLevel_eq_successor_sort
#assert_no_axioms LeanFX2.FX1Bridge.encodedUniverseCodeSameLevel_has_type
#assert_no_axioms LeanFX2.FX1Bridge.encodeTermSound_universeCodeSameLevel
#assert_no_axioms LeanFX2.FX1Bridge.encodeTermSound_universeCodeSameLevel_roundTrip

end LeanFX2.Tools
