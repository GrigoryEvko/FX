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

/-! ## AuditFX1Bridge_Record — record bridge `#assert_no_axioms` checks. -/

#assert_no_axioms LeanFX2.FX1Bridge.encodeTy_record
#assert_no_axioms LeanFX2.FX1Bridge.encodeRawTerm_recordIntro
#assert_no_axioms LeanFX2.FX1Bridge.encodeRawTerm_recordProj
#assert_no_axioms LeanFX2.FX1Bridge.decodeTy_record
#assert_no_axioms LeanFX2.FX1Bridge.decodeRawTerm_recordIntro
#assert_no_axioms LeanFX2.FX1Bridge.decodeRawTerm_recordProj
#assert_no_axioms LeanFX2.FX1Bridge.encodeTy_record_eq_field
#assert_no_axioms LeanFX2.FX1Bridge.encodeRawTerm_recordIntro_eq_field
#assert_no_axioms LeanFX2.FX1Bridge.encodeRawTerm_recordProj_eq_record
#assert_no_axioms LeanFX2.FX1Bridge.encodedRecordType_has_sort
#assert_no_axioms LeanFX2.FX1Bridge.encodedRecordIntro_has_type
#assert_no_axioms LeanFX2.FX1Bridge.encodedRecordProj_has_type
#assert_no_axioms LeanFX2.FX1Bridge.encodeTermSound_recordIntro
#assert_no_axioms LeanFX2.FX1Bridge.encodeTermSound_recordIntro_roundTrip
#assert_no_axioms LeanFX2.FX1Bridge.encodeTermSound_recordProj
#assert_no_axioms LeanFX2.FX1Bridge.encodeTermSound_recordProj_roundTrip

end LeanFX2.Tools
