import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Normalization.Core.IotaFragmentOrdinalAnalysis

/-! # AuditIotaFragmentOrdinalAnalysis — zero-axiom gate for ORD-NORM (#1448)

The certified ι-fragment's proof-theoretic ordinal (the RPO ordinal) and
the SN-as-its-well-foundedness identification.  Each pin must be free of
`propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.iotaOrientedReduction_strictlyDecreasesRpoOrdinal
#assert_no_axioms FX1Poly.Core.iotaFragmentSN_fromRpoOrdinalWellFounded
#assert_no_axioms FX1Poly.Core.iotaFragmentSN_byRpoOrdinal

end FX1PolyAudit
