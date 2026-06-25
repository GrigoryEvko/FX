import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Normalization.Core.IotaFragmentOrdinalAnalysis

/-! # FX1PolyAudit.Core.Metatheory.Normalization.Core.IotaFragmentOrdinalAnalysis

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Metatheory.Normalization.Core.IotaFragmentOrdinalAnalysis`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.iotaOrientedReduction_strictlyDecreasesRpoOrdinal

#assert_no_axioms FX1Poly.Core.iotaFragmentSN_fromRpoOrdinalWellFounded

#assert_no_axioms FX1Poly.Core.iotaFragmentSN_byRpoOrdinal

end FX1PolyAudit
