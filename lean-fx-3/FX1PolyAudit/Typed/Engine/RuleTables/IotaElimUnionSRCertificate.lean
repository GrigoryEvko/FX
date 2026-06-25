import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Engine.RuleTables.IotaElimUnionSRCertificate

/-! # FX1PolyAudit.Typed.Engine.RuleTables.IotaElimUnionSRCertificate

Zero-axiom audit shard mirroring kernel module `FX1Poly.Typed.Engine.RuleTables.IotaElimUnionSRCertificate`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.iotaRowCoheresWithBundle

#assert_no_axioms FX1Poly.Typed.WfIotaElimSRTable

#assert_no_axioms FX1Poly.Typed.iotaRuleTable_elimSRCertified

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.bundleIotaRowSubjectReduction

-- ★ TYTAB-2 SRINV: the single bundle SR interface — all seventeen reducing rows unconditional, no obligation.
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.subjectReductionOnIotaRedex

#assert_no_axioms FX1Poly.Typed.WfIotaElimSRCoverage

#assert_no_axioms FX1Poly.Typed.wfIotaElimSRCoverageWitness

end FX1PolyAudit
