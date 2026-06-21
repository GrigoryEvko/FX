import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Engine.RuleTables.IotaElimUnionSRCertificate

/-! # FX1PolyAudit/AuditIotaElimUnionSRCertificate — TYTAB-2 capstone audit shard

Per-declaration zero-axiom gate for the decidable bundle ι-subject-reduction certificate: the
slot-agnostic static<->operational coherence checker + its `rfl` certificate, the OBLIGATION-FREE unified
bundle SR soundness theorem (TYTAB-2 SRINV — the per-row obligation parameter and the
`UnionClassifierRespectsConv` validity `Prop` are both RETIRED, every reducing row unconditional), and the
coverage record + witness.  Every declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## The decidable coherence certificate -/

#assert_no_axioms FX1Poly.Typed.iotaRowCoheresWithBundle
#assert_no_axioms FX1Poly.Typed.WfIotaElimSRTable
#assert_no_axioms FX1Poly.Typed.iotaRuleTable_elimSRCertified

/-! ## The unified bundle SR soundness theorem (obligation-free) -/

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.bundleIotaRowSubjectReduction
-- ★ TYTAB-2 SRINV: the single bundle SR interface — all seventeen reducing rows unconditional, no obligation.
#assert_no_axioms FX1Poly.Typed.HasTypeUnion.subjectReductionOnIotaRedex

/-! ## The coverage record / witness -/

#assert_no_axioms FX1Poly.Typed.WfIotaElimSRCoverage
#assert_no_axioms FX1Poly.Typed.wfIotaElimSRCoverageWitness

end FX1PolyAudit
