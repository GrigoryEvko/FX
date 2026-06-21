import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.HasTypeUnionCongruenceArms

/-! # FX1PolyAudit/AuditUnionCongruenceArms — TYTAB-2-FT gate-2 congruence-arm audit shard

Per-declaration zero-axiom gate for the per-arm congruence subject-reduction legs (gate 2 congruence half of
TYTAB-2-FT, #1697): the ofGrown arm at the empty context, discharged through the grown master.  Must be free
of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.ofGrownCongruenceAtEmptyContext

end FX1PolyAudit
