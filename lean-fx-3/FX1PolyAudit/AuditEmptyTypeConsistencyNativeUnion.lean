import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.Canonicity.Consistency.EmptyTypeConsistencyNativeUnion

/-! # FX1PolyAudit/AuditEmptyTypeConsistencyNativeUnion — TYTAB-2-FT consistency-route audit shard

Per-declaration zero-axiom gate for the assembled NATIVE union consistency route (`HasTypeUnion`'s closed
empty-type uninhabitedness, gated on the three named FT-lane residuals — native SN, iterated union subject
reduction, closed-normal canonicity).  Must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.consistencyOfNativeSubjectReduction

end FX1PolyAudit
