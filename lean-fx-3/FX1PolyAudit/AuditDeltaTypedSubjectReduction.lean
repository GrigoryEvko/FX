import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.DeltaTypedSubjectReduction

/-! # FX1PolyAudit/AuditDeltaTypedSubjectReduction — RW-4 typed δ-link audit shard

Per-declaration zero-axiom gate for the typed δ subject-reduction tier: the
reserved-tier pin for the canonical δ heads (`deltaConstantHead_reserved`),
the grown-untyped fact for a δ-redex cell (`deltaConstantCell_grownUntyped`),
and the ★ vacuous typed δ-SR (`deltaRootStep_typedSubjectReduction`).  Every
declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.deltaConstantHead_reserved
#assert_no_axioms FX1Poly.Typed.deltaConstantCell_grownUntyped
#assert_no_axioms FX1Poly.Typed.deltaRootStep_typedSubjectReduction

end FX1PolyAudit
