import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.PathLamStructuralAffinity

/-! # FX1PolyAudit/PathLamStructuralAffinity — the structural-affinity audit shard

Per-declaration zero-axiom gate for the structural-affinity theorem: under a `lockCons` context the locked
interval dimension `var 0` is union-typeable only at the `.dimensional` modality (the live bridge use), and is
NOT usable at a FIBRANT obligation, so the canonical subject-reduction breaker `pair (var 0) (var 0)` is
rejected by the #1829 fibrant-guarded use-site conjunct.  Must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.varSubjectIsAccessibleAtSomeModality
#assert_no_axioms FX1Poly.Typed.lockedDimensionVar_isNotFibrantlyUsable

end FX1PolyAudit
