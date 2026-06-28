import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Metatheory.SubjectReduction.PathLamStructuralAffinity

/-! # FX1PolyAudit/PathLamStructuralAffinity — the structural-affinity audit shard

Per-declaration zero-axiom gate for the structural-affinity theorem: under a `lockCons` context the locked
interval dimension `var 0` is not fibrantly union-typeable, so the canonical subject-reduction breaker
`pair (var 0) (var 0)` is structurally untypeable and `pathLam`'s affine occurrence count is a redundant
duplicate of the Fitch dimension-lock discipline.  Must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.HasTypeUnion.varSubjectIsFibrantlyAccessible
#assert_no_axioms FX1Poly.Typed.lockedDimensionVar_isNotFibrantlyTypeable

end FX1PolyAudit
