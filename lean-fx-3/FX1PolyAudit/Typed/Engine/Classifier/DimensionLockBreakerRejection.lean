import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Engine.Classifier.DimensionLockBreakerRejection

/-! # FX1PolyAudit/.../DimensionLockBreakerRejection — zero-axiom gate

Per-declaration zero-axiom gate for the concrete rule-table SR-mechanism certificate: the SR-breaker
`pair (var 0) (var 0)` has, among the shipped `pairIntroRule`'s obligations, one that fails the fibrant
use-site usability conjunct under the affine lock.  Must be free of `propext`, `Quot.sound`, `Classical`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Typed.pairDuplicatingDimensionBodyRejectedByLock

end FX1PolyAudit
