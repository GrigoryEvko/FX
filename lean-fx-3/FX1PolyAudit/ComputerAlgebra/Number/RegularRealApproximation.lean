import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.RegularRealApproximation

/-! # FX1PolyAudit/ComputerAlgebra/Number/RegularRealApproximation — zero-axiom
    gate (NUM-R-7a)

Per-declaration zero-axiom gate for rational density: the exactly-tight
constant-approximant bound, the rational approximation sequence, and
the round-trip through limit uniqueness.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.constantApproximantIsWithinReciprocal
#assert_no_axioms FX1Poly.ComputerAlgebra.rationalApproximationSequence
#assert_no_axioms FX1Poly.ComputerAlgebra.limitOfRationalApproximantsDenotesSelf

end FX1PolyAudit
