import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.RegularRealApproximation

/-! # FX1PolyAudit/ComputerAlgebra/Number/RegularRealApproximation — zero-axiom
    gate (NUM-R-7a/7b)

Per-declaration zero-axiom gate for rational density and the
Archimedean property: the exactly-tight constant-approximant bound,
the rational approximation sequence, the round-trip through limit
uniqueness, and the canonical-bound domination.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.constantApproximantIsWithinReciprocal
#assert_no_axioms FX1Poly.ComputerAlgebra.rationalApproximationSequence
#assert_no_axioms FX1Poly.ComputerAlgebra.limitOfRationalApproximantsDenotesSelf
#assert_no_axioms FX1Poly.ComputerAlgebra.realIsBelowItsCanonicalBound

end FX1PolyAudit
