import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialGcdFuelAdequate

/-! # FX1PolyAudit/.../IntPolynomialGcdFuelAdequate — zero-axiom gate

Per-declaration zero-axiom gate for the ℤ[x] GCD fuel-adequacy capstone (the nineteenth brick of
`invariantFactorSeparator`'s ℚ[x] arc, WP-ENDO #2255): the Euclidean step strictly shrinks the divisor's
trim-length (`polyGcdStepMeasureDecreases`), a computed fuel reaches the honest-termination branch
(`polyGcdReachesNilAdequateFuel`), and the converse root-containment holds **unconditionally** at that fuel
(`polyGcdAdequateFuelRootIffCommonRoot`) — the "polyGcd with adequate fuel = the actual gcd" wiring.

Structural budget recursion + uniform degree bound; r21/r30 measure drop; core Nat order arithmetic.  Must
be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.natLeSubOneAddOne
#assert_no_axioms FX1Poly.ComputerAlgebra.polyGcdStepMeasureDecreases
#assert_no_axioms FX1Poly.ComputerAlgebra.polyGcdReachesNilOfBudget
#assert_no_axioms FX1Poly.ComputerAlgebra.polyGcdReachesNilAdequateFuel
#assert_no_axioms FX1Poly.ComputerAlgebra.polyGcdAdequateFuelRootIffCommonRoot
#assert_no_axioms FX1Poly.ComputerAlgebra.polyGcdReachesNilAdequateFuelGrounding
#assert_no_axioms FX1Poly.ComputerAlgebra.fxIntPoly_hasGcdFuelAdequacy

end FX1PolyAudit
