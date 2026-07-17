import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialPseudoRemFuelStable

/-! # FX1PolyAudit/.../IntPolynomialPseudoRemFuelStable — zero-axiom gate

Per-declaration zero-axiom gate for the adequate-fuel pseudo-remainder stability (the fifteenth brick of
`invariantFactorSeparator`'s ℚ[x] arc, WP-ENDO #2255): for a non-constant divisor, extra fuel leaves the
pseudo-remainder unchanged once fuel is adequate (`polyPseudoRemFuelStableNonconstant`), the fuel-monotonicity
lynchpin of the Euclidean GCD's fuel-adequacy wiring.

Structural fuel recursion; guard `Nat.decLt`; `Nat.add_right_comm` + core Nat order lemmas + r20 step
degree-decrease.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.polyPseudoRemFuelStableNonconstant
#assert_no_axioms FX1Poly.ComputerAlgebra.polyPseudoRemFuelStableGrounding
#assert_no_axioms FX1Poly.ComputerAlgebra.fxIntPoly_hasPseudoRemainderFuelStability

end FX1PolyAudit
