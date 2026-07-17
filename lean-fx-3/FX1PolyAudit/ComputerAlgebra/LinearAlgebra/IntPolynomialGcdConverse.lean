import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialGcdConverse

/-! # FX1PolyAudit/.../IntPolynomialGcdConverse — zero-axiom gate

Per-declaration zero-axiom gate for the single Euclidean-step converse (the twelfth brick of
`invariantFactorSeparator`'s ℚ[x] arc, WP-ENDO #2255): a root of both the divisor and the pseudo-remainder
is a root of the dividend, cancelling the `leadDivisor^scalePower` factor off the r10 reconstruction via the
r22 arbitrary-sign ℤ no-zero-divisor.

Reconstruction identity + ℤ no-zero-divisor, no case analysis.  Must be free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.polyPseudoRemBackwardRoot
#assert_no_axioms FX1Poly.ComputerAlgebra.polyPseudoRemBackwardRootGrounding
#assert_no_axioms FX1Poly.ComputerAlgebra.fxIntPoly_hasPseudoRemainderBackwardRoot

end FX1PolyAudit
