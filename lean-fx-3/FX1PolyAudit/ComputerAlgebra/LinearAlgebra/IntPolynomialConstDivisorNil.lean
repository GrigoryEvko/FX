import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialConstDivisorNil

/-! # FX1PolyAudit/.../IntPolynomialConstDivisorNil — zero-axiom gate

Per-declaration zero-axiom gate for the constant-divisor pseudo-remainder → nil (the eighteenth brick of
`invariantFactorSeparator`'s ℚ[x] arc, WP-ENDO #2255): pseudo-dividing any dividend by a nonzero constant
divisor yields a zero remainder with adequate fuel (`polyPseudoRemConstantTrimsNil`), assembling r28's
constant-divisor step decrease with r29's zero-polynomial persistence — the GCD's coprime tail reaches nil.

Structural fuel recursion + degree-value case split; r28/r29 + coefficient homomorphisms + r16.  Must be free
of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.polyPseudoRemConstantTrimsNil
#assert_no_axioms FX1Poly.ComputerAlgebra.polyPseudoRemConstantTrimsNilGrounding
#assert_no_axioms FX1Poly.ComputerAlgebra.fxIntPoly_hasConstantDivisorRemainderNil

end FX1PolyAudit
