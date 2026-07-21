import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialConstDivisorNil

/-! # FX1PolyAudit/.../IntPolynomialConstDivisorNil — zero-axiom gate

Per-declaration zero-axiom gate for the constant-divisor pseudo-remainder → nil: pseudo-dividing any
dividend by a nonzero constant divisor yields a zero remainder with adequate fuel
(`polyPseudoRemConstantTrimsNil`), so the GCD's coprime tail reaches nil.  Structural fuel recursion +
degree-value case split; the constant-divisor step decrease, the zero-polynomial cascade, coefficient
homomorphisms.  Free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.polyPseudoRemConstantTrimsNil
#assert_no_axioms FX1Poly.ComputerAlgebra.polyPseudoRemConstantTrimsNilGrounding

end FX1PolyAudit
