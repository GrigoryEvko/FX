import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.Number.ComplexRealModulus

/-! # FX1PolyAudit/ComputerAlgebra/Number/ComplexRealModulus — zero-axiom gate

Per-declaration zero-axiom gate for the Gaussian-real modulus: the sign-blind
square-nonneg lemmas, the pointwise-nonneg helpers, the squared modulus and its
nonnegativity, the `z * conj z ~ |z|²` identity, the modulus, and the square
law.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.intMulSelfNonNegative
#assert_no_axioms FX1Poly.ComputerAlgebra.mulExactSelfIsNonNegative
#assert_no_axioms FX1Poly.ComputerAlgebra.mulRealSelfIsNonNegativeReal
#assert_no_axioms FX1Poly.ComputerAlgebra.addRealPreservesIsNonNegativeReal
#assert_no_axioms FX1Poly.ComputerAlgebra.modulusSquared
#assert_no_axioms FX1Poly.ComputerAlgebra.modulusSquaredIsNonNegativeReal
#assert_no_axioms FX1Poly.ComputerAlgebra.mulComplexConjDenotesModulusSquared
#assert_no_axioms FX1Poly.ComputerAlgebra.modulus
#assert_no_axioms FX1Poly.ComputerAlgebra.modulusSquareDenotesModulusSquared

end FX1PolyAudit
