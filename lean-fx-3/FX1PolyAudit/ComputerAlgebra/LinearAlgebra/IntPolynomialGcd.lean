import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialGcd

/-! # FX1PolyAudit/.../IntPolynomialGcd — zero-axiom gate

Per-declaration zero-axiom gate for the ℤ[x] Euclidean GCD via pseudo-division: the pseudo-remainder, the
GCD algorithm, and the theorems that both vanish at every common root of their inputs.  Structural recursion
on `fuel`; `polyTrim` `nil`/`cons` case analysis; corpus `Int` lemmas.  Free of `propext`, `Quot.sound`,
`Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.polyPseudoRem
#assert_no_axioms FX1Poly.ComputerAlgebra.polyGcd
#assert_no_axioms FX1Poly.ComputerAlgebra.polyPseudoRemVanishesAtCommonRoot
#assert_no_axioms FX1Poly.ComputerAlgebra.polyGcdVanishesAtCommonRoot
#assert_no_axioms FX1Poly.ComputerAlgebra.polyGcdRightZero
#assert_no_axioms FX1Poly.ComputerAlgebra.polyGcdSeesSharedLinearFactor
#assert_no_axioms FX1Poly.ComputerAlgebra.polyGcdSharesCommonRootAtMinusOne
#assert_no_axioms FX1Poly.ComputerAlgebra.polyPseudoRemSharesCommonRootAtMinusOne
#assert_no_axioms FX1Poly.ComputerAlgebra.polyGcdExtractsCommonFactorDegree
#assert_no_axioms FX1Poly.ComputerAlgebra.polyGcdSeesSharedEigenvalueAtTwo

end FX1PolyAudit
