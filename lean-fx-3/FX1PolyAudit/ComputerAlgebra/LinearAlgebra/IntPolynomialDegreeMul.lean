import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialDegreeMul

/-! # FX1PolyAudit/.../IntPolynomialDegreeMul — zero-axiom gate

Per-declaration zero-axiom gate for the polynomial product-degree law (the WP-ENDO #2255 degree keystone):
`polyDegreeMul` (`deg(p·q) = deg p + deg q` over ℤ, both factors nonzero) via the top-coefficient identity
`polyCoeffMulTop` + ℤ no-zero-divisors, and the divisibility-degree corollary `polyDegreeDvdMono`
(`p·r = q, q ≠ 0 ⟹ deg p ≤ deg q`).  Distinct from the walled Cauchy–Binet route; unblocks the general
invariant-factor degree reasoning.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.polyCoeffMulLeftZero
#assert_no_axioms FX1Poly.ComputerAlgebra.polyCoeffMulVanish
#assert_no_axioms FX1Poly.ComputerAlgebra.polyCoeffMulTop
#assert_no_axioms FX1Poly.ComputerAlgebra.natLePredOfLt
#assert_no_axioms FX1Poly.ComputerAlgebra.polyDegreeGeOfCoeffNonzero
#assert_no_axioms FX1Poly.ComputerAlgebra.polyDegreeMul
#assert_no_axioms FX1Poly.ComputerAlgebra.polyDegreeDvdMono
#assert_no_axioms FX1Poly.ComputerAlgebra.polyDegreeMulBinomialExample
#assert_no_axioms FX1Poly.ComputerAlgebra.polyDegreeMulLinearFactorsExample
#assert_no_axioms FX1Poly.ComputerAlgebra.fxIntPoly_hasPolynomialDegreeMul

end FX1PolyAudit
