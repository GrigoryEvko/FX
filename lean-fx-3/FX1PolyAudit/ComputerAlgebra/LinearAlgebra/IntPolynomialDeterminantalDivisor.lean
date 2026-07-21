import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialDeterminantalDivisor

/-! # FX1PolyAudit/.../IntPolynomialDeterminantalDivisor — zero-axiom gate

Per-declaration zero-axiom gate for the first determinantal divisor `d₁` and its similarity separation: the
ℤ[x] GCD fold (`polyGcdList`) over the `1×1` minors of `x·I − M` computes `d₁` (`charMatrixDivisorOne`),
whose degree is a decidable similarity invariant separating the derogatory scalar `2·I` (`deg d₁ = 1`) from
the cyclic Jordan block `[[2,1],[0,2]]` (`deg d₁ = 0`), which share char poly `(x−2)²`.  GCD fold + `decide`
groundings + a `Nat` degree inequality.  Free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.polyGcdList
#assert_no_axioms FX1Poly.ComputerAlgebra.charMatrixDivisorOne
#assert_no_axioms FX1Poly.ComputerAlgebra.charMatrixDivisorOneScalarDegreeOne
#assert_no_axioms FX1Poly.ComputerAlgebra.charMatrixDivisorOneJordanDegreeZero
#assert_no_axioms FX1Poly.ComputerAlgebra.charMatrixDivisorOneDiagDistinctDegreeZero
#assert_no_axioms FX1Poly.ComputerAlgebra.scalarAndJordanShareCharPoly
#assert_no_axioms FX1Poly.ComputerAlgebra.DissimilarByDivisorOneDegree
#assert_no_axioms FX1Poly.ComputerAlgebra.scalarNotSimilarToJordanByDivisorOne

end FX1PolyAudit
