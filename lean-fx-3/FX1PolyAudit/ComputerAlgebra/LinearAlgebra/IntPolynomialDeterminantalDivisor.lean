import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialDeterminantalDivisor

/-! # FX1PolyAudit/.../IntPolynomialDeterminantalDivisor — zero-axiom gate

Per-declaration zero-axiom gate for the first determinantal divisor `d₁` and its similarity separation
(the third brick of the char-matrix → invariant-factors layer, WP-ENDO #2255): the ℤ[x] GCD fold
(`polyGcdList`) over the `1×1` minors of `x·I − M` computes `d₁` (`charMatrixDivisorOne`), whose degree
is a decidable similarity invariant separating the derogatory scalar `2·I` (`deg d₁ = 1`) from the
cyclic Jordan block `[[2,1],[0,2]]` (`deg d₁ = 0`) — matrices with equal characteristic polynomial
`(x−2)²`, so trace/determinant/char-poly are blind.

GCD fold (structural on fuel) + `decide` groundings + a `Nat` degree inequality.  Must be free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.polyGcdList
#assert_no_axioms FX1Poly.ComputerAlgebra.charMatrixDivisorOne
#assert_no_axioms FX1Poly.ComputerAlgebra.charMatrixDivisorOneScalarDegreeOne
#assert_no_axioms FX1Poly.ComputerAlgebra.charMatrixDivisorOneJordanDegreeZero
#assert_no_axioms FX1Poly.ComputerAlgebra.charMatrixDivisorOneDiagDistinctDegreeZero
#assert_no_axioms FX1Poly.ComputerAlgebra.scalarAndJordanShareCharPoly
#assert_no_axioms FX1Poly.ComputerAlgebra.DissimilarByDivisorOneDegree
#assert_no_axioms FX1Poly.ComputerAlgebra.scalarNotSimilarToJordanByDivisorOne
#assert_no_axioms FX1Poly.ComputerAlgebra.fxIntPoly_hasFirstDeterminantalDivisor

end FX1PolyAudit
