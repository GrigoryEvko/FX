import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialCharMinors

/-! # FX1PolyAudit/.../IntPolynomialCharMinors — zero-axiom gate

Per-declaration zero-axiom gate for the ℤ[x] characteristic-matrix minors (the second brick of the
char-matrix → invariant-factors layer, WP-ENDO #2255): the carrier-generic minor selector
(`SetoidMatrix.submatrixByIndex`/`minorDet`) instantiated at the polynomial ring witness computes any
`k×k` minor of `x·I − M` as a genuine ℤ[x] polynomial (`charMatrixMinor`), the raw ingredient of the
determinantal divisors.  The off-diagonal 1×1 minor already separates the scalar `2·I` from the Jordan
block that shares its characteristic polynomial.

Structure literals + generic `cofactorDet` + `decide` groundings.  Must be free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.submatrixByIndex
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.minorDet
#assert_no_axioms FX1Poly.ComputerAlgebra.charMatrixMinor
#assert_no_axioms FX1Poly.ComputerAlgebra.twoByTwoMatrix
#assert_no_axioms FX1Poly.ComputerAlgebra.charMatrixMinorDiagTopLeftIsXMinusTwo
#assert_no_axioms FX1Poly.ComputerAlgebra.charMatrixMinorDiagBottomRightIsXMinusThree
#assert_no_axioms FX1Poly.ComputerAlgebra.charMatrixMinorDiagFullIsCharPoly
#assert_no_axioms FX1Poly.ComputerAlgebra.charMatrixMinorJordanOffDiagIsUnit
#assert_no_axioms FX1Poly.ComputerAlgebra.charMatrixMinorScalarOffDiagIsZero
#assert_no_axioms FX1Poly.ComputerAlgebra.fxIntPoly_hasCharMatrixMinors

end FX1PolyAudit
