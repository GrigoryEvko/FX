import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialCharMinors

/-! # FX1PolyAudit/.../IntPolynomialCharMinors — zero-axiom gate

Per-declaration zero-axiom gate for the ℤ[x] characteristic-matrix minors: the carrier-generic minor
selector (`SetoidMatrix.submatrixByIndex`/`minorDet`) instantiated at the polynomial ring witness computes
any `k×k` minor of `x·I − M` as a genuine ℤ[x] polynomial (`charMatrixMinor`), the raw ingredient of the
determinantal divisors.  Structure literals + generic `cofactorDet` + `decide` groundings.  Free of
`propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

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

end FX1PolyAudit
