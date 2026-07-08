import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SetoidDeterminant

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SetoidDeterminant — zero-axiom gate

Per-declaration zero-axiom gate for the exact cofactor determinant: the minor, the alternating
sign, the determinant itself, its setoid congruence, the base cases, and `det I = 1`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.mulSwapLastTwo
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.iteSuccCondCollapse
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.minorFirstRow
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.signAlternating
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.cofactorDet
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.minorFirstRowRespects
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.cofactorDetCongr
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.cofactorDetZeroSize
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.cofactorDetOneSize
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.minorFirstRowOfIdentity
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.cofactorDetIdentity

end FX1PolyAudit
