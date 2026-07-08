import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SetoidMatrix

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SetoidMatrix — zero-axiom gate

Per-declaration zero-axiom gate for the generic setoid-matrix carrier, its setoid-equality trio,
the additive/scalar/transpose operations, their congruences, and the additive abelian-group +
scalar + transpose laws over an arbitrary `CommutativeRingWitness`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.DenoteSame
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.denoteSameRefl
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.denoteSameSymm
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.denoteSameTrans
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.zeroMatrix
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.identityMatrix
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.addMatrix
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.negMatrix
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.subMatrix
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.scalarMul
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.transposeMatrix
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.addMatrixRespectsDenoteSame
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.negMatrixRespectsDenoteSame
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.subMatrixRespectsDenoteSame
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.scalarMulRespectsDenoteSame
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.transposeMatrixRespectsDenoteSame
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.addMatrixComm
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.addMatrixAssoc
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.addMatrixZeroRight
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.addMatrixNegRight
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.subMatrixSelf
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.scalarMulDistributesOverAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.scalarMulOne
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.transposeMatrixInvolutive
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.transposeMatrixOfAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.transposeIdentityMatrix

end FX1PolyAudit
