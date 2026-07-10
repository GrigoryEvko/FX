import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithNormalForm

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithNormalForm — zero-axiom gate (H2-SMITH r1)

Per-declaration zero-axiom gate for the ZZ Smith driver + certificates: the certified-gcd
interface and its integer instance, the operation-inverse kit, the elimination driver, and the
non-vacuity theorems (driver-produced and diagonal SNF certificates, including the `Z/2`
homology-with-torsion seed).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.CertifiedGcd
#assert_no_axioms FX1Poly.ComputerAlgebra.intCertifiedGcd
#assert_no_axioms FX1Poly.ComputerAlgebra.inverseRowOperation
#assert_no_axioms FX1Poly.ComputerAlgebra.inverseColumnOperation
#assert_no_axioms FX1Poly.ComputerAlgebra.inverseOperation
#assert_no_axioms FX1Poly.ComputerAlgebra.reverseOperationWord
#assert_no_axioms FX1Poly.ComputerAlgebra.listMapNegNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.listModifyAtNegNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.negateRowInvolutive
#assert_no_axioms FX1Poly.ComputerAlgebra.addScaledEntriesCancel
#assert_no_axioms FX1Poly.ComputerAlgebra.intPivotQuotient
#assert_no_axioms FX1Poly.ComputerAlgebra.smithClearRowRightSteps
#assert_no_axioms FX1Poly.ComputerAlgebra.smithClearColumnBelowSteps
#assert_no_axioms FX1Poly.ComputerAlgebra.smithReduceSweep
#assert_no_axioms FX1Poly.ComputerAlgebra.smithReduce
#assert_no_axioms FX1Poly.ComputerAlgebra.smithExampleTorsionDiagonal
#assert_no_axioms FX1Poly.ComputerAlgebra.smithReducedUpperTriangular
#assert_no_axioms FX1Poly.ComputerAlgebra.smithReducedDenseTwo
#assert_no_axioms FX1Poly.ComputerAlgebra.smithExampleChainThree
#assert_no_axioms FX1Poly.ComputerAlgebra.smithExampleCyclicTwo
#assert_no_axioms FX1Poly.ComputerAlgebra.smithRotationDecreasesPivotSize
#assert_no_axioms FX1Poly.ComputerAlgebra.smithReducedEuclideanRow
#assert_no_axioms FX1Poly.ComputerAlgebra.smithReducedSignedDiagonal
#assert_no_axioms FX1Poly.ComputerAlgebra.smithReducedRankDeficient

end FX1PolyAudit
