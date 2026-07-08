import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SetoidMatrixRing

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SetoidMatrixRing — zero-axiom gate

Per-declaration zero-axiom gate for the finite-sum toolkit, matrix multiplication, and the
multiplicative ring laws (congruence, associativity, distributivity, windowed identity).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.denotesSameOfEq
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.addZeroLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.selfAddIdempotentImpliesZero
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.mulZeroRight
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.zeroMulLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.oneMulLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.mulRightDistributesOverAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.iteOneZeroCondSymm
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.sumUpTo
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.sumUpToBoundCongr
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.sumUpToCongr
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.sumUpToZeroTerms
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.addFourRearrangeMiddle
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.sumUpToAdd
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.sumUpToMulRight
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.sumUpToMulLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.sumUpToSwap
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.sumUpToDeltaRightVanishes
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.sumUpToDeltaRightPicks
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.mulMatrix
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.mulMatrixRespectsDenoteSame
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.mulMatrixAssoc
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.mulMatrixLeftDistrib
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.mulMatrixRightDistrib
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.mulMatrixIdentityRightEntry
#assert_no_axioms FX1Poly.ComputerAlgebra.SetoidMatrix.mulMatrixIdentityLeftEntry

end FX1PolyAudit
