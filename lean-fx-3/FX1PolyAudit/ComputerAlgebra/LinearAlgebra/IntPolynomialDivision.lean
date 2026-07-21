import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialDivision

/-! # FX1PolyAudit/.../IntPolynomialDivision — zero-axiom gate

Per-declaration zero-axiom gate for the ℤ[x] division layer: the `Int` cancellation helpers, the monic and
pseudo division algorithms, and the fuel-independent reconstruction identities.  Structural recursion on
`fuel`; the only non-list case analysis is `Nat.decLt`.  Free of `propext`, `Quot.sound`, `Classical`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.intAddSubCancel
#assert_no_axioms FX1Poly.ComputerAlgebra.polyDivStepArith
#assert_no_axioms FX1Poly.ComputerAlgebra.polyDivModMonic
#assert_no_axioms FX1Poly.ComputerAlgebra.polyDivModMonicReconstructs
#assert_no_axioms FX1Poly.ComputerAlgebra.polyDividesMonicEvalMultiple
#assert_no_axioms FX1Poly.ComputerAlgebra.intMulSubDistrib
#assert_no_axioms FX1Poly.ComputerAlgebra.polyPseudoDivStepArith
#assert_no_axioms FX1Poly.ComputerAlgebra.polyPseudoDivMod
#assert_no_axioms FX1Poly.ComputerAlgebra.polyPseudoDivModReconstructs
#assert_no_axioms FX1Poly.ComputerAlgebra.polyDivModMonicDifferenceOfSquares
#assert_no_axioms FX1Poly.ComputerAlgebra.polyDivModMonicRemainderExample
#assert_no_axioms FX1Poly.ComputerAlgebra.polyDivModMonicReconstructsGroundingAtFour
#assert_no_axioms FX1Poly.ComputerAlgebra.polyLinearFactorDividesDifferenceOfSquares
#assert_no_axioms FX1Poly.ComputerAlgebra.polyDividesMonicEvalMultipleGroundingAtSeven
#assert_no_axioms FX1Poly.ComputerAlgebra.polyPseudoDivModDividesExactly
#assert_no_axioms FX1Poly.ComputerAlgebra.polyPseudoDivModReconstructsGroundingAtFive
#assert_no_axioms FX1Poly.ComputerAlgebra.fxIntPoly_hasMonicDivisionReconstruction

end FX1PolyAudit
