import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.IntPolynomialDivision

/-! # FX1PolyAudit/.../IntPolynomialDivision — zero-axiom gate

Per-declaration zero-axiom gate for the ℤ[x] monic division-with-remainder layer (the third brick of
`invariantFactorSeparator`'s ℚ[x] arc, WP-ENDO #2255): the `Int` cancellation helpers, the division
algorithm, and the fuel-independent reconstruction identity
`dividend = quotient · divisor + remainder`.

The recursion is structural on `fuel`; the only non-list case analysis is `Nat.decLt` on its full
`isTrue`/`isFalse` enumeration; the proof's `dsimp only`/`cases` are over data.  Must be free of `propext`,
`Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.intAddSubCancel
#assert_no_axioms FX1Poly.ComputerAlgebra.polyDivStepArith
#assert_no_axioms FX1Poly.ComputerAlgebra.polyDivModMonic
#assert_no_axioms FX1Poly.ComputerAlgebra.polyDivModMonicReconstructs
#assert_no_axioms FX1Poly.ComputerAlgebra.polyDividesMonicEvalMultiple
#assert_no_axioms FX1Poly.ComputerAlgebra.polyDivModMonicDifferenceOfSquares
#assert_no_axioms FX1Poly.ComputerAlgebra.polyDivModMonicRemainderExample
#assert_no_axioms FX1Poly.ComputerAlgebra.polyDivModMonicReconstructsGroundingAtFour
#assert_no_axioms FX1Poly.ComputerAlgebra.polyLinearFactorDividesDifferenceOfSquares
#assert_no_axioms FX1Poly.ComputerAlgebra.polyDividesMonicEvalMultipleGroundingAtSeven
#assert_no_axioms FX1Poly.ComputerAlgebra.fxIntPoly_hasMonicDivisionReconstruction

end FX1PolyAudit
