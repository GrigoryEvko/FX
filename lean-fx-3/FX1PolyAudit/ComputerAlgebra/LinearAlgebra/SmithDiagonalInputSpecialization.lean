import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithDiagonalInputSpecialization

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithDiagonalInputSpecialization — zero-axiom gate
    (H2-SMITH r24, #2261 — the diagonal-input specialization + pairwise gcd)

Per-declaration zero-axiom gate for the diagonal-input keystone specialization, the pairwise-gcd
contract, the iterated-pairwise-gcd common-divisor fact, and the re-plumb refutation witness.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

/- BRICK 1 — the pairwise-gcd eval truth-probes + the reusable contract. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.intGcdFifteenTen
#assert_no_axioms FX1Poly.ComputerAlgebra.intGcdSixTen
#assert_no_axioms FX1Poly.ComputerAlgebra.intGcdZeroFour
#assert_no_axioms FX1Poly.ComputerAlgebra.intGcdNegSixNegFour
#assert_no_axioms FX1Poly.ComputerAlgebra.intGcdSixNegFour
#assert_no_axioms FX1Poly.ComputerAlgebra.intGcdNegFifteenTen
#assert_no_axioms FX1Poly.ComputerAlgebra.IntPairwiseGcdSpec
#assert_no_axioms FX1Poly.ComputerAlgebra.intGcdSatisfiesPairwiseSpec

/- BRICK 2 — the diagonal-input narrowing + the pivot-0 discharge + the re-plumb refutation. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.subBlockOffDiagonalDivisibleOfWindowDiagonal
#assert_no_axioms FX1Poly.ComputerAlgebra.matrixEntriesDivisibleByWithinOfDiagonalInput
#assert_no_axioms FX1Poly.ComputerAlgebra.SmithDiagonalInputLandedPivotDividesDiagonal
#assert_no_axioms FX1Poly.ComputerAlgebra.landedPivotDividesMinorOnDiagonalInput
#assert_no_axioms FX1Poly.ComputerAlgebra.phaseAOutputIsWindowDiagonalAtZero
#assert_no_axioms FX1Poly.ComputerAlgebra.smithDiagonalInputReplumbFixture
#assert_no_axioms FX1Poly.ComputerAlgebra.smithDiagonalInputPivotOneInputNotWindowDiagonal

end FX1PolyAudit
