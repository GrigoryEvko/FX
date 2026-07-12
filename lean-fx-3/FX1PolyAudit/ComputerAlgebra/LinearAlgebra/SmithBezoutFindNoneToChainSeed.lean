import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithBezoutFindNoneToChainSeed

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithBezoutFindNoneToChainSeed — zero-axiom gate
    (H2-SMITH r49, #2261 — the word-agnostic ARC-C seed reduction + lo-monotonicity + the recorded
    ARC-A residuals (α)/(β); the mandate stays honestly UNINHABITED)

Per-declaration zero-axiom gate for the r49 file: the sub-block ideal lo-monotonicity
(`matrixEntriesDivisibleByWithinLoMonotone`), the word-agnostic ARC-C seed reduction
(`smithBezoutFindNoneImpliesLandsDivisibleSubBlock`), the two recorded ARC-A residual Props
(`SmithBezoutRepairRoundLandsPivotPositiveStatement`,
`SmithBezoutTrailingCascadePreservesFindNoneStatement`), and the (α)/(β) honesty `decide` pins.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`.  Both the fuel-based `#assert_no_axioms` AND the independent (non-fuel) `#print axioms` are run
on every declaration (the project macro is fuel-based — not trusted alone). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.matrixEntriesDivisibleByWithinLoMonotone
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBezoutFindNoneImpliesLandsDivisibleSubBlock
#assert_no_axioms FX1Poly.ComputerAlgebra.SmithBezoutRepairRoundLandsPivotPositiveStatement
#assert_no_axioms FX1Poly.ComputerAlgebra.SmithBezoutTrailingCascadePreservesFindNoneStatement
#assert_no_axioms FX1Poly.ComputerAlgebra.alphaZeroPivotRoundLandsPivotPositive
#assert_no_axioms FX1Poly.ComputerAlgebra.alphaZeroPivotRoundReEstablishesCleanCross
#assert_no_axioms FX1Poly.ComputerAlgebra.alphaZeroPivotWideRoundLandsPivotPositive
#assert_no_axioms FX1Poly.ComputerAlgebra.alphaZeroPivotWideRoundReEstablishesCleanCross
#assert_no_axioms FX1Poly.ComputerAlgebra.betaFindNoneDiagBefore
#assert_no_axioms FX1Poly.ComputerAlgebra.betaFindNoneDiagTrailingCascadePreservesFindNone
#assert_no_axioms FX1Poly.ComputerAlgebra.betaFindNoneSingletonBefore
#assert_no_axioms FX1Poly.ComputerAlgebra.betaFindNoneSingletonTrailingCascadePreservesFindNone
#assert_no_axioms FX1Poly.ComputerAlgebra.betaFindNoneTripleBefore
#assert_no_axioms FX1Poly.ComputerAlgebra.betaFindNoneTripleTrailingCascadePreservesFindNone
#assert_no_axioms FX1Poly.ComputerAlgebra.betaFindNoneDiagBezoutSweepLandedFindNone

-- Independent (non-fuel) axiom prints on every declaration.
#print axioms FX1Poly.ComputerAlgebra.matrixEntriesDivisibleByWithinLoMonotone
#print axioms FX1Poly.ComputerAlgebra.smithBezoutFindNoneImpliesLandsDivisibleSubBlock
#print axioms FX1Poly.ComputerAlgebra.SmithBezoutRepairRoundLandsPivotPositiveStatement
#print axioms FX1Poly.ComputerAlgebra.SmithBezoutTrailingCascadePreservesFindNoneStatement
#print axioms FX1Poly.ComputerAlgebra.alphaZeroPivotRoundLandsPivotPositive
#print axioms FX1Poly.ComputerAlgebra.alphaZeroPivotRoundReEstablishesCleanCross
#print axioms FX1Poly.ComputerAlgebra.alphaZeroPivotWideRoundLandsPivotPositive
#print axioms FX1Poly.ComputerAlgebra.alphaZeroPivotWideRoundReEstablishesCleanCross
#print axioms FX1Poly.ComputerAlgebra.betaFindNoneDiagBefore
#print axioms FX1Poly.ComputerAlgebra.betaFindNoneDiagTrailingCascadePreservesFindNone
#print axioms FX1Poly.ComputerAlgebra.betaFindNoneSingletonBefore
#print axioms FX1Poly.ComputerAlgebra.betaFindNoneSingletonTrailingCascadePreservesFindNone
#print axioms FX1Poly.ComputerAlgebra.betaFindNoneTripleBefore
#print axioms FX1Poly.ComputerAlgebra.betaFindNoneTripleTrailingCascadePreservesFindNone
#print axioms FX1Poly.ComputerAlgebra.betaFindNoneDiagBezoutSweepLandedFindNone

end FX1PolyAudit
