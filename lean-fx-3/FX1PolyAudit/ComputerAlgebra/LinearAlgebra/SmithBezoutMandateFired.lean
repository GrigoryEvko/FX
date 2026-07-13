import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithBezoutMandateFired

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithBezoutMandateFired — zero-axiom gate
    (H2-SMITH r50, #2261 — THE MANDATE FIRED: `SmithReduceCompleteBezoutDriverStatement` INHABITED)

Per-declaration zero-axiom gate for the mandate-firing file: the Bezout freeze/band twins, the
settled-frame step and outer fold, the carried chain invariant and its fold, the two gate conjuncts
(`repairWindowDiagHoldsForBezout` / `repairChainHoldsForBezout`), the gate inhabitant
(`smithBezoutRepairInvariantsHold`), and THE MANDATE (`smithReduceCompleteBezoutDriverHolds`).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`.  Both the fuel-based `#assert_no_axioms` AND the independent (non-fuel)
`#print axioms` are run on every declaration (the project macro is fuel-based — not trusted alone). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.smithBezoutRepairRoundWordAtFoundFreezesBelow
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBezoutRepairPositionSweepFreezesBelow
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBezoutRepairRoundWordAtFoundPreservesRowBandZero
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBezoutRepairRoundWordAtFoundPreservesColBandZero
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBezoutRepairPositionSweepPreservesRowBandZero
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBezoutRepairPositionSweepPreservesColBandZero
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBezoutRepairPositionSweepSeedStepSettles
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBezoutDivisibilityRepairSweepSucc
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBezoutDivisibilityRepairSweepSettlesThroughPivots
#assert_no_axioms FX1Poly.ComputerAlgebra.repairWindowDiagHoldsForBezout
#assert_no_axioms FX1Poly.ComputerAlgebra.SmithBezoutSettledDiagonalsDivideAdvancedBlocks
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBezoutDivisibilityRepairSweepCarriesChain
#assert_no_axioms FX1Poly.ComputerAlgebra.repairChainHoldsForBezout
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBezoutRepairInvariantsHold
#assert_no_axioms FX1Poly.ComputerAlgebra.smithReduceCompleteBezoutDriverHolds
#assert_no_axioms FX1Poly.ComputerAlgebra.mandateProbeDiagonal
#assert_no_axioms FX1Poly.ComputerAlgebra.mandateProbeCoprime
#assert_no_axioms FX1Poly.ComputerAlgebra.mandateProbeDense
#assert_no_axioms FX1Poly.ComputerAlgebra.mandateProbeZeroPivot
#assert_no_axioms FX1Poly.ComputerAlgebra.mandateProbeKiller
#assert_no_axioms FX1Poly.ComputerAlgebra.mandateProbeWide
#assert_no_axioms FX1Poly.ComputerAlgebra.mandateProbeTall
#assert_no_axioms FX1Poly.ComputerAlgebra.mandateProbeNegative

-- Independent (non-fuel) axiom prints on every declaration.
#print axioms FX1Poly.ComputerAlgebra.smithBezoutRepairRoundWordAtFoundFreezesBelow
#print axioms FX1Poly.ComputerAlgebra.smithBezoutRepairPositionSweepFreezesBelow
#print axioms FX1Poly.ComputerAlgebra.smithBezoutRepairRoundWordAtFoundPreservesRowBandZero
#print axioms FX1Poly.ComputerAlgebra.smithBezoutRepairRoundWordAtFoundPreservesColBandZero
#print axioms FX1Poly.ComputerAlgebra.smithBezoutRepairPositionSweepPreservesRowBandZero
#print axioms FX1Poly.ComputerAlgebra.smithBezoutRepairPositionSweepPreservesColBandZero
#print axioms FX1Poly.ComputerAlgebra.smithBezoutRepairPositionSweepSeedStepSettles
#print axioms FX1Poly.ComputerAlgebra.smithBezoutDivisibilityRepairSweepSucc
#print axioms FX1Poly.ComputerAlgebra.smithBezoutDivisibilityRepairSweepSettlesThroughPivots
#print axioms FX1Poly.ComputerAlgebra.repairWindowDiagHoldsForBezout
#print axioms FX1Poly.ComputerAlgebra.SmithBezoutSettledDiagonalsDivideAdvancedBlocks
#print axioms FX1Poly.ComputerAlgebra.smithBezoutDivisibilityRepairSweepCarriesChain
#print axioms FX1Poly.ComputerAlgebra.repairChainHoldsForBezout
#print axioms FX1Poly.ComputerAlgebra.smithBezoutRepairInvariantsHold
#print axioms FX1Poly.ComputerAlgebra.smithReduceCompleteBezoutDriverHolds
#print axioms FX1Poly.ComputerAlgebra.mandateProbeDiagonal
#print axioms FX1Poly.ComputerAlgebra.mandateProbeCoprime
#print axioms FX1Poly.ComputerAlgebra.mandateProbeDense
#print axioms FX1Poly.ComputerAlgebra.mandateProbeZeroPivot
#print axioms FX1Poly.ComputerAlgebra.mandateProbeKiller
#print axioms FX1Poly.ComputerAlgebra.mandateProbeWide
#print axioms FX1Poly.ComputerAlgebra.mandateProbeTall
#print axioms FX1Poly.ComputerAlgebra.mandateProbeNegative

end FX1PolyAudit
