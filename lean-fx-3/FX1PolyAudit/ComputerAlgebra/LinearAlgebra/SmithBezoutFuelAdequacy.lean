import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithBezoutFuelAdequacy

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithBezoutFuelAdequacy — zero-axiom gate
    (H2-SMITH r50, #2261 — ARC-A discharged: (α), (β), and the fuel-adequacy residual INHABITED)

Per-declaration zero-axiom gate for the ARC-A discharge file: the divisibility micro-kit, the
cascade-output non-vanishing lever (`smithCascadeSweepOutputPivotNonzero`), the inhabitants of (α)
(`smithBezoutRepairRoundLandsPivotPositiveHolds`), (β)
(`smithBezoutTrailingCascadePreservesFindNoneHolds`), the dirty-tolerant first-round bound, the
gcd-floored master fuel induction, and the ARC-A seed theorem + residual inhabitation
(`smithBezoutRepairPositionSweepReachesFindNoneHolds`).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`.  Both the fuel-based `#assert_no_axioms` AND the independent (non-fuel)
`#print axioms` are run on every declaration (the project macro is fuel-based — not trusted alone). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.dividesExactlySelf
#assert_no_axioms FX1Poly.ComputerAlgebra.dividesExactlyZeroDivisorForcesZero
#assert_no_axioms FX1Poly.ComputerAlgebra.dividesExactlyNegDivisor
#assert_no_axioms FX1Poly.ComputerAlgebra.natLeMulOfPosRight
#assert_no_axioms FX1Poly.ComputerAlgebra.dividesExactlyNonzeroLowerBoundsMagnitude
#assert_no_axioms FX1Poly.ComputerAlgebra.intEqOrNegOfNatAbsEqOfNonneg
#assert_no_axioms FX1Poly.ComputerAlgebra.addRowMultipleSelfIsIdentity
#assert_no_axioms FX1Poly.ComputerAlgebra.addColumnMultipleSelfIsIdentity
#assert_no_axioms FX1Poly.ComputerAlgebra.smithCascadeSweepSeedFuelBound
#assert_no_axioms FX1Poly.ComputerAlgebra.smithCascadeSweepOutputPivotNonzero
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBezoutTrailingCascadePreservesFindNoneHolds
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBezoutRepairRoundLandsPivotPositiveHolds
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBezoutRepairRoundAtFoundPivotMagnitudeLeMinorAbsSum
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBezoutRepairRoundWordAtFoundApplied
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBezoutRepairPositionSweepSucc
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBezoutRepairPositionSweepMasterLandsFindNoneAndCrossClear
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBezoutRepairPositionSweepSeedLandsFindNoneAndCrossClear
#assert_no_axioms FX1Poly.ComputerAlgebra.smithBezoutRepairPositionSweepReachesFindNoneHolds

-- Independent (non-fuel) axiom prints on every declaration.
#print axioms FX1Poly.ComputerAlgebra.dividesExactlySelf
#print axioms FX1Poly.ComputerAlgebra.dividesExactlyZeroDivisorForcesZero
#print axioms FX1Poly.ComputerAlgebra.dividesExactlyNegDivisor
#print axioms FX1Poly.ComputerAlgebra.natLeMulOfPosRight
#print axioms FX1Poly.ComputerAlgebra.dividesExactlyNonzeroLowerBoundsMagnitude
#print axioms FX1Poly.ComputerAlgebra.intEqOrNegOfNatAbsEqOfNonneg
#print axioms FX1Poly.ComputerAlgebra.addRowMultipleSelfIsIdentity
#print axioms FX1Poly.ComputerAlgebra.addColumnMultipleSelfIsIdentity
#print axioms FX1Poly.ComputerAlgebra.smithCascadeSweepSeedFuelBound
#print axioms FX1Poly.ComputerAlgebra.smithCascadeSweepOutputPivotNonzero
#print axioms FX1Poly.ComputerAlgebra.smithBezoutTrailingCascadePreservesFindNoneHolds
#print axioms FX1Poly.ComputerAlgebra.smithBezoutRepairRoundLandsPivotPositiveHolds
#print axioms FX1Poly.ComputerAlgebra.smithBezoutRepairRoundAtFoundPivotMagnitudeLeMinorAbsSum
#print axioms FX1Poly.ComputerAlgebra.smithBezoutRepairRoundWordAtFoundApplied
#print axioms FX1Poly.ComputerAlgebra.smithBezoutRepairPositionSweepSucc
#print axioms FX1Poly.ComputerAlgebra.smithBezoutRepairPositionSweepMasterLandsFindNoneAndCrossClear
#print axioms FX1Poly.ComputerAlgebra.smithBezoutRepairPositionSweepSeedLandsFindNoneAndCrossClear
#print axioms FX1Poly.ComputerAlgebra.smithBezoutRepairPositionSweepReachesFindNoneHolds

end FX1PolyAudit
