import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithPivotMagnitudeDescent

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithPivotMagnitudeDescent — zero-axiom gate
    (H2-SMITH r27, #2261 — the corrected descent measure `pivotMagnitudeWithin`, the zero-pivot scope,
    and the correct per-pivot statement)

Per-declaration zero-axiom gate for the corrected measure `pivotMagnitudeWithin` (`= |diagonalEntryAt p|`,
which DROPS on the exact `diag(15,10,6,4)` fold where r26's `minNonzeroAbsWithin` STALLED), the budget fit,
the zero-pivot scope (`smithZeroPivotImpliesFindNone`), the named r28 obligation
`SmithFoldDescendsOnNonzeroPivot` with its battery, the guarded NODE-D fuel-adequacy reduction, and the
correct per-pivot statement (seed = fuel-adequacy + off-diagonal half → `SmithReduceCompleteDriverStatement`).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`.  Both the fuel-based `#assert_no_axioms` AND the independent (non-fuel) `#print axioms` are run on
every declaration (the project macro is fuel-based — not trusted alone). -/

namespace FX1PolyAudit

/- The corrected measure and the propext-clean Nat subtraction facts. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.pivotMagnitudeWithin
#assert_no_axioms FX1Poly.ComputerAlgebra.natSubPositiveOfLt
#assert_no_axioms FX1Poly.ComputerAlgebra.natSubEqZeroOfLe

/- Bricks 2-3 — the measure's fold behaviour (strict drops + the sole zero-pivot rise). -/
#assert_no_axioms FX1Poly.ComputerAlgebra.smithPivotMagnitudeDescendsWhereMinNonzeroAbsStalls
#assert_no_axioms FX1Poly.ComputerAlgebra.smithPivotMagnitudeDescendsOnAdversaryBattery
#assert_no_axioms FX1Poly.ComputerAlgebra.smithPivotMagnitudeRisesOnZeroPivotBootstrap

/- The budget fit (`pivotAbs ≤ smithMinorAbsSum`). -/
#assert_no_axioms FX1Poly.ComputerAlgebra.smithRowAbsSumHeadLe
#assert_no_axioms FX1Poly.ComputerAlgebra.smithMinorAbsSumRowsHeadLe
#assert_no_axioms FX1Poly.ComputerAlgebra.pivotMagnitudeLeMinorAbsSum

/- Brick 4 — the zero-pivot seam scoped away. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.smithFindNonDividingLaterDiagonalNoneOfLaterZero
#assert_no_axioms FX1Poly.ComputerAlgebra.smithZeroPivotImpliesFindNone

/- Brick 5 — the named r28 obligation + its battery. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.SmithFoldDescendsOnNonzeroPivot
#assert_no_axioms FX1Poly.ComputerAlgebra.smithFoldDescendsHoldsOnBattery

/- Brick 6 — the guarded NODE-D variant + the fuel-adequacy reduction. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.smithClearingSweepReachesFindNoneOfGuardedDescent
#assert_no_axioms FX1Poly.ComputerAlgebra.ZeroTrailingDiagonalsFrom
#assert_no_axioms FX1Poly.ComputerAlgebra.smithClearingOutputFindNoneFromFoldDescent

/- Brick 7 — the correct per-pivot statement (residual defs + the seed / driver reduction). -/
#assert_no_axioms FX1Poly.ComputerAlgebra.SmithClearingOutputFindNone
#assert_no_axioms FX1Poly.ComputerAlgebra.SmithClearingOutputOffDiagonalDivides
#assert_no_axioms FX1Poly.ComputerAlgebra.seedOfClearingFindNoneAndOffDiagonalResidual
#assert_no_axioms FX1Poly.ComputerAlgebra.smithReduceCompleteDriverOfFindNoneAndOffDiagonal

-- Independent (non-fuel) axiom prints on every declaration.
#print axioms FX1Poly.ComputerAlgebra.pivotMagnitudeWithin
#print axioms FX1Poly.ComputerAlgebra.natSubPositiveOfLt
#print axioms FX1Poly.ComputerAlgebra.natSubEqZeroOfLe
#print axioms FX1Poly.ComputerAlgebra.smithPivotMagnitudeDescendsWhereMinNonzeroAbsStalls
#print axioms FX1Poly.ComputerAlgebra.smithPivotMagnitudeDescendsOnAdversaryBattery
#print axioms FX1Poly.ComputerAlgebra.smithPivotMagnitudeRisesOnZeroPivotBootstrap
#print axioms FX1Poly.ComputerAlgebra.smithRowAbsSumHeadLe
#print axioms FX1Poly.ComputerAlgebra.smithMinorAbsSumRowsHeadLe
#print axioms FX1Poly.ComputerAlgebra.pivotMagnitudeLeMinorAbsSum
#print axioms FX1Poly.ComputerAlgebra.smithFindNonDividingLaterDiagonalNoneOfLaterZero
#print axioms FX1Poly.ComputerAlgebra.smithZeroPivotImpliesFindNone
#print axioms FX1Poly.ComputerAlgebra.SmithFoldDescendsOnNonzeroPivot
#print axioms FX1Poly.ComputerAlgebra.smithFoldDescendsHoldsOnBattery
#print axioms FX1Poly.ComputerAlgebra.smithClearingSweepReachesFindNoneOfGuardedDescent
#print axioms FX1Poly.ComputerAlgebra.ZeroTrailingDiagonalsFrom
#print axioms FX1Poly.ComputerAlgebra.smithClearingOutputFindNoneFromFoldDescent
#print axioms FX1Poly.ComputerAlgebra.SmithClearingOutputFindNone
#print axioms FX1Poly.ComputerAlgebra.SmithClearingOutputOffDiagonalDivides
#print axioms FX1Poly.ComputerAlgebra.seedOfClearingFindNoneAndOffDiagonalResidual
#print axioms FX1Poly.ComputerAlgebra.smithReduceCompleteDriverOfFindNoneAndOffDiagonal

end FX1PolyAudit
