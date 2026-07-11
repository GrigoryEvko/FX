import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithWindowedDivisibility

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithWindowedDivisibility — zero-axiom gate
    (H2-SMITH r19)

Per-declaration zero-axiom gate for the WINDOWED sub-block divisibility preserve tower + the
operation-bounded-below decidable check: the col-guarded row ideal predicate, the two generic guarded
slot carriers, the six windowed single-operation deltas, and the bounded-below word fold.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.RowSlotsDivisibleByFrom
#assert_no_axioms FX1Poly.ComputerAlgebra.MatrixEntriesDivisibleByWithin
#assert_no_axioms FX1Poly.ComputerAlgebra.rowSlotsDivisibleByFromEmpty
#assert_no_axioms FX1Poly.ComputerAlgebra.matrixEntriesDivisibleByWithinAt
#assert_no_axioms FX1Poly.ComputerAlgebra.listReplaceAtGuardedSlot
#assert_no_axioms FX1Poly.ComputerAlgebra.listModifyAtGuardedSlot
#assert_no_axioms FX1Poly.ComputerAlgebra.listGetWithDefaultGe
#assert_no_axioms FX1Poly.ComputerAlgebra.rowSlotsDivisibleFromMapNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.rowSlotsDivisibleFromAddScaledEntriesAt
#assert_no_axioms FX1Poly.ComputerAlgebra.rowSlotsDivisibleFromAddScaledEntries
#assert_no_axioms FX1Poly.ComputerAlgebra.rowSlotsDivisibleFromModifyNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.rowSlotsDivisibleFromSwapEntries
#assert_no_axioms FX1Poly.ComputerAlgebra.rowSlotsDivisibleFromAddScaledWithinRow
#assert_no_axioms FX1Poly.ComputerAlgebra.mapAllRowsGuardedRowPred
#assert_no_axioms FX1Poly.ComputerAlgebra.boolConjTrueLeft
#assert_no_axioms FX1Poly.ComputerAlgebra.boolConjTrueRight
#assert_no_axioms FX1Poly.ComputerAlgebra.opIsBoundedBelow
#assert_no_axioms FX1Poly.ComputerAlgebra.allOpsBoundedBelow
#assert_no_axioms FX1Poly.ComputerAlgebra.applyRowOperationPreservesEntriesDivisibleWithin
#assert_no_axioms FX1Poly.ComputerAlgebra.applyColumnOperationPreservesEntriesDivisibleWithin
#assert_no_axioms FX1Poly.ComputerAlgebra.applyOperationPreservesEntriesDivisibleWithin
#assert_no_axioms FX1Poly.ComputerAlgebra.applyOperationsPreservesEntriesDivisibleWithin

/- H2-SMITH r19 — the CONFINEMENT discharge: the later-pivot repair operations are bounded below the
   start pivot (truth-probed by `#eval`).  The monotone/append kit, the per-generator boundedness
   (clear-column/row, move, sign), and the cascade / position-sweep / whole-sweep structural lifts. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.boolAndBothTrue
#assert_no_axioms FX1Poly.ComputerAlgebra.allOpsBoundedBelowMatchBool
#assert_no_axioms FX1Poly.ComputerAlgebra.allOpsBoundedBelowAppend
#assert_no_axioms FX1Poly.ComputerAlgebra.opIsBoundedBelowMonotone
#assert_no_axioms FX1Poly.ComputerAlgebra.allOpsBoundedBelowMonotone
#assert_no_axioms FX1Poly.ComputerAlgebra.opBoundedBelowAddRow
#assert_no_axioms FX1Poly.ComputerAlgebra.opBoundedBelowAddColumn
#assert_no_axioms FX1Poly.ComputerAlgebra.smithClearColumnBelowStepsBoundedBelow
#assert_no_axioms FX1Poly.ComputerAlgebra.smithClearRowRightStepsBoundedBelow
#assert_no_axioms FX1Poly.ComputerAlgebra.smithMoveToPivotOpsBoundedBelow
#assert_no_axioms FX1Poly.ComputerAlgebra.smithSignNormalizeOpsBoundedBelow
#assert_no_axioms FX1Poly.ComputerAlgebra.smithCascadeSweepBoundedBelow
#assert_no_axioms FX1Poly.ComputerAlgebra.smithRepairPositionSweepClearingBoundedBelow
#assert_no_axioms FX1Poly.ComputerAlgebra.smithDivisibilityRepairSweepClearingOpsBoundedBelow

/- H2-SMITH r19 — NODE 3 read-off: the windowed sub-block diagonal chain yields `SmithChainPrefix`
   (the second conjunct of the cross-pivot motive; the bridge from the windowed tower's output to the
   chain the corrected-driver totality consumes). -/
#assert_no_axioms FX1Poly.ComputerAlgebra.MatrixDiagonalChainWindowed
#assert_no_axioms FX1Poly.ComputerAlgebra.smithChainPrefixOfDiagonalChainWindowed

end FX1PolyAudit
