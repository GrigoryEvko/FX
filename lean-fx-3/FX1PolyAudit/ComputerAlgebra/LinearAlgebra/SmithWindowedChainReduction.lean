import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithWindowedChainReduction

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithWindowedChainReduction — zero-axiom gate
    (H2-SMITH r20)

Per-declaration zero-axiom gate for the seed ⟹ chain reduction: the generic list-slot freeze lemmas,
the freeze-below decidable check and its entry-level / word-level carriers, the sweep re-walk, and the
NODE A cross-pivot carrier `chainWindowedThroughPivots`.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

/- H2-SMITH r20 — NODE A (B1): generic list-slot freeze lemmas + the freeze-below check + entry/word
   freeze + the sweep re-walk + the cross-pivot carrier. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.listReplaceAtGetOther
#assert_no_axioms FX1Poly.ComputerAlgebra.listModifyAtGetOther
#assert_no_axioms FX1Poly.ComputerAlgebra.opFreezesBelow
#assert_no_axioms FX1Poly.ComputerAlgebra.allOpsFreezeBelow
#assert_no_axioms FX1Poly.ComputerAlgebra.swapRowsRowsGetOther
#assert_no_axioms FX1Poly.ComputerAlgebra.negateRowRowsGetOther
#assert_no_axioms FX1Poly.ComputerAlgebra.addRowMultipleRowsGetOther
#assert_no_axioms FX1Poly.ComputerAlgebra.swapEntriesWithinRowGetOther
#assert_no_axioms FX1Poly.ComputerAlgebra.addScaledEntryWithinRowGetOther
#assert_no_axioms FX1Poly.ComputerAlgebra.mapAllRowsFreezesColEntry
#assert_no_axioms FX1Poly.ComputerAlgebra.entryAtOfRowsGet
#assert_no_axioms FX1Poly.ComputerAlgebra.applyRowOperationFreezesEntryBelow
#assert_no_axioms FX1Poly.ComputerAlgebra.applyColumnOperationFreezesEntryBelow
#assert_no_axioms FX1Poly.ComputerAlgebra.applyOperationFreezesEntryBelow
#assert_no_axioms FX1Poly.ComputerAlgebra.applyOperationsFreezeEntryBelow
#assert_no_axioms FX1Poly.ComputerAlgebra.allOpsFreezeBelowAppend
#assert_no_axioms FX1Poly.ComputerAlgebra.allOpsFreezeBelowMatchBool
#assert_no_axioms FX1Poly.ComputerAlgebra.opFreezesBelowAddRow
#assert_no_axioms FX1Poly.ComputerAlgebra.opFreezesBelowAddColumn
#assert_no_axioms FX1Poly.ComputerAlgebra.smithClearColumnBelowStepsFreezesBelow
#assert_no_axioms FX1Poly.ComputerAlgebra.smithClearRowRightStepsFreezesBelow
#assert_no_axioms FX1Poly.ComputerAlgebra.smithMoveToPivotOpsFreezesBelow
#assert_no_axioms FX1Poly.ComputerAlgebra.smithSignNormalizeOpsFreezesBelow
#assert_no_axioms FX1Poly.ComputerAlgebra.smithCascadeSweepFreezesBelow
#assert_no_axioms FX1Poly.ComputerAlgebra.smithRepairPositionSweepClearingFreezesBelow
#assert_no_axioms FX1Poly.ComputerAlgebra.matrixDiagonalChainWindowedMonotone
#assert_no_axioms FX1Poly.ComputerAlgebra.smithDivisibilityRepairSweepClearingSucc
#assert_no_axioms FX1Poly.ComputerAlgebra.chainWindowedThroughPivots

end FX1PolyAudit
