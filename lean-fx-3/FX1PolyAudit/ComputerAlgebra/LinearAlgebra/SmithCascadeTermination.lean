import FX1PolyAudit.DependencyAudit
import FX1Poly.ComputerAlgebra.LinearAlgebra.SmithCascadeTermination

/-! # FX1PolyAudit/ComputerAlgebra/LinearAlgebra/SmithCascadeTermination — zero-axiom gate
    (H2-SMITH r8)

Per-declaration zero-axiom gate for the Euclid-cascade descent-measure infrastructure: the
signed-residue reconstruction, the column ON-target entry formula (and its `mapAllRows` row-read),
the nonnegative-pivot magnitude bridge, the single-clear residue landing, and the minimal-magnitude
search lower bound (row + minor scan, with their update-step and `== 0` helpers).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.ComputerAlgebra.intMagnitudeSignedRemainder
#assert_no_axioms FX1Poly.ComputerAlgebra.intMagnitudeSignedRemainderNatAbs
#assert_no_axioms FX1Poly.ComputerAlgebra.intMagnitudeReconstructs
#assert_no_axioms FX1Poly.ComputerAlgebra.intOfNatNatAbsOfNonNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.listGetWithDefaultMapAllRows
#assert_no_axioms FX1Poly.ComputerAlgebra.addColumnMultipleEntryOnTargetCol
#assert_no_axioms FX1Poly.ComputerAlgebra.smithSingleClearResidueLands
#assert_no_axioms FX1Poly.ComputerAlgebra.smithSingleClearStrictlyDecreasesPivot
#assert_no_axioms FX1Poly.ComputerAlgebra.natBeqZeroFalseOfNe
#assert_no_axioms FX1Poly.ComputerAlgebra.smithScanRowUpdateSomeBound
#assert_no_axioms FX1Poly.ComputerAlgebra.smithScanRowUpdateNoneBound
#assert_no_axioms FX1Poly.ComputerAlgebra.smithScanRowUpdateSomeEntryBound
#assert_no_axioms FX1Poly.ComputerAlgebra.smithScanRowMinAbsPreservesSomeBound
#assert_no_axioms FX1Poly.ComputerAlgebra.smithScanRowMinAbsBoundsWitness
#assert_no_axioms FX1Poly.ComputerAlgebra.smithScanMinorMinAbsPreservesSomeBound
#assert_no_axioms FX1Poly.ComputerAlgebra.smithScanMinorMinAbsBoundsWitness
#assert_no_axioms FX1Poly.ComputerAlgebra.smithFindMinAbsInMinorBoundsWitness

/- H2-SMITH r9 — the clear-word lift + cross-clear fuel adequacy. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.addColumnMultipleEntryOffTargetCol
#assert_no_axioms FX1Poly.ComputerAlgebra.smithClearRowRightStepsPreservesColumn
#assert_no_axioms FX1Poly.ComputerAlgebra.smithClearRowRightStepsLandsAt
#assert_no_axioms FX1Poly.ComputerAlgebra.smithClearColumnBelowStepsPreservesRow
#assert_no_axioms FX1Poly.ComputerAlgebra.smithClearColumnBelowStepsLandsAt
#assert_no_axioms FX1Poly.ComputerAlgebra.smithClearRowRightStepsCrossEntryEqSingle
#assert_no_axioms FX1Poly.ComputerAlgebra.smithClearColumnBelowStepsCrossEntryEqSingle
#assert_no_axioms FX1Poly.ComputerAlgebra.smithSingleColumnBelowClearResidueLands
#assert_no_axioms FX1Poly.ComputerAlgebra.smithSingleColumnBelowClearStrictlyDecreasesPivot
#assert_no_axioms FX1Poly.ComputerAlgebra.smithClearRowRightStepsCrossEntryStrictlyDecreases
#assert_no_axioms FX1Poly.ComputerAlgebra.smithClearColumnBelowStepsCrossEntryStrictlyDecreases
#assert_no_axioms FX1Poly.ComputerAlgebra.smithRowEntryLeAbsSum
#assert_no_axioms FX1Poly.ComputerAlgebra.smithMinorEntryLeAbsSumRows
#assert_no_axioms FX1Poly.ComputerAlgebra.smithMinorEntryLeAbsSum
#assert_no_axioms FX1Poly.ComputerAlgebra.natNeZeroOfBeqZeroFalse
#assert_no_axioms FX1Poly.ComputerAlgebra.smithScanRowMinAbsResultNonzero
#assert_no_axioms FX1Poly.ComputerAlgebra.smithScanMinorMinAbsResultNonzero
#assert_no_axioms FX1Poly.ComputerAlgebra.smithFindMinAbsInMinorFoundNonzero
#assert_no_axioms FX1Poly.ComputerAlgebra.smithFindMinAbsInMinorNoneAllZero

/- H2-SMITH r9 — the cross-clear segment characterization (the fuel-adequacy base/loop bridge). -/
#assert_no_axioms FX1Poly.ComputerAlgebra.smithNatAddSubOfLe
#assert_no_axioms FX1Poly.ComputerAlgebra.natLtAddSubOfLt
#assert_no_axioms FX1Poly.ComputerAlgebra.smithRowSegmentAllZeroOfPointwiseZero
#assert_no_axioms FX1Poly.ComputerAlgebra.smithColSegmentAllZeroOfPointwiseZero
#assert_no_axioms FX1Poly.ComputerAlgebra.smithCrossIsClearOfFindNone
#assert_no_axioms FX1Poly.ComputerAlgebra.smithRowSegmentNotAllZeroWitness
#assert_no_axioms FX1Poly.ComputerAlgebra.smithColSegmentNotAllZeroWitness
#assert_no_axioms FX1Poly.ComputerAlgebra.smithCrossNotClearWitness

/- H2-SMITH r9 — the move swap-entry bridge (joint (a)'s backbone). -/
#assert_no_axioms FX1Poly.ComputerAlgebra.listGetWithDefaultReplaceAtEq
#assert_no_axioms FX1Poly.ComputerAlgebra.listGetWithDefaultReplaceAtNe
#assert_no_axioms FX1Poly.ComputerAlgebra.swapRowsEntryAtFirst
#assert_no_axioms FX1Poly.ComputerAlgebra.swapEntriesWithinRowAtFirst
#assert_no_axioms FX1Poly.ComputerAlgebra.swapColumnsEntryAtFirst
#assert_no_axioms FX1Poly.ComputerAlgebra.smithMoveToPivotEntryOnPivot

/- H2-SMITH r10 — the found-in-range scan companion (joint (i)) + the negation-magnitude micro-atom. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.smithScanRowMinAbsResultInRange
#assert_no_axioms FX1Poly.ComputerAlgebra.smithScanMinorMinAbsResultInRange
#assert_no_axioms FX1Poly.ComputerAlgebra.smithFindMinAbsInMinorFoundInRange
#assert_no_axioms FX1Poly.ComputerAlgebra.intNegNatAbs

end FX1PolyAudit
