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

/- H2-SMITH r20 — NODE B (B2): the kernel reduction theorem seed ⟹ repairChainHolds, and the driver
   totality on the seed ALONE (structural assembly; no kernel evaluation). -/
#assert_no_axioms FX1Poly.ComputerAlgebra.repairChainHoldsOfSeed
#assert_no_axioms FX1Poly.ComputerAlgebra.smithReduceCompleteDriverOfSubBlockSeed

/- H2-SMITH r20 — NODE C (B3): the seed decomposition (diagonal / off-diagonal halves) + the C2
   diagonal bridging lemma from the find-loop none-exit.  The seed does NOT close (C1's off-diagonal
   ideal content is a separate major arc); these are the honest machine-checked partials. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.SubBlockDiagonalDivisibleFrom
#assert_no_axioms FX1Poly.ComputerAlgebra.SubBlockOffDiagonalDivisibleFrom
#assert_no_axioms FX1Poly.ComputerAlgebra.matrixEntriesDivisibleByWithinOfHalves
#assert_no_axioms FX1Poly.ComputerAlgebra.natMinLeToOr
#assert_no_axioms FX1Poly.ComputerAlgebra.entryAtBeyondZero
#assert_no_axioms FX1Poly.ComputerAlgebra.diagonalEntryAtBeyondWindowZero
#assert_no_axioms FX1Poly.ComputerAlgebra.subBlockDiagonalDivisibleOfFindNone

/- H2-SMITH r21 — NODE D (B1/B2): the C3 fuel-adequacy DESCENT REDUCTION (fold/terminal step helpers +
   rectangularity preservation + the fuel-counting induction reducing find-none-on-output to the two
   named cascade residuals) + the seed's DIAGONAL half from the descent. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.smithClearingFoldStep
#assert_no_axioms FX1Poly.ComputerAlgebra.smithClearingTerminalStep
#assert_no_axioms FX1Poly.ComputerAlgebra.smithClearingFoldStepPreservesRectangular
#assert_no_axioms FX1Poly.ComputerAlgebra.smithClearingSweepReachesFindNoneOfDescent
#assert_no_axioms FX1Poly.ComputerAlgebra.smithClearingSweepDiagonalHalfOfDescent

/- H2-SMITH r21 — NODE E (B3): route (i) of the C1 adjudication refuted, machine-checked (a diagonal
   4x4 whose single-pivot clearing sweep leaves a nonzero interior off-diagonal). -/
#assert_no_axioms FX1Poly.ComputerAlgebra.smithClearingSweepInteriorNotDiagonalWitness

/- H2-SMITH r22 — THE FIT CHECK (B1): Node 3 (`foldDescends`) is a genuine three-part delta, TWO
   halves machine-refuted — the minor-abs-sum measure rises on a fold (Δ1), and the zero-pivot fold
   saturates the fuel budget so no fixed-K lex-into-Nat measure fits (Δ2). -/
#assert_no_axioms FX1Poly.ComputerAlgebra.smithMinorAbsSumRaisesOnFoldWitness
#assert_no_axioms FX1Poly.ComputerAlgebra.smithZeroPivotFoldSaturatesBudgetWitness

/- H2-SMITH r22 — NODE 1 (B2): the gcd-ideal invariance forward-tower route — the sub-block floor
   lo-monotonicity plumbing + the concrete gcd>1 window where the cascade lands the minor gcd (2). -/
#assert_no_axioms FX1Poly.ComputerAlgebra.matrixEntriesDivisibleByWithinLoMono
#assert_no_axioms FX1Poly.ComputerAlgebra.smithClearingSweepLandsMinorGcdOnConcreteWindow

end FX1PolyAudit
