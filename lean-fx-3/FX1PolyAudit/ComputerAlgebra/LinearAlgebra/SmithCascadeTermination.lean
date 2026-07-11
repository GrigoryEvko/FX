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

/- H2-SMITH r10 — the fuel-adequacy induction (B2): the pivot-magnitude packaging, the sweep
   succ-unfolding equation, and the cross-clear-within-fuel reachability theorem itself. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.smithSignNormalizeOpsPreservesPivotMagnitude
#assert_no_axioms FX1Poly.ComputerAlgebra.smithCascadeSweepSucc
#assert_no_axioms FX1Poly.ComputerAlgebra.smithCascadeReachesCrossClear

/- H2-SMITH r10 — the driver-path seed corollary (B3): the cascade at its ACTUAL seed fuel
   (smithMinorAbsSum) reaches cross-clear. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.smithCascadeSweepSeedReachesCrossClear

/- H2-SMITH r11 — the sub-block (low-low) locality round (B1): the two swap off-both atoms, the move-word
   assembly, and the cascade low-low preservation keystone (the settled-prefix monotonicity). -/
#assert_no_axioms FX1Poly.ComputerAlgebra.swapRowsPreservesEntryOffBothRows
#assert_no_axioms FX1Poly.ComputerAlgebra.swapEntriesWithinRowPreservesEntryOffBoth
#assert_no_axioms FX1Poly.ComputerAlgebra.swapColumnsPreservesEntryOffBothCols
#assert_no_axioms FX1Poly.ComputerAlgebra.smithMoveToPivotOpsPreservesLowLowEntry
#assert_no_axioms FX1Poly.ComputerAlgebra.smithCascadeSweepPreservesLowLowEntry

/- H2-SMITH r11 — the fold transport up the driver stack (B2): the min-le-right companion, the seed-fuel
   corollary, and the three per-pivot sweep lifts (cross-clear total sweep, per-position repair, top-down
   divisibility repair). -/
#assert_no_axioms FX1Poly.ComputerAlgebra.natMinLeRight
#assert_no_axioms FX1Poly.ComputerAlgebra.smithCascadeSweepSeedPreservesLowLowEntry
#assert_no_axioms FX1Poly.ComputerAlgebra.smithReduceTotalSweepPreservesLowLowEntry
#assert_no_axioms FX1Poly.ComputerAlgebra.smithRepairPositionSweepSucc
#assert_no_axioms FX1Poly.ComputerAlgebra.smithRepairPositionSweepPreservesLowLowEntry
#assert_no_axioms FX1Poly.ComputerAlgebra.smithDivisibilityRepairSweepPreservesLowLowEntry

/- H2-SMITH r11 — the sub-block postcondition (B3): the settled-prefix off-diagonal-zero transport
   through the seed cascade and the whole divisibility-repair sweep (the prefix conjunct of
   repairWindowDiagHolds; the bands + sub-block stay POLE-A-walled). -/
#assert_no_axioms FX1Poly.ComputerAlgebra.smithCascadeSweepSeedPreservesPrefixOffDiagonal
#assert_no_axioms FX1Poly.ComputerAlgebra.smithDivisibilityRepairSweepPreservesPrefixOffDiagonal

/- H2-SMITH r12 — the band-zero re-expression + the settled-through-`p` frame (B1): the `== 0`/`natAbs`
   micro-atoms, the segment forward pointwise decode (the `= true → pointwise` converse), the cross-clear
   band re-expression, the `SmithPrefixSettled` frame predicate, and its vacuous base + `Nat.min` terminal
   (= full window-diagonal). -/
#assert_no_axioms FX1Poly.ComputerAlgebra.natEqZeroOfBeqZeroTrue
#assert_no_axioms FX1Poly.ComputerAlgebra.intOfNatAbsZero
#assert_no_axioms FX1Poly.ComputerAlgebra.smithRowSegmentAllZeroPointwise
#assert_no_axioms FX1Poly.ComputerAlgebra.smithColSegmentAllZeroPointwise
#assert_no_axioms FX1Poly.ComputerAlgebra.smithCrossIsClearPointwise
#assert_no_axioms FX1Poly.ComputerAlgebra.SmithPrefixSettled
#assert_no_axioms FX1Poly.ComputerAlgebra.smithPrefixSettledZero
#assert_no_axioms FX1Poly.ComputerAlgebra.smithPrefixSettledAtMinIsWindowDiagonal

/- H2-SMITH r12 — the band-preservation lemmas (B2): the `…AtSecond` swap readers, the two zero-source clear
   preservers (row-right reads pivot column, column-below reads pivot row), the two move-word band preservers,
   and the two cascade band keystones (above-right ROW band, below-left COLUMN band) with their driver-path
   seed forms.  The genuinely new content — zeros propagate through the `p+1` ops. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.swapEntriesWithinRowAtSecond
#assert_no_axioms FX1Poly.ComputerAlgebra.swapRowsEntryAtSecond
#assert_no_axioms FX1Poly.ComputerAlgebra.swapColumnsEntryAtSecond
#assert_no_axioms FX1Poly.ComputerAlgebra.smithClearRowRightStepsPreservesRowWithZeroPivotColumn
#assert_no_axioms FX1Poly.ComputerAlgebra.smithClearColumnBelowStepsPreservesColumnWithZeroPivotRow
#assert_no_axioms FX1Poly.ComputerAlgebra.smithMoveToPivotOpsPreservesRowBandZero
#assert_no_axioms FX1Poly.ComputerAlgebra.smithMoveToPivotOpsPreservesColBandZero
#assert_no_axioms FX1Poly.ComputerAlgebra.smithCascadeSweepPreservesAboveRightRowBandZero
#assert_no_axioms FX1Poly.ComputerAlgebra.smithCascadeSweepPreservesBelowLeftColBandZero
#assert_no_axioms FX1Poly.ComputerAlgebra.smithCascadeSweepSeedPreservesAboveRightRowBandZero
#assert_no_axioms FX1Poly.ComputerAlgebra.smithCascadeSweepSeedPreservesBelowLeftColBandZero

/- H2-SMITH r12 — the single-step composed postcondition (B3): one full driver step advances the settled
   frame `p → p+1` (the induction step body, a 5-way region dispatch over r10 cross-clear + r11 low-low + the
   two B2 bands). -/
#assert_no_axioms FX1Poly.ComputerAlgebra.smithCascadeStepSettlesThroughPivot

/- H2-SMITH r12 — the descending-pivot induction skeleton (B4): the frame monotonicity, the propext-clean
   `Nat.min` idempotence, the growing-frame outer fold to the `Nat.min` cap, and its driver-level top —
   the total CROSS-CLEAR driver output is window-diagonal (POLE-A driver path; the repair phase's
   `repairWindowDiagHolds`/`repairChainHolds` stay walled; NO flip). -/
#assert_no_axioms FX1Poly.ComputerAlgebra.smithPrefixSettledMonotone
#assert_no_axioms FX1Poly.ComputerAlgebra.natMinSelf
#assert_no_axioms FX1Poly.ComputerAlgebra.smithReduceTotalSweepSettlesThroughPivots
#assert_no_axioms FX1Poly.ComputerAlgebra.smithReduceTotalSweepDiagonalizes

/- H2-SMITH r13 — the repair-fold frame confinement (B1): the repair fold `addRowMultiple foundPos
   pivotIndex 1` preserves the settled frame AT `pivotIndex` (touches only row `pivotIndex`; the on-row
   frame cells are settled columns that stay `0 + 1*0`).  The r12 frame recast of
   `foldPreservesSettledColumnZero` over the weaker `SmithPrefixSettled` hypothesis; advancing the frame
   `p → p+1` through the fold+re-cascade stays the POLE-B wall. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.smithRepairFoldPreservesSettledFrame

/- H2-SMITH r13 — the repair terminal re-clear (B2): the r10 seed cross-clear instantiated at the post-fold
   matrix, and the whole-position-sweep cross-clear (input cross clear ⇒ output cross clear, structural on the
   repair fuel).  The MEDIUM unconditional cross-strip clearing; the frame advance `p → p+1` stays walled. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.smithRepairFoldCascadeReachesCrossClear
#assert_no_axioms FX1Poly.ComputerAlgebra.smithRepairPositionSweepReachesCrossClear

/- H2-SMITH r13 — the composed repair postcondition (B3): the named repair single-step `Prop` (refutable over
   the bare `SmithPrefixSettled` frame per POLE-B), the conditional growing-frame fold (verbatim mirror of the
   r12 cross-clear `smithReduceTotalSweepSettlesThroughPivots`, single-step CALL replaced by HYPOTHESIS), and
   the conditional window-diagonal read-off at the driver start.  Reusable structural transport isolating the
   repair-fold window-diagonal wall to ONE named `Prop`; `SmithReduceFullDriverStatement` stays uninhabited. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.SmithRepairStepSettlesStatement
#assert_no_axioms FX1Poly.ComputerAlgebra.smithDivisibilityRepairSweepSettlesThroughPivots
#assert_no_axioms FX1Poly.ComputerAlgebra.smithDivisibilityRepairSweepDiagonalizes

/- H2-SMITH r13 — the verbatim repair-window-diagonal hypothesis + the audited driver movement (B4): the
   conditional `smithDivisibilityRepairSweepDiagonalizes` instantiated at the driver's actual repair input to
   match `smithReduceFullDriverOfRepairInvariants`'s first hypothesis `repairWindowDiagHolds` verbatim, and the
   driver totality reduced to EXACTLY `{SmithRepairStepSettlesStatement, repairChainHolds}` (does NOT rest on
   the chain alone — the single-step is the window-diagonal residual, refutable over the bare frame per POLE-B).
   `SmithReduceFullDriverStatement` stays uninhabited; NO flip. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.repairWindowDiagHoldsOfRepairStep
#assert_no_axioms FX1Poly.ComputerAlgebra.smithReduceFullDriverOfRepairStepAndChain

/- H2-SMITH r14 — the ideal / Z-combination stability atom (B4, JAM 2-PRESERVE core): the three `Int`
   divisibility atoms (`d ∣ 0`, `d ∣ -x`, `d ∣ a + c*b`), the three range-free slot-predicate preservers
   (`listReplaceAt`/`listModifyAt`/`mapAllRows`), the row/matrix divisibility predicates, the six primitive
   row/column-transform preservers, and the whole-matrix preservation under a single operation, a whole
   certificate word, and the diagonal read-off — the refutation-immune UNCONDITIONAL PRESERVE half (the
   sub-block ESTABLISH for `d_p`, `p > 0`, re-imports JAM 1; `SmithReduceFullDriverStatement` uninhabited). -/
#assert_no_axioms FX1Poly.ComputerAlgebra.dividesExactlyZero
#assert_no_axioms FX1Poly.ComputerAlgebra.dividesExactlyNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.dividesExactlyAddScaled
#assert_no_axioms FX1Poly.ComputerAlgebra.listReplaceAtPreservesSlotPredicate
#assert_no_axioms FX1Poly.ComputerAlgebra.listModifyAtPreservesSlotPredicate
#assert_no_axioms FX1Poly.ComputerAlgebra.mapAllRowsPreservesSlotPredicate
#assert_no_axioms FX1Poly.ComputerAlgebra.RowSlotsDivisibleBy
#assert_no_axioms FX1Poly.ComputerAlgebra.rowSlotsDivisibleByEmpty
#assert_no_axioms FX1Poly.ComputerAlgebra.MatrixEntriesDivisibleBy
#assert_no_axioms FX1Poly.ComputerAlgebra.matrixEntriesDivisibleByAt
#assert_no_axioms FX1Poly.ComputerAlgebra.rowSlotsDivisibleMapNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.rowSlotsDivisibleAddScaledEntries
#assert_no_axioms FX1Poly.ComputerAlgebra.rowSlotsDivisibleSwapEntries
#assert_no_axioms FX1Poly.ComputerAlgebra.rowSlotsDivisibleModifyNeg
#assert_no_axioms FX1Poly.ComputerAlgebra.rowSlotsDivisibleAddScaledWithinRow
#assert_no_axioms FX1Poly.ComputerAlgebra.applyRowOperationPreservesEntriesDivisible
#assert_no_axioms FX1Poly.ComputerAlgebra.applyColumnOperationPreservesEntriesDivisible
#assert_no_axioms FX1Poly.ComputerAlgebra.applyOperationPreservesEntriesDivisible
#assert_no_axioms FX1Poly.ComputerAlgebra.applyOperationsPreservesEntriesDivisible
#assert_no_axioms FX1Poly.ComputerAlgebra.matrixEntriesDivisibleByDiagonal

/- H2-SMITH r14 — the pivot-is-min premise refuted on-path (B1): the (refuted) pivot-is-min-abs
   reduceTotal-postcondition statement and its refutation via the driver-computed `diag(4, 1, 150)`
   (`d_0 = 4 > d_1 = 1`) — a permanent regression recording that the round's central premise is a DEAD
   lemma; the true no-drag invariant is the suffix-min property (B3), not sortedness. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.SmithReduceTotalPivotMinStatement
#assert_no_axioms FX1Poly.ComputerAlgebra.smithReduceTotalPivotMinIsRefuted

/- H2-SMITH r14 — the strict-`<` / row-major tie-no-drag atom (B2): the single-step position-keep (a tie
   never displaces the earlier-scanned best, from the strict-`<` update guard) and its segment fold (the
   whole scan keeps its `some` best when no scanned entry is strictly smaller).  The load-bearing
   tie-resolution witnessing that equal magnitudes never strand repair residue. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.smithScanRowUpdateTieKeepsPosition
#assert_no_axioms FX1Poly.ComputerAlgebra.smithScanRowMinAbsTieKeepsBest

/- H2-SMITH r14 — the true no-drag reachability invariant, correctly stated (B3): the suffix-min invariant
   (the fold operand pair carries the suffix minimum), its EXCLUSION probe (the drag input `diag(30,20,12)`
   violates it) and its on-path witness (the reduceTotal fixed point `diag(2,3)` satisfies it).  The
   correctly-stated r14 wall replacing the B1-refuted pivot-is-min and the refutable bare frame; a genuine
   non-vacuous strengthening, NOT a discharge (`SmithReduceFullDriverStatement` stays uninhabited; NO flip). -/
#assert_no_axioms FX1Poly.ComputerAlgebra.SmithSuffixMinRepairInvariant
#assert_no_axioms FX1Poly.ComputerAlgebra.smithSuffixMinDragInputViolates
#assert_no_axioms FX1Poly.ComputerAlgebra.smithSuffixMinReduceTotalOnPathProbe

/- H2-SMITH r15 — the suffix-min invariant REFUTED on the genuine driver path (B1/B3): the matrix-21
   witness (its two literal diagonals and the per-diagonal reduceTotal-output anchor), the establishment
   that the witness satisfies the invariant (pinning non-vacuity), the (refuted) preservation node, and
   the crux refutation that the pivot-0 repair does NOT preserve it (`min(180,210)=180 > d_3=150`).  A
   permanent regression retiring the invariant to a DEAD node; `SmithReduceFullDriverStatement` stays
   uninhabited (NO flip). -/
#assert_no_axioms FX1Poly.ComputerAlgebra.smithSuffixMinRepairWitnessEstablishes
#assert_no_axioms FX1Poly.ComputerAlgebra.smithSuffixMinRepairWitnessMatchesReduceTotalDiagonal
#assert_no_axioms FX1Poly.ComputerAlgebra.SmithSuffixMinRepairPreservesStatement
#assert_no_axioms FX1Poly.ComputerAlgebra.smithSuffixMinRepairDoesNotPreserve

/- H2-SMITH r15 — the establishment fails on rank-deficient inputs (B2/R1): `diag(4, 1, 150, 0)` refutes
   the invariant (`min(4,1)=1 > trailing d_3=0`), witnessing the def is over-strong on zeros — not
   establishable as a reduceTotal postcondition without excluding them.  A second permanent regression. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.smithSuffixMinEstablishFailsOnRankDeficient

/- H2-SMITH r15 — the positive counterweight (B1-positive): the augmented driver `smithReduceFull` lands
   valid Smith normal form on the exact r14 refuters — the drag input `diag(30,20,12)` reduces to
   `diag(2,60,60)` and the unsorted minor `[[4,0,0],[0,6,10],[0,15,0]]` to `diag(1,2,300)` — so the
   refuted suffix-min invariant is NOT necessary for driver correctness. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.smithDragDiagonalDriverReducesToSmithForm
#assert_no_axioms FX1Poly.ComputerAlgebra.smithUnsortedMinorDriverReducesToSmithForm

/- H2-SMITH r16 — the driver totality target is REFUTED (B1): the rectangular `diag(10, 10, 6, 9)` is a
   kernel-confirmed refuter — `smithReduceFull` strands `entryAt 3 2 = 30` off the diagonal
   (`[[1,0,0,0],[0,2,0,0],[0,0,30,0],[0,0,30,90]]`), so `SmithReduceFullDriverStatement` is FALSE.
   Non-vacuity pinned both directions: the input is rectangular and the strand is nonzero. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.smithReduceFullDriverRefuterInputIsRectangular
#assert_no_axioms FX1Poly.ComputerAlgebra.smithReduceFullStrandsOffDiagonalWitness
#assert_no_axioms FX1Poly.ComputerAlgebra.smithReduceFullDriverIsRefuted

/- H2-SMITH r17 — the corrected driver lands the refuter (B1 battery): the corrected `smithReduceComplete`
   reduces the exact rectangular `diag(10, 10, 6, 9)` refuter to `diag(1, 2, 30, 90)` (the positive flip of
   `smithReduceFullDriverIsRefuted`), re-lands the drag / unsorted / coprime counterweights, and a
   RECTANGULAR `2 x 4` member — each kernel-checked by whole-driver defeq to the literal Smith normal form. -/
#assert_no_axioms FX1Poly.ComputerAlgebra.smithReduceCompleteDriverRefuterLandsSmithForm
#assert_no_axioms FX1Poly.ComputerAlgebra.smithDragDiagonalByCompleteDriver
#assert_no_axioms FX1Poly.ComputerAlgebra.smithUnsortedMinorByCompleteDriver
#assert_no_axioms FX1Poly.ComputerAlgebra.smithCoprimeByCompleteDriver
#assert_no_axioms FX1Poly.ComputerAlgebra.smithRectangularByCompleteDriver

end FX1PolyAudit
