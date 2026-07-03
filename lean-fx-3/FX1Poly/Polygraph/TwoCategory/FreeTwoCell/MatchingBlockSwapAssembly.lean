import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFreshShift

/-! # mode-3 keystone — the block-swap `openMap` assembly (`blockRotate` relates the transposed orders)

The sigma witness of the matching Godement core swap is `blockRotate nf wA wB` (`nf` the shared fresh
counter, `wA`/`wB` the two blocks' structural fresh counts).  This file proves its `openMap` field: the
REDUCT core's open wires (beta then upper-alpha) are exactly the `blockRotate`-image of the REDEX core's
(upper-alpha then beta).  Assembly is pointwise (`natListEqOfPointwiseGetAt`) over FOUR zones of the final
wire list:

  * prefix `[0, p)` — both orders leave it untouched (prefix invariants twice per order); the values are
    pre-swap ids `< nf` (freshness), fixed by the rotation;
  * alpha window `[p, p + |fHigh|)` — order-2 runs upper-alpha at counter `nf + wB` on the same window
    (beta fired above it), so the window congruence at `delta = wB` gives `freshShiftAbove nf wB` of
    order-1's window; on values `< nf + wA` the rotation IS that shift
    (`blockRotate_eq_freshShiftAbove_ofFirstBlockRange`);
  * beta window `[p + |fHigh|, p + |fHigh| + |gMid|)` — the TWO-POSITION window congruence at `delta = wA`
    (beta fires below `fHigh` in order-1 but below `fMid` in order-2) gives order-1's window as
    `freshShiftAbove nf wA` of order-2's; on values `< nf + wB` the rotation UNDOES that shift
    (`blockRotate_freshShiftAbove_eq_self_ofSecondBlockRange`);
  * suffix — both orders shift the same pre-swap reads into place (suffix invariants twice per order);
    the values are `< nf`, fixed by the rotation.

Raw Lean 4 + Init; structural recursion only; per-declaration `#assert_no_axioms` gated in the audit
twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The rotation/shift agreement lemmas (the zone value bridges) -/

/-- ★ **Below the FIRST block's top (`value < lo + w1`), the block rotation IS the fresh shift by the
second width.**  Below the window both fix the value; on the first sub-block both shift up by `w2`. -/
theorem blockRotate_eq_freshShiftAbove_ofFirstBlockRange (lo w1 w2 value : Nat)
    (belowFirstTop : value < lo + w1) :
    blockRotate lo w1 w2 value = freshShiftAbove lo w2 value := by
  cases Nat.lt_or_ge value lo with
  | inl belowWindow =>
      rw [blockRotate_below lo w1 w2 value belowWindow,
        freshShiftAbove_ofNotLe lo w2 value
          (fun windowLe => absurd belowWindow (Nat.not_lt.mpr windowLe))]
  | inr atOrAboveWindow =>
      rw [blockRotate_firstBlock lo w1 w2 value atOrAboveWindow belowFirstTop,
        freshShiftAbove_ofLe lo w2 value atOrAboveWindow]

/-- ★ **The block rotation UNDOES the fresh shift by the first width on values below the SECOND block's
width top (`value < lo + w2`).**  A below-window value is fixed by both; an in-range value shifts into
the second sub-block `[lo + w1, lo + w1 + w2)` and rotates back down by `w1` (exact truncated
subtraction via `addSubCancelRight`). -/
theorem blockRotate_freshShiftAbove_eq_self_ofSecondBlockRange (lo w1 w2 value : Nat)
    (belowSecondTop : value < lo + w2) :
    blockRotate lo w1 w2 (freshShiftAbove lo w1 value) = value := by
  cases Nat.lt_or_ge value lo with
  | inl belowWindow =>
      rw [freshShiftAbove_ofNotLe lo w1 value
          (fun windowLe => absurd belowWindow (Nat.not_lt.mpr windowLe)),
        blockRotate_below lo w1 w2 value belowWindow]
  | inr atOrAboveWindow =>
      rw [freshShiftAbove_ofLe lo w1 value atOrAboveWindow]
      have inSecondBlock : lo + w1 ≤ value + w1 := Nat.add_le_add_right atOrAboveWindow w1
      have belowSecondBlockTop : value + w1 < lo + w1 + w2 := by
        rw [Nat.add_right_comm lo w1 w2]
        exact Nat.add_lt_add_right belowSecondTop w1
      rw [blockRotate_secondBlock lo w1 w2 (value + w1) inSecondBlock belowSecondBlockTop,
        addSubCancelRight value w1]

/-! ## Nat cancellation helpers (hand-rolled; the core cancellation lemmas leak `propext`) -/

private theorem natAddRightCancel : (cancelled : Nat) → {leftSum rightSum : Nat} →
    leftSum + cancelled = rightSum + cancelled → leftSum = rightSum
  | 0, _, _, sumsEq => sumsEq
  | cancelled + 1, _, _, sumsEq => natAddRightCancel cancelled (Nat.succ.inj sumsEq)

private theorem natAddLeCancelRight : (cancelled : Nat) → {leftSum rightSum : Nat} →
    leftSum + cancelled ≤ rightSum + cancelled → leftSum ≤ rightSum
  | 0, _, _, sumsLe => sumsLe
  | cancelled + 1, _, _, sumsLe => natAddLeCancelRight cancelled (Nat.le_of_succ_le_succ sumsLe)

/-! ## The openMap assembly -/

/-- ★ **The block-swap `openMap` field: the reduct core's open wires are the `blockRotate`-image of the
redex core's.**  From a FRESH state with both blocks' windows in range, running upper-alpha then beta
(the redex order) versus beta then upper-alpha (the reduct order) produces wire lists related pointwise
by `blockRotate shared.nextFresh wA wB` — the four-zone argument of the file header.  This is the
genuinely-geometric field of the `MatchingComponentSim` sigma witness; `nfEq` is banked
(`matchingCoreSwap_nextFresh_eq`), the forests are generic, and `componentComm` / `loopsEq` ride the
component-algebra kit. -/
theorem matchingCoreSwap_openWires_blockRotate {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {fMid fHigh : ModalityPath signature.graph sourceMode middleMode}
    {gLow gMid : ModalityPath signature.graph middleMode targetMode}
    (cellAlphaUpper : RawTwoCellExpr signature fMid fHigh)
    (cellBeta : RawTwoCellExpr signature gLow gMid)
    (leftAcc : ModalityPath signature.graph overallSource sourceMode)
    (rightAcc : ModalityPath signature.graph targetMode overallTarget)
    (shared : WireState)
    (alphaCupCap : CellHasCupCapGenerators cellAlphaUpper)
    (betaCupCap : CellHasCupCapGenerators cellBeta)
    (sharedFresh : WireStateFresh shared)
    (nfPos : 0 < shared.nextFresh)
    (windowsInRange : leftAcc.length + fMid.length + gLow.length ≤ shared.openWires.length) :
    (runMatchingCell (runMatchingCell shared (composePath leftAcc fMid) rightAcc cellBeta)
        leftAcc (composePath gMid rightAcc) cellAlphaUpper).openWires
      = ((runMatchingCell (runMatchingCell shared leftAcc (composePath gLow rightAcc)
            cellAlphaUpper) (composePath leftAcc fHigh) rightAcc cellBeta).openWires).map
          (blockRotate shared.nextFresh (cellFreshCount cellAlphaUpper)
            (cellFreshCount cellBeta)) := by
  -- window ranges and boundary counts for the four runs
  have rangeAlphaFirst : leftAcc.length + fMid.length ≤ shared.openWires.length :=
    Nat.le_trans (Nat.le_add_right (leftAcc.length + fMid.length) gLow.length) windowsInRange
  have rangeBetaSecond : (composePath leftAcc fMid).length + gLow.length
      ≤ shared.openWires.length := by
    rw [composePath_length leftAcc fMid]
    exact windowsInRange
  have countAlphaFirst := (runMatchingCell_openWiresSuffix_invariant leftAcc
    (composePath gLow rightAcc) cellAlphaUpper shared alphaCupCap rangeAlphaFirst).2
  have countBetaSecond := (runMatchingCell_openWiresSuffix_invariant (composePath leftAcc fMid)
    rightAcc cellBeta shared betaCupCap rangeBetaSecond).2
  have rangeBetaFirst : (composePath leftAcc fHigh).length + gLow.length
      ≤ (runMatchingCell shared leftAcc (composePath gLow rightAcc)
          cellAlphaUpper).openWires.length := by
    have padded : (composePath leftAcc fHigh).length + gLow.length + fMid.length
        ≤ (runMatchingCell shared leftAcc (composePath gLow rightAcc)
            cellAlphaUpper).openWires.length + fMid.length := by
      rw [composePath_length leftAcc fHigh,
        Nat.add_right_comm (leftAcc.length + fHigh.length) gLow.length fMid.length,
        Nat.add_right_comm leftAcc.length fHigh.length fMid.length,
        Nat.add_right_comm (leftAcc.length + fMid.length) fHigh.length gLow.length,
        countAlphaFirst]
      exact Nat.add_le_add_right windowsInRange fHigh.length
    exact natAddLeCancelRight fMid.length padded
  have rangeAlphaSecond : leftAcc.length + fMid.length
      ≤ (runMatchingCell shared (composePath leftAcc fMid) rightAcc
          cellBeta).openWires.length := by
    have padded : leftAcc.length + fMid.length + gLow.length
        ≤ (runMatchingCell shared (composePath leftAcc fMid) rightAcc
            cellBeta).openWires.length + gLow.length := by
      rw [countBetaSecond]
      exact Nat.le_trans windowsInRange (Nat.le_add_right shared.openWires.length gMid.length)
    exact natAddLeCancelRight gLow.length padded
  have countBetaFirst := (runMatchingCell_openWiresSuffix_invariant (composePath leftAcc fHigh)
    rightAcc cellBeta (runMatchingCell shared leftAcc (composePath gLow rightAcc) cellAlphaUpper)
    betaCupCap rangeBetaFirst).2
  have countAlphaSecond := (runMatchingCell_openWiresSuffix_invariant leftAcc
    (composePath gMid rightAcc) cellAlphaUpper
    (runMatchingCell shared (composePath leftAcc fMid) rightAcc cellBeta)
    alphaCupCap rangeAlphaSecond).2
  -- freshness value bounds for the three states the zone values come from
  have sharedValueBelow : ∀ index, natListGetAt shared.openWires index < shared.nextFresh :=
    fun index => natListGetAt_lt shared.nextFresh nfPos shared.openWires index sharedFresh.1
  have alphaFirstValueBelow : ∀ index,
      natListGetAt (runMatchingCell shared leftAcc (composePath gLow rightAcc)
          cellAlphaUpper).openWires index
        < shared.nextFresh + cellFreshCount cellAlphaUpper := by
    intro index
    have belowOwnCounter := natListGetAt_lt
      (runMatchingCell shared leftAcc (composePath gLow rightAcc) cellAlphaUpper).nextFresh
      (Nat.lt_of_lt_of_le nfPos
        (runMatchingCell_nextFresh_le shared leftAcc (composePath gLow rightAcc) cellAlphaUpper))
      (runMatchingCell shared leftAcc (composePath gLow rightAcc) cellAlphaUpper).openWires index
      (runMatchingCell_wireStateFresh shared leftAcc (composePath gLow rightAcc) cellAlphaUpper
        sharedFresh nfPos).1
    rw [runMatchingCell_nextFresh shared leftAcc (composePath gLow rightAcc) cellAlphaUpper]
      at belowOwnCounter
    exact belowOwnCounter
  have betaSecondValueBelow : ∀ index,
      natListGetAt (runMatchingCell shared (composePath leftAcc fMid) rightAcc
          cellBeta).openWires index
        < shared.nextFresh + cellFreshCount cellBeta := by
    intro index
    have belowOwnCounter := natListGetAt_lt
      (runMatchingCell shared (composePath leftAcc fMid) rightAcc cellBeta).nextFresh
      (Nat.lt_of_lt_of_le nfPos
        (runMatchingCell_nextFresh_le shared (composePath leftAcc fMid) rightAcc cellBeta))
      (runMatchingCell shared (composePath leftAcc fMid) rightAcc cellBeta).openWires index
      (runMatchingCell_wireStateFresh shared (composePath leftAcc fMid) rightAcc cellBeta
        sharedFresh nfPos).1
    rw [runMatchingCell_nextFresh shared (composePath leftAcc fMid) rightAcc cellBeta]
      at belowOwnCounter
    exact belowOwnCounter
  -- the alpha-window congruence: order-2 runs upper-alpha at counter nf + wB on the SAME window
  have windowMapAlpha : ∀ innerOffset, innerOffset < fMid.length →
      natListGetAt (runMatchingCell shared (composePath leftAcc fMid) rightAcc
          cellBeta).openWires (leftAcc.length + innerOffset)
        = freshShiftAbove shared.nextFresh (cellFreshCount cellBeta)
            (natListGetAt shared.openWires (leftAcc.length + innerOffset)) := by
    intro innerOffset offsetInRange
    have belowWindow : leftAcc.length + innerOffset < (composePath leftAcc fMid).length := by
      rw [composePath_length leftAcc fMid]
      exact Nat.add_lt_add_left offsetInRange leftAcc.length
    have prefixRead := (runMatchingCell_openWiresPrefix_invariant shared
      (composePath leftAcc fMid) rightAcc cellBeta (leftAcc.length + innerOffset) belowWindow
      (Nat.lt_of_lt_of_le (Nat.add_lt_add_left offsetInRange leftAcc.length)
        rangeAlphaFirst)).1
    rw [prefixRead, freshShiftAbove_ofNotLe shared.nextFresh (cellFreshCount cellBeta)
      (natListGetAt shared.openWires (leftAcc.length + innerOffset))
      (fun counterLe => absurd (sharedValueBelow (leftAcc.length + innerOffset))
        (Nat.not_lt.mpr counterLe))]
  have alphaWindowCongruence := runMatchingCell_windowWireView_freshShift shared.nextFresh
    (cellFreshCount cellBeta) leftAcc leftAcc (composePath gLow rightAcc)
    (composePath gMid rightAcc) cellAlphaUpper shared
    (runMatchingCell shared (composePath leftAcc fMid) rightAcc cellBeta) alphaCupCap
    windowMapAlpha (runMatchingCell_nextFresh shared (composePath leftAcc fMid) rightAcc cellBeta)
    (Nat.le_refl shared.nextFresh) rangeAlphaFirst rangeAlphaSecond
  -- the beta-window congruence, TWO-POSITION: beta fires below fHigh in order-1, below fMid in order-2
  have windowMapBeta : ∀ innerOffset, innerOffset < gLow.length →
      natListGetAt (runMatchingCell shared leftAcc (composePath gLow rightAcc)
          cellAlphaUpper).openWires ((composePath leftAcc fHigh).length + innerOffset)
        = freshShiftAbove shared.nextFresh (cellFreshCount cellAlphaUpper)
            (natListGetAt shared.openWires
              ((composePath leftAcc fMid).length + innerOffset)) := by
    intro innerOffset offsetInRange
    have suffixRead := (runMatchingCell_openWiresSuffix_invariant leftAcc
      (composePath gLow rightAcc) cellAlphaUpper shared alphaCupCap rangeAlphaFirst).1
      innerOffset
    rw [composePath_length leftAcc fHigh, composePath_length leftAcc fMid,
      Nat.add_right_comm leftAcc.length fHigh.length innerOffset,
      Nat.add_right_comm leftAcc.length fMid.length innerOffset, suffixRead,
      freshShiftAbove_ofNotLe shared.nextFresh (cellFreshCount cellAlphaUpper)
        (natListGetAt shared.openWires (leftAcc.length + innerOffset + fMid.length))
        (fun counterLe => absurd
          (sharedValueBelow (leftAcc.length + innerOffset + fMid.length))
          (Nat.not_lt.mpr counterLe))]
  have betaWindowCongruence := runMatchingCell_windowWireView_freshShift shared.nextFresh
    (cellFreshCount cellAlphaUpper) (composePath leftAcc fMid) (composePath leftAcc fHigh)
    rightAcc rightAcc cellBeta shared
    (runMatchingCell shared leftAcc (composePath gLow rightAcc) cellAlphaUpper) betaCupCap
    windowMapBeta (runMatchingCell_nextFresh shared leftAcc (composePath gLow rightAcc)
      cellAlphaUpper)
    (Nat.le_refl shared.nextFresh) rangeBetaSecond rangeBetaFirst
  -- the two final lists have equal length (cancel the two block widths)
  have paddedLengthEq :
      (runMatchingCell (runMatchingCell shared (composePath leftAcc fMid) rightAcc cellBeta)
          leftAcc (composePath gMid rightAcc) cellAlphaUpper).openWires.length
          + fMid.length + gLow.length
        = (runMatchingCell (runMatchingCell shared leftAcc (composePath gLow rightAcc)
              cellAlphaUpper) (composePath leftAcc fHigh) rightAcc
              cellBeta).openWires.length
          + fMid.length + gLow.length := by
    rw [countAlphaSecond,
      Nat.add_right_comm (runMatchingCell shared (composePath leftAcc fMid) rightAcc
        cellBeta).openWires.length fHigh.length gLow.length,
      countBetaSecond,
      Nat.add_right_comm shared.openWires.length gMid.length fHigh.length,
      Nat.add_right_comm (runMatchingCell (runMatchingCell shared leftAcc
        (composePath gLow rightAcc) cellAlphaUpper) (composePath leftAcc fHigh) rightAcc
        cellBeta).openWires.length fMid.length gLow.length,
      countBetaFirst,
      Nat.add_right_comm (runMatchingCell shared leftAcc (composePath gLow rightAcc)
        cellAlphaUpper).openWires.length gMid.length fMid.length,
      countAlphaFirst]
  have lengthEq :
      (runMatchingCell (runMatchingCell shared (composePath leftAcc fMid) rightAcc cellBeta)
          leftAcc (composePath gMid rightAcc) cellAlphaUpper).openWires.length
        = (runMatchingCell (runMatchingCell shared leftAcc (composePath gLow rightAcc)
            cellAlphaUpper) (composePath leftAcc fHigh) rightAcc
            cellBeta).openWires.length :=
    natAddRightCancel fMid.length (natAddRightCancel gLow.length paddedLengthEq)
  -- pointwise assembly over the four zones
  refine natListEqOfPointwiseGetAt _ _ ?_ ?_
  · rw [mapLength]
    exact lengthEq
  · intro index indexBelowLength
    rw [natListGetAt_map_inRange (blockRotate shared.nextFresh (cellFreshCount cellAlphaUpper)
      (cellFreshCount cellBeta))
      (runMatchingCell (runMatchingCell shared leftAcc (composePath gLow rightAcc)
        cellAlphaUpper) (composePath leftAcc fHigh) rightAcc cellBeta).openWires index
      (Nat.lt_of_lt_of_le indexBelowLength (Nat.le_of_eq lengthEq))]
    cases Nat.lt_or_ge index leftAcc.length with
    | inl belowWindowStart =>
        -- ZONE 1 (prefix): both orders read the untouched shared prefix, values < nf are fixed
        have alphaSecondPrefix := (runMatchingCell_openWiresPrefix_invariant
          (runMatchingCell shared (composePath leftAcc fMid) rightAcc cellBeta) leftAcc
          (composePath gMid rightAcc) cellAlphaUpper index belowWindowStart
          (Nat.lt_of_lt_of_le belowWindowStart
            (Nat.le_trans (Nat.le_add_right leftAcc.length fMid.length) rangeAlphaSecond))).1
        have betaSecondPrefix := (runMatchingCell_openWiresPrefix_invariant shared
          (composePath leftAcc fMid) rightAcc cellBeta index
          (Nat.lt_of_lt_of_le belowWindowStart (composePath_length_left_le leftAcc fMid))
          (Nat.lt_of_lt_of_le belowWindowStart
            (Nat.le_trans (composePath_length_left_le leftAcc fMid)
              (Nat.le_trans (Nat.le_add_right (composePath leftAcc fMid).length gLow.length)
                rangeBetaSecond)))).1
        have betaFirstPrefix := (runMatchingCell_openWiresPrefix_invariant
          (runMatchingCell shared leftAcc (composePath gLow rightAcc) cellAlphaUpper)
          (composePath leftAcc fHigh) rightAcc cellBeta index
          (Nat.lt_of_lt_of_le belowWindowStart (composePath_length_left_le leftAcc fHigh))
          (Nat.lt_of_lt_of_le belowWindowStart
            (Nat.le_trans (composePath_length_left_le leftAcc fHigh)
              (Nat.le_trans (Nat.le_add_right (composePath leftAcc fHigh).length gLow.length)
                rangeBetaFirst)))).1
        have alphaFirstPrefix := (runMatchingCell_openWiresPrefix_invariant shared leftAcc
          (composePath gLow rightAcc) cellAlphaUpper index belowWindowStart
          (Nat.lt_of_lt_of_le belowWindowStart
            (Nat.le_trans (Nat.le_add_right leftAcc.length fMid.length) rangeAlphaFirst))).1
        rw [alphaSecondPrefix, betaSecondPrefix, betaFirstPrefix, alphaFirstPrefix,
          blockRotate_below shared.nextFresh (cellFreshCount cellAlphaUpper)
            (cellFreshCount cellBeta) (natListGetAt shared.openWires index)
            (sharedValueBelow index)]
    | inr atOrPastWindowStart =>
        obtain ⟨windowOffset, windowOffsetEq⟩ := Nat.le.dest atOrPastWindowStart
        cases Nat.lt_or_ge windowOffset fHigh.length with
        | inl insideAlphaWindow =>
            -- ZONE 2 (alpha window): the window congruence at delta = wB, rotation = shift
            have belowBetaWindow : index < (composePath leftAcc fHigh).length := by
              rw [composePath_length leftAcc fHigh, ← windowOffsetEq]
              exact Nat.add_lt_add_left insideAlphaWindow leftAcc.length
            have betaFirstPrefix := (runMatchingCell_openWiresPrefix_invariant
              (runMatchingCell shared leftAcc (composePath gLow rightAcc) cellAlphaUpper)
              (composePath leftAcc fHigh) rightAcc cellBeta index belowBetaWindow
              (Nat.lt_of_lt_of_le belowBetaWindow
                (Nat.le_trans
                  (Nat.le_add_right (composePath leftAcc fHigh).length gLow.length)
                  rangeBetaFirst))).1
            have alphaWindowRead := alphaWindowCongruence.1 windowOffset insideAlphaWindow
            rw [windowOffsetEq] at alphaWindowRead
            rw [alphaWindowRead, betaFirstPrefix]
            exact (blockRotate_eq_freshShiftAbove_ofFirstBlockRange shared.nextFresh
              (cellFreshCount cellAlphaUpper) (cellFreshCount cellBeta)
              (natListGetAt (runMatchingCell shared leftAcc (composePath gLow rightAcc)
                cellAlphaUpper).openWires index) (alphaFirstValueBelow index)).symm
        | inr atOrPastAlphaWindow =>
            obtain ⟨betaOffset, betaOffsetEq⟩ := Nat.le.dest atOrPastAlphaWindow
            -- order-2 reads past its upper-alpha output window shift back to the beta-run state
            have alphaSecondSuffix := (runMatchingCell_openWiresSuffix_invariant leftAcc
              (composePath gMid rightAcc) cellAlphaUpper
              (runMatchingCell shared (composePath leftAcc fMid) rightAcc cellBeta)
              alphaCupCap rangeAlphaSecond).1 betaOffset
            rw [Nat.add_right_comm leftAcc.length betaOffset fHigh.length,
              Nat.add_assoc leftAcc.length fHigh.length betaOffset, betaOffsetEq,
              windowOffsetEq] at alphaSecondSuffix
            rw [alphaSecondSuffix]
            cases Nat.lt_or_ge betaOffset gMid.length with
            | inl insideBetaWindow =>
                -- ZONE 3 (beta window): the two-position congruence at delta = wA, rotation undoes
                have betaWindowRead := betaWindowCongruence.1 betaOffset insideBetaWindow
                rw [composePath_length leftAcc fHigh, composePath_length leftAcc fMid,
                  Nat.add_assoc leftAcc.length fHigh.length betaOffset, betaOffsetEq,
                  windowOffsetEq,
                  Nat.add_right_comm leftAcc.length fMid.length betaOffset] at betaWindowRead
                rw [betaWindowRead]
                exact (blockRotate_freshShiftAbove_eq_self_ofSecondBlockRange
                  shared.nextFresh (cellFreshCount cellAlphaUpper) (cellFreshCount cellBeta)
                  (natListGetAt (runMatchingCell shared (composePath leftAcc fMid) rightAcc
                    cellBeta).openWires (leftAcc.length + betaOffset + fMid.length))
                  (betaSecondValueBelow (leftAcc.length + betaOffset + fMid.length))).symm
            | inr atOrPastBetaWindow =>
                -- ZONE 4 (suffix): both orders shift the same pre-swap read into place
                obtain ⟨suffixOffset, suffixOffsetEq⟩ := Nat.le.dest atOrPastBetaWindow
                have betaSecondSuffix := (runMatchingCell_openWiresSuffix_invariant
                  (composePath leftAcc fMid) rightAcc cellBeta shared betaCupCap
                  rangeBetaSecond).1 suffixOffset
                rw [composePath_length leftAcc fMid,
                  Nat.add_right_comm (leftAcc.length + fMid.length) suffixOffset gMid.length,
                  Nat.add_right_comm leftAcc.length fMid.length gMid.length,
                  Nat.add_right_comm (leftAcc.length + gMid.length) fMid.length suffixOffset,
                  Nat.add_assoc leftAcc.length gMid.length suffixOffset,
                  suffixOffsetEq] at betaSecondSuffix
                rw [betaSecondSuffix]
                have betaFirstSuffix := (runMatchingCell_openWiresSuffix_invariant
                  (composePath leftAcc fHigh) rightAcc cellBeta
                  (runMatchingCell shared leftAcc (composePath gLow rightAcc) cellAlphaUpper)
                  betaCupCap rangeBetaFirst).1 suffixOffset
                rw [composePath_length leftAcc fHigh,
                  Nat.add_assoc (leftAcc.length + fHigh.length) suffixOffset gMid.length,
                  Nat.add_comm suffixOffset gMid.length,
                  suffixOffsetEq,
                  Nat.add_assoc leftAcc.length fHigh.length betaOffset,
                  betaOffsetEq, windowOffsetEq,
                  Nat.add_assoc (leftAcc.length + fHigh.length) suffixOffset gLow.length,
                  Nat.add_right_comm leftAcc.length fHigh.length
                    (suffixOffset + gLow.length)] at betaFirstSuffix
                have alphaFirstSuffix := (runMatchingCell_openWiresSuffix_invariant leftAcc
                  (composePath gLow rightAcc) cellAlphaUpper shared alphaCupCap
                  rangeAlphaFirst).1 (suffixOffset + gLow.length)
                rw [alphaFirstSuffix] at betaFirstSuffix
                rw [← Nat.add_assoc leftAcc.length suffixOffset gLow.length,
                  Nat.add_right_comm (leftAcc.length + suffixOffset) gLow.length fMid.length,
                  Nat.add_right_comm leftAcc.length suffixOffset fMid.length] at betaFirstSuffix
                rw [betaFirstSuffix,
                  blockRotate_below shared.nextFresh (cellFreshCount cellAlphaUpper)
                    (cellFreshCount cellBeta)
                    (natListGetAt shared.openWires
                      (leftAcc.length + fMid.length + suffixOffset + gLow.length))
                    (sharedValueBelow
                      (leftAcc.length + fMid.length + suffixOffset + gLow.length))]

/-! ## Honesty marker -/

/-- **Honesty marker — the block-swap `openMap` is PROVED at the two-block-core granularity.**
`matchingCoreSwap_openWires_blockRotate`: from a fresh state with both windows in range, the reduct
core's open wires (beta then upper-alpha) are exactly the `blockRotate nf wA wB` image of the redex
core's (upper-alpha then beta) — assembled pointwise over four zones (fixed prefix, shifted alpha
window via the window congruence at `delta = wB`, un-shifted beta window via the TWO-POSITION congruence
at `delta = wA`, fixed suffix), with the rotation/shift agreement lemmas bridging the zone values.  NOT
yet covered: the remaining sigma-witness fields (`componentComm` via the join-swap/lift kit, `loopsEq`
via the exchange law), their bundling into `MatchingComponentSim`, and the instantiation at the
post-`cellAlpha` shared state feeding `MatchingGodementComponentCoreSwap` — the next bricks.  `= true`. -/
def fxMode_hasMatchingBlockSwapOpenWiresWitness : Bool := true

end FX1Poly.Polygraph
