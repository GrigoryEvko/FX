import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingRenameSupport
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingBlockSwapAssembly

/-! # mode-3 keystone — the cross-order trace assembly (`blockRotate` relates the transposed traces)

The sigma witness's remaining fields (`componentComm` / `loopsEq`) compare the two transposed
Godement run orders through their JOIN-EVENT TRACES.  This file proves the trace-level
correspondence at the two-block-core setup:

  * alpha block — order-2 runs upper-alpha AFTER beta, at counter `nf + wB` on the same window,
    so its trace is the `freshShiftAbove nf wB` image of order-1's (the trace congruence at
    `delta = wB`); order-1's alpha values lie below `nf + wA` (`valuesBounded`), where the
    rotation IS that shift — so order-2's alpha trace is the `blockRotate` image of order-1's;
  * beta block — order-1 runs beta AFTER upper-alpha (below `fHigh`) where order-2 runs it
    FIRST (below `fMid`), so order-1's trace is the `freshShiftAbove nf wA` image of order-2's
    (the TWO-POSITION congruence at `delta = wA`); order-2's beta values lie below `nf + wB`,
    where the rotation UNDOES that shift — so order-2's beta trace is again the `blockRotate`
    image of order-1's;
  * combined — order-2's full trace (beta then alpha) is the `blockRotate` image of order-1's
    trace REORDERED as beta-block ++ alpha-block.  The next brick composes this with the
    membership block exchange and the base rename correspondence into `componentComm`/`loopsEq`.

Raw Lean 4 + Init; structural recursion only; per-declaration `#assert_no_axioms` gated in the
audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Pointwise map over a trace concatenation -/

/-- A pair-rename maps over a trace concatenation blockwise. -/
theorem listMapPairAppend (sigma : Nat → Nat) :
    (leftEvents rightEvents : List (Nat × Nat)) →
    (leftEvents ++ rightEvents).map (fun event => (sigma event.1, sigma event.2))
      = leftEvents.map (fun event => (sigma event.1, sigma event.2))
        ++ rightEvents.map (fun event => (sigma event.1, sigma event.2))
  | [], _ => rfl
  | (firstNode, secondNode) :: restLeft, rightEvents =>
      congrArg ((sigma firstNode, sigma secondNode) :: ·)
        (listMapPairAppend sigma restLeft rightEvents)

/-! ## Nat cancellation helper (hand-rolled; the core cancellation lemmas leak `propext`) -/

private theorem natAddLeCancelRight : (cancelled : Nat) → {leftSum rightSum : Nat} →
    leftSum + cancelled ≤ rightSum + cancelled → leftSum ≤ rightSum
  | 0, _, _, sumsLe => sumsLe
  | cancelled + 1, _, _, sumsLe => natAddLeCancelRight cancelled (Nat.le_of_succ_le_succ sumsLe)

/-! ## The per-block trace correspondences -/

/-- ★ **The alpha block's trace correspondence: order-2's upper-alpha trace is the `blockRotate`
image of order-1's.**  Order-2 runs upper-alpha at counter `nf + wB` on the same window (beta fired
above it), so the trace congruence at `delta = wB` gives the `freshShiftAbove nf wB` image; order-1's
alpha trace values lie below `nf + wA` (`valuesBounded`), where the rotation IS that shift. -/
theorem matchingCoreSwap_alphaTrace_blockRotate {signature : ModeSignature}
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
    spineJoinEvents (cellAlphaUpper.spineDiff leftAcc (composePath gMid rightAcc) [])
        (runMatchingCell shared (composePath leftAcc fMid) rightAcc cellBeta)
      = (spineJoinEvents (cellAlphaUpper.spineDiff leftAcc (composePath gLow rightAcc) [])
            shared).map
          (fun event => (blockRotate shared.nextFresh (cellFreshCount cellAlphaUpper)
              (cellFreshCount cellBeta) event.1,
            blockRotate shared.nextFresh (cellFreshCount cellAlphaUpper)
              (cellFreshCount cellBeta) event.2)) := by
  -- window ranges for the S-side (shared) and T-side (post-beta) runs
  have rangeAlphaFirst : leftAcc.length + fMid.length ≤ shared.openWires.length :=
    Nat.le_trans (Nat.le_add_right (leftAcc.length + fMid.length) gLow.length) windowsInRange
  have rangeBetaSecond : (composePath leftAcc fMid).length + gLow.length
      ≤ shared.openWires.length := by
    rw [composePath_length leftAcc fMid]
    exact windowsInRange
  have countBetaSecond := (runMatchingCell_openWiresSuffix_invariant (composePath leftAcc fMid)
    rightAcc cellBeta shared betaCupCap rangeBetaSecond).2
  have rangeAlphaSecond : leftAcc.length + fMid.length
      ≤ (runMatchingCell shared (composePath leftAcc fMid) rightAcc
          cellBeta).openWires.length := by
    have padded : leftAcc.length + fMid.length + gLow.length
        ≤ (runMatchingCell shared (composePath leftAcc fMid) rightAcc
            cellBeta).openWires.length + gLow.length := by
      rw [countBetaSecond]
      exact Nat.le_trans windowsInRange (Nat.le_add_right shared.openWires.length gMid.length)
    exact natAddLeCancelRight gLow.length padded
  -- the alpha window reads at the post-beta state are the fresh-shifted shared reads
  have sharedValueBelow : ∀ index, natListGetAt shared.openWires index < shared.nextFresh :=
    fun index => natListGetAt_lt shared.nextFresh nfPos shared.openWires index sharedFresh.1
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
  -- the trace congruence at delta = wB
  have shiftTraceAlpha := runMatchingCell_joinEvents_freshShift shared.nextFresh
    (cellFreshCount cellBeta) leftAcc leftAcc (composePath gLow rightAcc)
    (composePath gMid rightAcc) cellAlphaUpper shared
    (runMatchingCell shared (composePath leftAcc fMid) rightAcc cellBeta) alphaCupCap
    windowMapAlpha (runMatchingCell_nextFresh shared (composePath leftAcc fMid) rightAcc cellBeta)
    (Nat.le_refl shared.nextFresh) rangeAlphaFirst rangeAlphaSecond
  rw [shiftTraceAlpha]
  -- on values below nf + wA the rotation IS the shift by wB
  refine listMapPairCongr_onMembers
    (freshShiftAbove shared.nextFresh (cellFreshCount cellBeta))
    (blockRotate shared.nextFresh (cellFreshCount cellAlphaUpper) (cellFreshCount cellBeta))
    (spineJoinEvents (cellAlphaUpper.spineDiff leftAcc (composePath gLow rightAcc) []) shared)
    ?_
  intro firstNode secondNode membership
  have valueBounds := runMatchingCell_joinEvents_valuesBounded shared leftAcc
    (composePath gLow rightAcc) cellAlphaUpper sharedFresh nfPos firstNode secondNode membership
  rw [runMatchingCell_nextFresh shared leftAcc (composePath gLow rightAcc) cellAlphaUpper]
    at valueBounds
  exact ⟨(blockRotate_eq_freshShiftAbove_ofFirstBlockRange shared.nextFresh
      (cellFreshCount cellAlphaUpper) (cellFreshCount cellBeta) firstNode valueBounds.1).symm,
    (blockRotate_eq_freshShiftAbove_ofFirstBlockRange shared.nextFresh
      (cellFreshCount cellAlphaUpper) (cellFreshCount cellBeta) secondNode valueBounds.2).symm⟩

/-- ★ **The beta block's trace correspondence: order-2's beta trace is the `blockRotate` image of
order-1's.**  The two-position trace congruence at `delta = wA` (beta fires below `fHigh` in order-1
but below `fMid` in order-2) gives order-1's trace as the `freshShiftAbove nf wA` image of order-2's;
order-2's beta values lie below `nf + wB` (`valuesBounded`), where the rotation UNDOES that shift —
so mapping the rotation over order-1's trace recovers order-2's. -/
theorem matchingCoreSwap_betaTrace_blockRotate {signature : ModeSignature}
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
    spineJoinEvents (cellBeta.spineDiff (composePath leftAcc fMid) rightAcc []) shared
      = (spineJoinEvents (cellBeta.spineDiff (composePath leftAcc fHigh) rightAcc [])
            (runMatchingCell shared leftAcc (composePath gLow rightAcc) cellAlphaUpper)).map
          (fun event => (blockRotate shared.nextFresh (cellFreshCount cellAlphaUpper)
              (cellFreshCount cellBeta) event.1,
            blockRotate shared.nextFresh (cellFreshCount cellAlphaUpper)
              (cellFreshCount cellBeta) event.2)) := by
  -- window ranges for the S-side (shared) and T-side (post-alpha) runs
  have rangeAlphaFirst : leftAcc.length + fMid.length ≤ shared.openWires.length :=
    Nat.le_trans (Nat.le_add_right (leftAcc.length + fMid.length) gLow.length) windowsInRange
  have rangeBetaSecond : (composePath leftAcc fMid).length + gLow.length
      ≤ shared.openWires.length := by
    rw [composePath_length leftAcc fMid]
    exact windowsInRange
  have countAlphaFirst := (runMatchingCell_openWiresSuffix_invariant leftAcc
    (composePath gLow rightAcc) cellAlphaUpper shared alphaCupCap rangeAlphaFirst).2
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
  -- the beta window reads at the post-alpha state are the fresh-shifted shared reads (two-position)
  have sharedValueBelow : ∀ index, natListGetAt shared.openWires index < shared.nextFresh :=
    fun index => natListGetAt_lt shared.nextFresh nfPos shared.openWires index sharedFresh.1
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
  -- the two-position trace congruence at delta = wA: order-1's trace = shift of order-2's
  have shiftTraceBeta := runMatchingCell_joinEvents_freshShift shared.nextFresh
    (cellFreshCount cellAlphaUpper) (composePath leftAcc fMid) (composePath leftAcc fHigh)
    rightAcc rightAcc cellBeta shared
    (runMatchingCell shared leftAcc (composePath gLow rightAcc) cellAlphaUpper) betaCupCap
    windowMapBeta (runMatchingCell_nextFresh shared leftAcc (composePath gLow rightAcc)
      cellAlphaUpper)
    (Nat.le_refl shared.nextFresh) rangeBetaSecond rangeBetaFirst
  rw [shiftTraceBeta,
    listMapPairCompose
      (blockRotate shared.nextFresh (cellFreshCount cellAlphaUpper) (cellFreshCount cellBeta))
      (freshShiftAbove shared.nextFresh (cellFreshCount cellAlphaUpper))
      (spineJoinEvents (cellBeta.spineDiff (composePath leftAcc fMid) rightAcc []) shared)]
  -- on values below nf + wB the rotation undoes the shift by wA
  refine (listMapPairEqSelf_onMembers
    (fun value => blockRotate shared.nextFresh (cellFreshCount cellAlphaUpper)
      (cellFreshCount cellBeta)
      (freshShiftAbove shared.nextFresh (cellFreshCount cellAlphaUpper) value))
    (spineJoinEvents (cellBeta.spineDiff (composePath leftAcc fMid) rightAcc []) shared)
    ?_).symm
  intro firstNode secondNode membership
  have valueBounds := runMatchingCell_joinEvents_valuesBounded shared
    (composePath leftAcc fMid) rightAcc cellBeta sharedFresh nfPos firstNode secondNode
    membership
  rw [runMatchingCell_nextFresh shared (composePath leftAcc fMid) rightAcc cellBeta]
    at valueBounds
  exact ⟨blockRotate_freshShiftAbove_eq_self_ofSecondBlockRange shared.nextFresh
      (cellFreshCount cellAlphaUpper) (cellFreshCount cellBeta) firstNode valueBounds.1,
    blockRotate_freshShiftAbove_eq_self_ofSecondBlockRange shared.nextFresh
      (cellFreshCount cellAlphaUpper) (cellFreshCount cellBeta) secondNode valueBounds.2⟩

/-! ## The combined trace correspondence -/

/-- ★ **The full cross-order trace correspondence: order-2's trace (beta then alpha) is the
`blockRotate` image of order-1's trace REORDERED as beta-block ++ alpha-block.**  The remaining
distance to `componentComm`/`loopsEq` is pure block EXCHANGE (beta ++ alpha vs alpha ++ beta),
discharged by the banked membership/count exchange laws over the shared base — the next brick. -/
theorem matchingCoreSwap_joinEvents_blockRotate {signature : ModeSignature}
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
    spineJoinEvents (cellBeta.spineDiff (composePath leftAcc fMid) rightAcc []) shared
      ++ spineJoinEvents (cellAlphaUpper.spineDiff leftAcc (composePath gMid rightAcc) [])
          (runMatchingCell shared (composePath leftAcc fMid) rightAcc cellBeta)
      = (spineJoinEvents (cellBeta.spineDiff (composePath leftAcc fHigh) rightAcc [])
            (runMatchingCell shared leftAcc (composePath gLow rightAcc) cellAlphaUpper)
          ++ spineJoinEvents (cellAlphaUpper.spineDiff leftAcc (composePath gLow rightAcc) [])
              shared).map
          (fun event => (blockRotate shared.nextFresh (cellFreshCount cellAlphaUpper)
              (cellFreshCount cellBeta) event.1,
            blockRotate shared.nextFresh (cellFreshCount cellAlphaUpper)
              (cellFreshCount cellBeta) event.2)) := by
  rw [matchingCoreSwap_betaTrace_blockRotate cellAlphaUpper cellBeta leftAcc rightAcc shared
      alphaCupCap betaCupCap sharedFresh nfPos windowsInRange,
    matchingCoreSwap_alphaTrace_blockRotate cellAlphaUpper cellBeta leftAcc rightAcc shared
      alphaCupCap betaCupCap sharedFresh nfPos windowsInRange,
    listMapPairAppend
      (blockRotate shared.nextFresh (cellFreshCount cellAlphaUpper) (cellFreshCount cellBeta))
      (spineJoinEvents (cellBeta.spineDiff (composePath leftAcc fHigh) rightAcc [])
        (runMatchingCell shared leftAcc (composePath gLow rightAcc) cellAlphaUpper))
      (spineJoinEvents (cellAlphaUpper.spineDiff leftAcc (composePath gLow rightAcc) [])
        shared)]

/-! ## Honesty marker -/

/-- **Honesty marker — the cross-order trace correspondence is PROVED at the two-block-core
granularity.**  `matchingCoreSwap_alphaTrace_blockRotate` / `matchingCoreSwap_betaTrace_blockRotate`
(each block's order-2 trace is the `blockRotate` image of order-1's, via the trace congruence at the
block's own delta plus the value-bound rotation/shift agreement) and
`matchingCoreSwap_joinEvents_blockRotate` (the combined reordered-trace correspondence).  NOT yet
covered: composing this with the membership block exchange and the base rename correspondence into
the `componentComm`/`loopsEq` fields and bundling `MatchingComponentSim` — the next brick.
`= true`. -/
def fxMode_hasMatchingTraceBlockRotateWitness : Bool := true

end FX1Poly.Polygraph
