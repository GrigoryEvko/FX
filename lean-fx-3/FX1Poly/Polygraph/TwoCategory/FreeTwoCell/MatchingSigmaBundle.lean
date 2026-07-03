import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingTraceAssembly
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingJoinEventExchange

/-! # mode-3 keystone — the sigma-witness bundle (`MatchingComponentSim` at the two-block core)

The capstone composition of the A2c-4 campaign: from a fresh forest state with both blocks'
windows in range, the two transposed Godement run orders (upper-alpha then beta vs beta then
upper-alpha) are `MatchingComponentSim`-related by `blockRotate nf wA wB`.  Every field is a
banked leg:

  * `openMap` — the four-zone pointwise wire assembly (`matchingCoreSwap_openWires_blockRotate`);
  * `nfEq` — both orders bump the counter by `wA + wB` (commutativity of the two widths);
  * `componentComm` — both orders' links are event folds over the SHARED state
    (`runMatchingCell_links_eq_applyJoinEvents` + `applyJoinEvents_append`), order-2's trace is
    the `blockRotate` image of order-1's reordered trace (`matchingCoreSwap_joinEvents_blockRotate`),
    the rename is invisible at the shared base (`componentView_ofFreshRename` — fresh links,
    below-fixing / above-keeping / injective rotation), the fold transports the view
    (`componentView_applyJoinEvents`), and the block transposition is invisible to the view
    (`componentView_applyJoinEvents_append_comm`);
  * `loopsEq` — the same chain at the loop-count level (`countJoinEventLoops_append` /
    `_map_congr` / `_append_comm`);
  * forests — the join fold preserves the forest invariant.

NOT yet the `MatchingGodementComponentCoreSwap` ∃-discharge: that wrapper still owes the
`bottomCount`/`fixesAbove` conjuncts and the range/cup-cap hypothesis handling at the
post-`cellAlpha` shared state — the next bricks.

Raw Lean 4 + Init; structural recursion only; per-declaration `#assert_no_axioms` gated in the
audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The rotation keeps at-or-above ids at-or-above (the base-correspondence side condition) -/

/-- The block rotation keeps at-or-above-window ids at-or-above the window base: the first block
shifts up, the second block lands on `[base, base + w2)` (still at-or-above), and everything past
the window is fixed. -/
theorem blockRotate_mapsAtOrAboveWithin (lowerBase firstWidth secondWidth : Nat) :
    ∀ identifier, lowerBase ≤ identifier →
    lowerBase ≤ blockRotate lowerBase firstWidth secondWidth identifier := by
  intro identifier atOrAbove
  cases Nat.lt_or_ge identifier (lowerBase + firstWidth) with
  | inl belowFirstTop =>
      rw [blockRotate_firstBlock lowerBase firstWidth secondWidth identifier atOrAbove
        belowFirstTop]
      exact Nat.le_trans atOrAbove (Nat.le_add_right identifier secondWidth)
  | inr atOrAboveFirstTop =>
      cases Nat.lt_or_ge identifier (lowerBase + firstWidth + secondWidth) with
      | inl belowWindowTop =>
          obtain ⟨difference, differenceEq⟩ := Nat.le.dest atOrAboveFirstTop
          rw [blockRotate_secondBlock lowerBase firstWidth secondWidth identifier
              atOrAboveFirstTop belowWindowTop, ← differenceEq,
            Nat.add_right_comm lowerBase firstWidth difference,
            addSubCancelRight (lowerBase + difference) firstWidth]
          exact Nat.le_add_right lowerBase difference
      | inr atOrAboveWindowTop =>
          rw [blockRotate_above lowerBase firstWidth secondWidth identifier atOrAboveWindowTop]
          exact atOrAbove

/-! ## The bundle -/

/-- ★ **The sigma-witness bundle: the two transposed Godement run orders are
`MatchingComponentSim`-related by `blockRotate`.**  The capstone composition of the banked legs —
see the file header for the field-by-field map. -/
theorem matchingCoreSwap_componentSim_blockRotate {signature : ModeSignature}
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
    (sharedForest : isUnionFindForest shared.links)
    (windowsInRange : leftAcc.length + fMid.length + gLow.length ≤ shared.openWires.length) :
    MatchingComponentSim
      (blockRotate shared.nextFresh (cellFreshCount cellAlphaUpper) (cellFreshCount cellBeta))
      (runMatchingCell (runMatchingCell shared leftAcc (composePath gLow rightAcc)
          cellAlphaUpper) (composePath leftAcc fHigh) rightAcc cellBeta)
      (runMatchingCell (runMatchingCell shared (composePath leftAcc fMid) rightAcc cellBeta)
        leftAcc (composePath gMid rightAcc) cellAlphaUpper) := by
  -- freshness at the two middle states (for the loops faithfulness)
  have afterA1Fresh : WireStateFresh
      (runMatchingCell shared leftAcc (composePath gLow rightAcc) cellAlphaUpper) :=
    runMatchingCell_wireStateFresh shared leftAcc (composePath gLow rightAcc) cellAlphaUpper
      sharedFresh nfPos
  have afterA1NfPos : 0 < (runMatchingCell shared leftAcc (composePath gLow rightAcc)
      cellAlphaUpper).nextFresh :=
    Nat.lt_of_lt_of_le nfPos
      (runMatchingCell_nextFresh_le shared leftAcc (composePath gLow rightAcc) cellAlphaUpper)
  have afterB2Fresh : WireStateFresh
      (runMatchingCell shared (composePath leftAcc fMid) rightAcc cellBeta) :=
    runMatchingCell_wireStateFresh shared (composePath leftAcc fMid) rightAcc cellBeta
      sharedFresh nfPos
  have afterB2NfPos : 0 < (runMatchingCell shared (composePath leftAcc fMid) rightAcc
      cellBeta).nextFresh :=
    Nat.lt_of_lt_of_le nfPos
      (runMatchingCell_nextFresh_le shared (composePath leftAcc fMid) rightAcc cellBeta)
  -- the base correspondence: the rotation is invisible to the shared component view
  have baseCorrespondence : ∀ probeOne probeTwo : Nat,
      (unionFindRootOf shared.links (blockRotate shared.nextFresh
            (cellFreshCount cellAlphaUpper) (cellFreshCount cellBeta) probeOne)
          == unionFindRootOf shared.links (blockRotate shared.nextFresh
            (cellFreshCount cellAlphaUpper) (cellFreshCount cellBeta) probeTwo))
        = (unionFindRootOf shared.links probeOne == unionFindRootOf shared.links probeTwo) :=
    fun probeOne probeTwo =>
      componentView_ofFreshRename
        (blockRotate shared.nextFresh (cellFreshCount cellAlphaUpper)
          (cellFreshCount cellBeta))
        shared.nextFresh shared.links sharedFresh.2
        (blockRotate_below shared.nextFresh (cellFreshCount cellAlphaUpper)
          (cellFreshCount cellBeta))
        (blockRotate_mapsAtOrAboveWithin shared.nextFresh (cellFreshCount cellAlphaUpper)
          (cellFreshCount cellBeta))
        (blockRotate_inj shared.nextFresh (cellFreshCount cellAlphaUpper)
          (cellFreshCount cellBeta))
        probeOne probeTwo
  -- both orders' links as event folds over the SHARED state
  have linksSEq : (runMatchingCell (runMatchingCell shared leftAcc (composePath gLow rightAcc)
        cellAlphaUpper) (composePath leftAcc fHigh) rightAcc cellBeta).links
      = applyJoinEvents
          (spineJoinEvents (cellAlphaUpper.spineDiff leftAcc (composePath gLow rightAcc) [])
              shared
            ++ spineJoinEvents (cellBeta.spineDiff (composePath leftAcc fHigh) rightAcc [])
                (runMatchingCell shared leftAcc (composePath gLow rightAcc) cellAlphaUpper))
          shared.links := by
    rw [runMatchingCell_links_eq_applyJoinEvents
        (runMatchingCell shared leftAcc (composePath gLow rightAcc) cellAlphaUpper)
        (composePath leftAcc fHigh) rightAcc cellBeta,
      runMatchingCell_links_eq_applyJoinEvents shared leftAcc (composePath gLow rightAcc)
        cellAlphaUpper,
      applyJoinEvents_append]
  have linksTEq : (runMatchingCell (runMatchingCell shared (composePath leftAcc fMid) rightAcc
        cellBeta) leftAcc (composePath gMid rightAcc) cellAlphaUpper).links
      = applyJoinEvents
          ((spineJoinEvents (cellBeta.spineDiff (composePath leftAcc fHigh) rightAcc [])
              (runMatchingCell shared leftAcc (composePath gLow rightAcc) cellAlphaUpper)
            ++ spineJoinEvents (cellAlphaUpper.spineDiff leftAcc (composePath gLow rightAcc) [])
                shared).map
            (fun event => (blockRotate shared.nextFresh (cellFreshCount cellAlphaUpper)
                (cellFreshCount cellBeta) event.1,
              blockRotate shared.nextFresh (cellFreshCount cellAlphaUpper)
                (cellFreshCount cellBeta) event.2)))
          shared.links := by
    rw [runMatchingCell_links_eq_applyJoinEvents
        (runMatchingCell shared (composePath leftAcc fMid) rightAcc cellBeta) leftAcc
        (composePath gMid rightAcc) cellAlphaUpper,
      runMatchingCell_links_eq_applyJoinEvents shared (composePath leftAcc fMid) rightAcc
        cellBeta,
      ← matchingCoreSwap_joinEvents_blockRotate cellAlphaUpper cellBeta leftAcc rightAcc shared
        alphaCupCap betaCupCap sharedFresh nfPos windowsInRange,
      applyJoinEvents_append]
  refine
    { openMap := matchingCoreSwap_openWires_blockRotate cellAlphaUpper cellBeta leftAcc rightAcc
        shared alphaCupCap betaCupCap sharedFresh nfPos windowsInRange
      nfEq := ?_
      componentComm := ?_
      loopsEq := ?_
      forestS := isUnionFindForest_runMatchingCell
        (runMatchingCell shared leftAcc (composePath gLow rightAcc) cellAlphaUpper)
        (composePath leftAcc fHigh) rightAcc cellBeta
        (isUnionFindForest_runMatchingCell shared leftAcc (composePath gLow rightAcc)
          cellAlphaUpper sharedForest)
      forestT := isUnionFindForest_runMatchingCell
        (runMatchingCell shared (composePath leftAcc fMid) rightAcc cellBeta)
        leftAcc (composePath gMid rightAcc) cellAlphaUpper
        (isUnionFindForest_runMatchingCell shared (composePath leftAcc fMid) rightAcc cellBeta
          sharedForest) }
  -- nfEq: both orders bump the counter by the two widths in either order
  · rw [runMatchingCell_nextFresh (runMatchingCell shared leftAcc (composePath gLow rightAcc)
        cellAlphaUpper) (composePath leftAcc fHigh) rightAcc cellBeta,
      runMatchingCell_nextFresh shared leftAcc (composePath gLow rightAcc) cellAlphaUpper,
      runMatchingCell_nextFresh (runMatchingCell shared (composePath leftAcc fMid) rightAcc
        cellBeta) leftAcc (composePath gMid rightAcc) cellAlphaUpper,
      runMatchingCell_nextFresh shared (composePath leftAcc fMid) rightAcc cellBeta,
      Nat.add_right_comm shared.nextFresh (cellFreshCount cellAlphaUpper)
        (cellFreshCount cellBeta)]
  -- componentComm: equivariance over the base correspondence, then the block exchange
  · intro probeOne probeTwo
    rw [linksTEq, linksSEq]
    have equivariant := componentView_applyJoinEvents
      (blockRotate shared.nextFresh (cellFreshCount cellAlphaUpper) (cellFreshCount cellBeta))
      (spineJoinEvents (cellBeta.spineDiff (composePath leftAcc fHigh) rightAcc [])
          (runMatchingCell shared leftAcc (composePath gLow rightAcc) cellAlphaUpper)
        ++ spineJoinEvents (cellAlphaUpper.spineDiff leftAcc (composePath gLow rightAcc) [])
            shared)
      shared.links shared.links sharedForest sharedForest baseCorrespondence probeOne probeTwo
    rw [equivariant]
    exact componentView_applyJoinEvents_append_comm
      (spineJoinEvents (cellBeta.spineDiff (composePath leftAcc fHigh) rightAcc [])
        (runMatchingCell shared leftAcc (composePath gLow rightAcc) cellAlphaUpper))
      (spineJoinEvents (cellAlphaUpper.spineDiff leftAcc (composePath gLow rightAcc) []) shared)
      shared.links sharedForest probeOne probeTwo
  -- loopsEq: the same chain at the loop-count level
  · rw [runMatchingCell_loops_eq_addJoinEventLoops
        (runMatchingCell shared (composePath leftAcc fMid) rightAcc cellBeta) leftAcc
        (composePath gMid rightAcc) cellAlphaUpper afterB2Fresh afterB2NfPos,
      runMatchingCell_loops_eq_addJoinEventLoops shared (composePath leftAcc fMid) rightAcc
        cellBeta sharedFresh nfPos,
      runMatchingCell_links_eq_applyJoinEvents shared (composePath leftAcc fMid) rightAcc
        cellBeta,
      runMatchingCell_loops_eq_addJoinEventLoops
        (runMatchingCell shared leftAcc (composePath gLow rightAcc) cellAlphaUpper)
        (composePath leftAcc fHigh) rightAcc cellBeta afterA1Fresh afterA1NfPos,
      runMatchingCell_loops_eq_addJoinEventLoops shared leftAcc (composePath gLow rightAcc)
        cellAlphaUpper sharedFresh nfPos,
      runMatchingCell_links_eq_applyJoinEvents shared leftAcc (composePath gLow rightAcc)
        cellAlphaUpper,
      Nat.add_assoc shared.loops
        (countJoinEventLoops
          (spineJoinEvents (cellBeta.spineDiff (composePath leftAcc fMid) rightAcc []) shared)
          shared.links)
        (countJoinEventLoops
          (spineJoinEvents (cellAlphaUpper.spineDiff leftAcc (composePath gMid rightAcc) [])
            (runMatchingCell shared (composePath leftAcc fMid) rightAcc cellBeta))
          (applyJoinEvents
            (spineJoinEvents (cellBeta.spineDiff (composePath leftAcc fMid) rightAcc []) shared)
            shared.links)),
      Nat.add_assoc shared.loops
        (countJoinEventLoops
          (spineJoinEvents (cellAlphaUpper.spineDiff leftAcc (composePath gLow rightAcc) [])
            shared)
          shared.links)
        (countJoinEventLoops
          (spineJoinEvents (cellBeta.spineDiff (composePath leftAcc fHigh) rightAcc [])
            (runMatchingCell shared leftAcc (composePath gLow rightAcc) cellAlphaUpper))
          (applyJoinEvents
            (spineJoinEvents (cellAlphaUpper.spineDiff leftAcc (composePath gLow rightAcc) [])
              shared)
            shared.links)),
      ← countJoinEventLoops_append
        (spineJoinEvents (cellBeta.spineDiff (composePath leftAcc fMid) rightAcc []) shared)
        (spineJoinEvents (cellAlphaUpper.spineDiff leftAcc (composePath gMid rightAcc) [])
          (runMatchingCell shared (composePath leftAcc fMid) rightAcc cellBeta))
        shared.links,
      ← countJoinEventLoops_append
        (spineJoinEvents (cellAlphaUpper.spineDiff leftAcc (composePath gLow rightAcc) [])
          shared)
        (spineJoinEvents (cellBeta.spineDiff (composePath leftAcc fHigh) rightAcc [])
          (runMatchingCell shared leftAcc (composePath gLow rightAcc) cellAlphaUpper))
        shared.links,
      matchingCoreSwap_joinEvents_blockRotate cellAlphaUpper cellBeta leftAcc rightAcc shared
        alphaCupCap betaCupCap sharedFresh nfPos windowsInRange,
      countJoinEventLoops_map_congr
        (blockRotate shared.nextFresh (cellFreshCount cellAlphaUpper) (cellFreshCount cellBeta))
        (spineJoinEvents (cellBeta.spineDiff (composePath leftAcc fHigh) rightAcc [])
            (runMatchingCell shared leftAcc (composePath gLow rightAcc) cellAlphaUpper)
          ++ spineJoinEvents (cellAlphaUpper.spineDiff leftAcc (composePath gLow rightAcc) [])
              shared)
        shared.links shared.links sharedForest sharedForest baseCorrespondence,
      countJoinEventLoops_append_comm
        (spineJoinEvents (cellBeta.spineDiff (composePath leftAcc fHigh) rightAcc [])
          (runMatchingCell shared leftAcc (composePath gLow rightAcc) cellAlphaUpper))
        (spineJoinEvents (cellAlphaUpper.spineDiff leftAcc (composePath gLow rightAcc) []) shared)
        shared.links sharedForest]

/-! ## Honesty marker -/

/-- **Honesty marker — the `MatchingComponentSim` sigma bundle is PROVED at the two-block-core
granularity.**  `matchingCoreSwap_componentSim_blockRotate`: from a fresh forest state with both
windows in range, the two transposed Godement run orders are component-simulated by
`blockRotate nf wA wB` — all six fields (openMap / nfEq / componentComm / loopsEq / two forests)
composed from the banked legs.  NOT yet covered: the `MatchingGodementComponentCoreSwap`
∃-discharge (the `bottomCount`/`fixesAbove` conjuncts and the range/cup-cap hypothesis handling at
the post-`cellAlpha` shared state) — the next bricks.  `= true`. -/
def fxMode_hasMatchingComponentSimBundle : Bool := true

end FX1Poly.Polygraph
