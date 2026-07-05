import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcParityIndexForm
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcParityFold
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingScanFallback

/-! # ArcCupFoldedLegSwap — the leg-swap kill at the two folded cup runs (peel campaign H, parity rung P-5b)

The index-form refutation (`arcPartnerLegSwap_impossible`) speaks abstract parity states;
this brick lands it on the two CHAINED FOLDED RUNS of the cup-head cancellation.  Both runs
fold from the padded seed at `bottomCount + 2`, so the parity capstone
(`arcEndTokenParity_ofChainedSpineList`) supplies the invariant on each, the shifted probe
is in the padded range, and the shift never hits a window leg — every hypothesis of the
kill discharges structurally.  On top of the kill sits the positive corollary the partner
cancel consumes (`arcCupFoldedLegAttachment_agrees`): when a shifted probe fuses to a
window leg in BOTH runs, it fuses to the SAME leg — the two fused branches of the
composite partner transport can no longer cover for each other.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private plumbing (per-file copy, following the codebase pattern) -/

/-- A composite-range index two-zone-shifts into the padded fresh range. -/
private theorem shiftIndexWithinFreshTotal (windowPosition bottomCount freshLength index : Nat)
    (indexInRange : index < bottomCount + freshLength) :
    freshShiftAbove windowPosition 2 index < bottomCount + 2 + freshLength := by
  cases Nat.lt_or_ge index windowPosition with
  | inl below =>
      rw [freshShiftAbove_ofNotLe windowPosition 2 index
        (fun windowLe => Nat.lt_irrefl windowPosition
          (Nat.lt_of_le_of_lt windowLe below))]
      exact Nat.lt_of_lt_of_le indexInRange
        (Nat.le_trans (Nat.le_add_right (bottomCount + freshLength) 2)
          (Nat.le_of_eq (Nat.add_right_comm bottomCount freshLength 2)))
  | inr atOrPast =>
      rw [freshShiftAbove_ofLe windowPosition 2 index atOrPast]
      exact Nat.lt_of_lt_of_le (Nat.add_lt_add_right indexInRange 2)
        (Nat.le_of_eq (Nat.add_right_comm bottomCount freshLength 2))

/-! ## The leg-swap kill at the folded runs -/

/-- ★ **The cross-run leg swap is impossible AT THE FOLDED RUNS.**  No composite index's
shifted probe can partner to the cup's left window leg in one chained run and to the right
leg in another: the parity capstone supplies the opposite-class invariant on both folded
states, and the run-independent index class forces the contradiction.  This is the exact
discrepancy the composite partner transport's two fused branches cannot distinguish — the
counter-scenario that refuted the unconditional cup cancel — now excluded on the
disciplined chained fragment. -/
theorem arcCupFoldedLegSwap_impossible
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat)
    (windowFits : windowPosition ≤ bottomCount)
    (firstAtoms secondAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (firstChained : SpineBoundaryChained (bottomCount + 2) firstAtoms)
    (secondChained : SpineBoundaryChained (bottomCount + 2) secondAtoms)
    (compositeIndex : Nat)
    (indexInRangeFirst : compositeIndex
      < bottomCount
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          firstAtoms).openWires.length)
    (indexInRangeSecond : compositeIndex
      < bottomCount
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          secondAtoms).openWires.length)
    (firstPartnerAtLeft : partnerIndexOf
        (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          firstAtoms).links
        (List.range (bottomCount + 2)
          ++ (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            firstAtoms).openWires)
        (bottomCount + 2
          + (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            firstAtoms).openWires.length)
        (freshShiftAbove windowPosition 2 compositeIndex) = windowPosition)
    (secondPartnerAtRight : partnerIndexOf
        (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          secondAtoms).links
        (List.range (bottomCount + 2)
          ++ (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            secondAtoms).openWires)
        (bottomCount + 2
          + (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            secondAtoms).openWires.length)
        (freshShiftAbove windowPosition 2 compositeIndex) = windowPosition + 1) :
    False := by
  have probeInRangeFirst := shiftIndexWithinFreshTotal windowPosition bottomCount
    (processArcSpine
      (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
      firstAtoms).openWires.length
    compositeIndex indexInRangeFirst
  have probeInRangeSecond := shiftIndexWithinFreshTotal windowPosition bottomCount
    (processArcSpine
      (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
      secondAtoms).openWires.length
    compositeIndex indexInRangeSecond
  exact arcPartnerLegSwap_impossible AdjunctionMode.base (bottomCount + 2)
    (processArcSpine
      (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
      firstAtoms)
    (processArcSpine
      (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
      secondAtoms)
    (arcEndTokenParity_ofChainedSpineList AdjunctionMode.base (bottomCount + 2)
      firstAtoms firstChained)
    (arcEndTokenParity_ofChainedSpineList AdjunctionMode.base (bottomCount + 2)
      secondAtoms secondChained)
    windowPosition (freshShiftAbove windowPosition 2 compositeIndex)
    (Nat.succ_lt_succ (Nat.lt_succ_of_le windowFits))
    (Ne.symm (freshShiftAbove_neWindow windowPosition compositeIndex))
    (Ne.symm (freshShiftAbove_neWindowSucc windowPosition compositeIndex))
    probeInRangeFirst probeInRangeSecond firstPartnerAtLeft secondPartnerAtRight

/-! ## The positive corollary: fused attachments agree across runs -/

/-- ★ **A probe fused in both runs fuses to the SAME leg.**  When a composite index's
shifted probe partners to a window leg in each of two chained runs, the legs coincide: the
two matching cases chain directly, and the two mixed cases are the leg swap — killed.
This is the agreement the composite partner transport needs to stop its fused branches
covering for each other. -/
theorem arcCupFoldedLegAttachment_agrees
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat)
    (windowFits : windowPosition ≤ bottomCount)
    (firstAtoms secondAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (firstChained : SpineBoundaryChained (bottomCount + 2) firstAtoms)
    (secondChained : SpineBoundaryChained (bottomCount + 2) secondAtoms)
    (compositeIndex : Nat)
    (indexInRangeFirst : compositeIndex
      < bottomCount
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          firstAtoms).openWires.length)
    (indexInRangeSecond : compositeIndex
      < bottomCount
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          secondAtoms).openWires.length)
    (firstFused : partnerIndexOf
        (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          firstAtoms).links
        (List.range (bottomCount + 2)
          ++ (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            firstAtoms).openWires)
        (bottomCount + 2
          + (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            firstAtoms).openWires.length)
        (freshShiftAbove windowPosition 2 compositeIndex) = windowPosition
      ∨ partnerIndexOf
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            firstAtoms).links
          (List.range (bottomCount + 2)
            ++ (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              firstAtoms).openWires)
          (bottomCount + 2
            + (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              firstAtoms).openWires.length)
          (freshShiftAbove windowPosition 2 compositeIndex) = windowPosition + 1)
    (secondFused : partnerIndexOf
        (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          secondAtoms).links
        (List.range (bottomCount + 2)
          ++ (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            secondAtoms).openWires)
        (bottomCount + 2
          + (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            secondAtoms).openWires.length)
        (freshShiftAbove windowPosition 2 compositeIndex) = windowPosition
      ∨ partnerIndexOf
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            secondAtoms).links
          (List.range (bottomCount + 2)
            ++ (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              secondAtoms).openWires)
          (bottomCount + 2
            + (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              secondAtoms).openWires.length)
          (freshShiftAbove windowPosition 2 compositeIndex) = windowPosition + 1) :
    partnerIndexOf
        (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          firstAtoms).links
        (List.range (bottomCount + 2)
          ++ (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            firstAtoms).openWires)
        (bottomCount + 2
          + (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            firstAtoms).openWires.length)
        (freshShiftAbove windowPosition 2 compositeIndex)
      = partnerIndexOf
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            secondAtoms).links
          (List.range (bottomCount + 2)
            ++ (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              secondAtoms).openWires)
          (bottomCount + 2
            + (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              secondAtoms).openWires.length)
          (freshShiftAbove windowPosition 2 compositeIndex) := by
  cases firstFused with
  | inl firstAtLeft =>
      cases secondFused with
      | inl secondAtLeft => exact firstAtLeft.trans secondAtLeft.symm
      | inr secondAtRight =>
          exact False.elim (arcCupFoldedLegSwap_impossible bottomCount windowPosition
            windowFits firstAtoms secondAtoms firstChained secondChained compositeIndex
            indexInRangeFirst indexInRangeSecond firstAtLeft secondAtRight)
  | inr firstAtRight =>
      cases secondFused with
      | inl secondAtLeft =>
          exact False.elim (arcCupFoldedLegSwap_impossible bottomCount windowPosition
            windowFits secondAtoms firstAtoms secondChained firstChained compositeIndex
            indexInRangeSecond indexInRangeFirst secondAtLeft firstAtRight)
      | inr secondAtRight => exact firstAtRight.trans secondAtRight.symm

/-! ## Honesty marker -/

/-- **Honesty marker — the folded leg-swap kill is SHIPPED (peel campaign H, parity rung
P-5b).**  The cross-run leg swap is impossible at the two chained folded runs
(`arcCupFoldedLegSwap_impossible` — the parity capstone discharges the invariant on both,
the shift discipline discharges the probe side conditions), and a probe fused in both runs
fuses to the SAME leg (`arcCupFoldedLegAttachment_agrees`).  What this marker does NOT
claim: the fresh partner cancel assembled over the composite dispatch equality (the
off-fused and mixed cells) and the orbit-realignment endgame.  `= true`. -/
def fxMode_hasArcCupFoldedLegSwap : Bool := true

end FX1Poly.Polygraph
