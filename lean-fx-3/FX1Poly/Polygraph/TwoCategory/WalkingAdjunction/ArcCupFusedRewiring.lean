import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupFusedBridge
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusCupHeadFolded
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupBoundaryReads
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcHeadFoldedSim

/-! # ArcCupFusedRewiring — the fused entries' composite partners rewire across the cup (peel campaign H, cup rung 2d-v close)

The entry-level fused rewiring: a composite boundary entry whose fresh read attaches to one
cup leg has its composite partner pinned at any entry whose fresh read attaches to the OTHER
leg.  The chain: the zone-dispatched boundary read (composite read = reindexed fresh read at
the two-zone shifted index), the fused-component bridge (opposite-leg fresh reads have
same-component sigma-images), and the composite partner pin (a censused state answers the
scan by candidate exhibition).  One theorem per leg orientation.

Together with the off-fused scan correspondence (`arcCupHeadFolded_partnerScan_offFused`)
this covers every non-leg composite entry: off both legs the partner shifts, fused across
the legs the partner rewires.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The zone-dispatched boundary read (packaged for the rewiring) -/

/-- **The composite boundary read IS the reindexed fresh read at the two-zone shifted
index** — the two zone corollaries packaged behind `freshShiftAbove`. -/
theorem arcCupHeadFolded_boundaryRead_shifted
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat)
    (windowFits : windowPosition ≤ bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (probeIndex : Nat)
    (probeInRange : probeIndex
      < bottomCount
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length) :
    natListGetAt
        (List.range bottomCount
          ++ (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires)
        probeIndex
      = arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
          [bottomCount, bottomCount + 1]) 1
        (natListGetAt
          (List.range (bottomCount + 2)
            ++ (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).openWires)
          (freshShiftAbove windowPosition 2 probeIndex)) := by
  cases Nat.lt_or_ge probeIndex windowPosition with
  | inl belowWindow =>
      rw [freshShiftAbove_ofNotLe windowPosition 2 probeIndex
        (fun windowLe => Nat.lt_irrefl windowPosition
          (Nat.lt_of_le_of_lt windowLe belowWindow))]
      exact arcCupHeadFolded_boundaryRead_belowWindow bottomCount windowPosition windowFits
        atoms probeIndex belowWindow
  | inr atWindow =>
      rw [freshShiftAbove_ofLe windowPosition 2 probeIndex atWindow]
      exact arcCupHeadFolded_boundaryRead_atOrPastWindow bottomCount windowPosition atoms
        probeIndex atWindow probeInRange

/-! ## The fused rewiring, one theorem per leg orientation -/

/-- ★ **The fused entry's composite partner rewires across the cup (left-leg exclude)**: a
composite entry whose fresh read attaches to the LEFT cup leg has its composite partner
pinned at any distinct in-range entry whose fresh read attaches to the RIGHT leg — the
boundary reads transport to sigma-images, the fused bridge connects them in the composite,
and the censused composite pins the scan. -/
theorem arcCupFusedEntry_partnerRewires_leftLeg
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat)
    (windowFits : windowPosition ≤ bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained (bottomCount + 2) atoms)
    (compositeExclude compositeTarget : Nat)
    (excludeInRange : compositeExclude
      < bottomCount
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length)
    (targetInRange : compositeTarget
      < bottomCount
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length)
    (targetNeExclude : compositeTarget ≠ compositeExclude)
    (excludeReachesLeftLeg : isSameComponent
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links windowPosition
      (natListGetAt
        (List.range (bottomCount + 2)
          ++ (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).openWires)
        (freshShiftAbove windowPosition 2 compositeExclude)) = true)
    (targetReachesRightLeg : isSameComponent
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links (windowPosition + 1)
      (natListGetAt
        (List.range (bottomCount + 2)
          ++ (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).openWires)
        (freshShiftAbove windowPosition 2 compositeTarget)) = true) :
    partnerIndexOf
      (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (List.range bottomCount
        ++ (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires)
      (bottomCount
        + (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires.length)
      compositeExclude = compositeTarget := by
  have excludeReadEq := arcCupHeadFolded_boundaryRead_shifted bottomCount windowPosition
    windowFits atoms compositeExclude excludeInRange
  have targetReadEq := arcCupHeadFolded_boundaryRead_shifted bottomCount windowPosition
    windowFits atoms compositeTarget targetInRange
  have compositeSame : isSameComponent
      (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (natListGetAt
        (List.range bottomCount
          ++ (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires)
        compositeExclude)
      (natListGetAt
        (List.range bottomCount
          ++ (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires)
        compositeTarget) = true := by
    rw [excludeReadEq, targetReadEq]
    exact arcCupHeadFolded_compositeSameComponent_ofFreshLegs bottomCount windowPosition
      windowFits atoms chained
      (natListGetAt
        (List.range (bottomCount + 2)
          ++ (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).openWires)
        (freshShiftAbove windowPosition 2 compositeExclude))
      (natListGetAt
        (List.range (bottomCount + 2)
          ++ (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).openWires)
        (freshShiftAbove windowPosition 2 compositeTarget))
      excludeReachesLeftLeg targetReachesRightLeg
  have excludeInComposite : compositeExclude
      < bottomCount
        + (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires.length := by
    rw [arcCupHeadFolded_openWiresLength bottomCount windowPosition atoms]
    exact excludeInRange
  have targetInComposite : compositeTarget
      < bottomCount
        + (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires.length := by
    rw [arcCupHeadFolded_openWiresLength bottomCount windowPosition atoms]
    exact targetInRange
  exact arcCupHeadFolded_partner_ofSameComponent bottomCount windowPosition windowFits
    atoms chained compositeExclude compositeTarget excludeInComposite targetInComposite
    targetNeExclude compositeSame

/-- ★ **The fused entry's composite partner rewires across the cup (right-leg exclude)**:
the opposite orientation — the exclude's fresh read attaches to the RIGHT cup leg, the
target's to the LEFT. -/
theorem arcCupFusedEntry_partnerRewires_rightLeg
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat)
    (windowFits : windowPosition ≤ bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained (bottomCount + 2) atoms)
    (compositeExclude compositeTarget : Nat)
    (excludeInRange : compositeExclude
      < bottomCount
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length)
    (targetInRange : compositeTarget
      < bottomCount
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length)
    (targetNeExclude : compositeTarget ≠ compositeExclude)
    (excludeReachesRightLeg : isSameComponent
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links (windowPosition + 1)
      (natListGetAt
        (List.range (bottomCount + 2)
          ++ (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).openWires)
        (freshShiftAbove windowPosition 2 compositeExclude)) = true)
    (targetReachesLeftLeg : isSameComponent
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links windowPosition
      (natListGetAt
        (List.range (bottomCount + 2)
          ++ (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).openWires)
        (freshShiftAbove windowPosition 2 compositeTarget)) = true) :
    partnerIndexOf
      (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (List.range bottomCount
        ++ (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires)
      (bottomCount
        + (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires.length)
      compositeExclude = compositeTarget := by
  have excludeReadEq := arcCupHeadFolded_boundaryRead_shifted bottomCount windowPosition
    windowFits atoms compositeExclude excludeInRange
  have targetReadEq := arcCupHeadFolded_boundaryRead_shifted bottomCount windowPosition
    windowFits atoms compositeTarget targetInRange
  have compositeSame : isSameComponent
      (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (natListGetAt
        (List.range bottomCount
          ++ (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires)
        compositeExclude)
      (natListGetAt
        (List.range bottomCount
          ++ (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires)
        compositeTarget) = true := by
    rw [excludeReadEq, targetReadEq]
    exact arcCupHeadFolded_compositeSameComponent_ofFreshLegsFlipped bottomCount
      windowPosition windowFits atoms chained
      (natListGetAt
        (List.range (bottomCount + 2)
          ++ (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).openWires)
        (freshShiftAbove windowPosition 2 compositeExclude))
      (natListGetAt
        (List.range (bottomCount + 2)
          ++ (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).openWires)
        (freshShiftAbove windowPosition 2 compositeTarget))
      excludeReachesRightLeg targetReachesLeftLeg
  have excludeInComposite : compositeExclude
      < bottomCount
        + (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires.length := by
    rw [arcCupHeadFolded_openWiresLength bottomCount windowPosition atoms]
    exact excludeInRange
  have targetInComposite : compositeTarget
      < bottomCount
        + (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires.length := by
    rw [arcCupHeadFolded_openWiresLength bottomCount windowPosition atoms]
    exact targetInRange
  exact arcCupHeadFolded_partner_ofSameComponent bottomCount windowPosition windowFits
    atoms chained compositeExclude compositeTarget excludeInComposite targetInComposite
    targetNeExclude compositeSame

/-- **Honesty marker — the entry-level fused rewiring is SHIPPED (peel campaign H, cup rung
2d-v close).**  The zone-dispatched cup boundary read
(`arcCupHeadFolded_boundaryRead_shifted`) and both leg orientations of the fused rewiring
(`arcCupFusedEntry_partnerRewires_leftLeg` / `_rightLeg`): a composite entry fused to one
cup leg has its composite partner pinned at any opposite-leg entry.  What this marker does
NOT claim: producing the opposite-leg witness from the fresh run's own partner scan (the
leg-attachment facts), the whole-diagram assembly over all entries, and the
cup-cancellation endgame.  `= true`. -/
def fxMode_hasArcCupFusedRewiring : Bool := true

end FX1Poly.Polygraph
