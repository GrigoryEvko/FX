import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapScanTestCorr
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapWindowScanFailure
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingRangeInterleave

/-! # ArcCapScanAssembly — the assembled cap-head partner-scan correspondence

The cap-head partner-scan correspondence, assembled (peel campaign H, rung E-3, part 4).
The four E-3 pieces chain into one equation: the composite extract's partner scan at a
shift-image exclude returns the shift-image of the fresh extract's partner scan.

  * the composite candidate range interleaves the window pair between the below-window
    candidates and the shifted tail images (`rangeInterleaveAtWindow`, after massaging the
    total port count through `arcCapHeadFolded_totalPorts`);
  * the window pair fails every folded scan test, so the middle segment drops out
    (`findPartnerScan_dropMiddle_ofAllFail` fed `arcCapHeadFolded_windowPairScanTestsFail`);
  * the remaining candidates are exactly the two-zone shift's image of the fresh range
    (`rangeShiftImageAtWindow`, backwards);
  * first hits correspond pointwise through the shift (`findPartnerScan_mapCongr` fed
    `arcCapHeadFolded_scanTestCorr`).

The scan equation's left side is definitionally `partnerIndexOf` at the composite folded
state, so the partner-map leg of the extract correspondence consumes this directly.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The zone-dispatched boundary read (packaged for the assembly) -/

/-- **The composite boundary read at a shift-image index IS the reindexed fresh read** —
the two zone corollaries packaged behind the two-zone index shift. -/
theorem arcCapHeadFolded_boundaryRead_shifted
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (probeIndex : Nat)
    (probeInRange : probeIndex
      < tailBoundary
        + (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          atoms).openWires.length) :
    natListGetAt
        (List.range bottomCount
          ++ (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires)
        (freshShiftAbove windowPosition 2 probeIndex)
      = arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
        (natListGetAt
          (List.range tailBoundary
            ++ (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              atoms).openWires)
          probeIndex) := by
  cases Nat.lt_or_ge probeIndex windowPosition with
  | inl belowWindow =>
      rw [freshShiftAbove_ofNotLe windowPosition 2 probeIndex
        (fun windowLe => Nat.lt_irrefl windowPosition
          (Nat.lt_of_le_of_lt windowLe belowWindow))]
      exact arcCapHeadFolded_boundaryRead_belowWindow bottomCount windowPosition
        tailBoundary windowFits tailBoundaryFits atoms probeIndex belowWindow
  | inr atWindow =>
      rw [freshShiftAbove_ofLe windowPosition 2 probeIndex atWindow]
      exact arcCapHeadFolded_boundaryRead_atOrPastWindow bottomCount windowPosition
        tailBoundary windowFits tailBoundaryFits atoms probeIndex atWindow probeInRange

/-! ## The assembled partner-scan correspondence -/

/-- ★ **The composite partner scan at a shift-image exclude returns the shift-image of the
fresh partner scan** — interleave, drop the failing window pair, recognize the shift image,
and correspond pointwise.  The left side is definitionally `partnerIndexOf` at the
composite folded state. -/
theorem arcCapHeadFolded_partnerScanCorr
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained tailBoundary atoms)
    (freshExclude : Nat)
    (excludeInRange : freshExclude
      < tailBoundary
        + (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          atoms).openWires.length) :
    findPartnerScan
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (List.range bottomCount
          ++ (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires)
        (unionFindRootOf
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).links
          (natListGetAt
            (List.range bottomCount
              ++ (processArcSpine
                (stepCapArc
                  (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                  windowPosition) atoms).openWires)
            (freshShiftAbove windowPosition 2 freshExclude)))
        (freshShiftAbove windowPosition 2 freshExclude)
        (List.range
          (bottomCount
            + (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).openWires.length))
      = freshShiftAbove windowPosition 2
        (findPartnerScan
          (processArcSpine
            (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
            atoms).links
          (List.range tailBoundary
            ++ (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              atoms).openWires)
          (unionFindRootOf
            (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              atoms).links
            (natListGetAt
              (List.range tailBoundary
                ++ (processArcSpine
                  (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                  atoms).openWires)
              freshExclude))
          freshExclude
          (List.range
            (tailBoundary
              + (processArcSpine
                (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                atoms).openWires.length))) := by
  have readExclude := arcCapHeadFolded_boundaryRead_shifted bottomCount windowPosition
    tailBoundary windowFits tailBoundaryFits atoms freshExclude excludeInRange
  have windowLeTailPlusTwo : windowPosition + 2 ≤ tailBoundary + 2 := by
    rw [tailBoundaryFits]
    exact windowFits
  have windowLeTotal : windowPosition
      ≤ tailBoundary
        + (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          atoms).openWires.length :=
    Nat.le_trans
      (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ windowLeTailPlusTwo))
      (Nat.le_add_right tailBoundary
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          atoms).openWires.length)
  obtain ⟨tailCount, tailSpec⟩ := Nat.le.dest windowLeTotal
  have compositeCandidatesEq : List.range
      (bottomCount
        + (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires.length)
    = List.range ((windowPosition + 2) + tailCount) :=
    congrArg List.range
      ((arcCapHeadFolded_totalPorts bottomCount windowPosition tailBoundary windowFits
        tailBoundaryFits atoms).trans
        ((congrArg (fun totalPorts => totalPorts + 2) tailSpec.symm).trans
          (Nat.add_right_comm windowPosition tailCount 2)))
  have freshCandidatesEq : List.range (windowPosition + tailCount)
      = List.range
        (tailBoundary
          + (processArcSpine
            (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
            atoms).openWires.length) :=
    congrArg List.range tailSpec
  have pairFails := arcCapHeadFolded_windowPairScanTestsFail bottomCount windowPosition
    tailBoundary windowFits tailBoundaryFits atoms chained
    (processArcSpine
      (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        windowPosition) atoms).openWires
    (freshShiftAbove windowPosition 2 freshExclude)
    (natListGetAt
      (List.range tailBoundary
        ++ (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          atoms).openWires)
      freshExclude)
  rw [← readExclude] at pairFails
  rw [compositeCandidatesEq, rangeInterleaveAtWindow windowPosition tailCount,
    findPartnerScan_dropMiddle_ofAllFail
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (List.range bottomCount
        ++ (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires)
      (unionFindRootOf
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (natListGetAt
          (List.range bottomCount
            ++ (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).openWires)
          (freshShiftAbove windowPosition 2 freshExclude)))
      (freshShiftAbove windowPosition 2 freshExclude)
      (List.range windowPosition) [windowPosition, windowPosition + 1]
      ((List.range tailCount).map (fun offset => (windowPosition + 2) + offset))
      pairFails,
    ← rangeShiftImageAtWindow (freshShiftAbove windowPosition 2) windowPosition tailCount
      (fun index indexBelow => freshShiftAbove_ofNotLe windowPosition 2 index
        (fun windowLe => Nat.lt_irrefl windowPosition
          (Nat.lt_of_le_of_lt windowLe indexBelow)))
      (fun index indexAtLeast => freshShiftAbove_ofLe windowPosition 2 index indexAtLeast),
    freshCandidatesEq]
  exact findPartnerScan_mapCongr
    (processArcSpine
      (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        windowPosition) atoms).links
    (processArcSpine
      (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] []) atoms).links
    (List.range bottomCount
      ++ (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).openWires)
    (List.range tailBoundary
      ++ (processArcSpine
        (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
        atoms).openWires)
    (unionFindRootOf
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (natListGetAt
        (List.range bottomCount
          ++ (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires)
        (freshShiftAbove windowPosition 2 freshExclude)))
    (unionFindRootOf
      (processArcSpine
        (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] []) atoms).links
      (natListGetAt
        (List.range tailBoundary
          ++ (processArcSpine
            (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
            atoms).openWires)
        freshExclude))
    freshExclude (freshShiftAbove windowPosition 2)
    (List.range
      (tailBoundary
        + (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          atoms).openWires.length))
    (arcCapHeadFolded_scanTestCorr bottomCount windowPosition tailBoundary windowFits
      tailBoundaryFits atoms chained freshExclude excludeInRange)

/-! ## Honesty marker -/

/-- **Honesty marker — the assembled cap-head partner-scan correspondence (peel campaign
H, rung E-3, part 4).**  The zone-dispatched shifted boundary read, and the full scan
assembly: composite scan over the whole candidate range at a shift-image exclude = the
shift-image of the fresh scan (interleave, failing window pair dropped, shift image
recognized, pointwise map congruence).  What this marker does NOT claim: the
`partnerIndexOf`/`extractDiagram` packaging (the window pair partnering EACH OTHER in the
composite extract, the mapped partner-list equality, and the `DiagramType` equality), the
cup-head diagram leg, and the head-cancellation assembly.  `= true`. -/
def fxMode_hasArcCapScanAssembly : Bool := true

end FX1Poly.Polygraph
