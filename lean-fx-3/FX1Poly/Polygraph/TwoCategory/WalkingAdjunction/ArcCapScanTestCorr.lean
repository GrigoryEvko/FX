import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapBoundaryReads
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcHeadFoldedCorr
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingComponentAlgebra
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcPartitionCommute

/-! # ArcCapScanTestCorr — the per-candidate scan-test correspondence at the cap head

The cap-head partner-scan correspondence (peel campaign H, rung E-3, part 3b).  For every
fresh candidate index, the composite scan's whole exclude-and-root test at the two-zone
shifted index equals the fresh scan's test at the original index:

  * the exclude bang-inequality corresponds because the two-zone index shift is injective
    (identity below the window, `+ 2` at or past it — the zones cannot collide);
  * the boundary reads correspond through the head reindexing `σ` (the E-3 zone reads at
    the folded states);
  * the component-root comparison corresponds because the folded composite components at
    `σ`-images ARE the folded fresh components — the head-cancellation component
    correspondence, with its degenerate `(0, 0)` seed-join collapsed by the union's
    built-in no-op test.

This is exactly the pointwise hypothesis `findPartnerScan_mapCongr` consumes, so the
composite scan over the shift-image candidates returns the shifted fresh partner.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The collapsed component correspondence at the folded end states -/

/-- **Folded composite components at `σ`-images are folded fresh components**: the
head-cancellation component correspondence with the degenerate `(0, 0)` seed-join
collapsed (joining a node to itself is a no-op). -/
theorem arcCapHeadFolded_componentCorr
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained tailBoundary atoms)
    (probeLeft probeRight : Nat) :
    isSameComponent
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
          probeLeft)
        (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
          probeRight)
      = isSameComponent
          (processArcSpine
            (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
            atoms).links
          probeLeft probeRight := by
  have degenerateJoinCollapses : unionFindJoin
      (processArcSpine
        (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] []) atoms).links
      0 0
    = (processArcSpine
        (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] []) atoms).links :=
    unionFindJoin_ofSameComponent
      (processArcSpine
        (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] []) atoms).links
      0 0 (decide_eq_true rfl)
  have rawCorr := arcComponentShiftCorr_capHeadFolded bottomCount windowPosition
    tailBoundary windowFits tailBoundaryFits atoms chained probeLeft probeRight
  rw [degenerateJoinCollapses] at rawCorr
  exact rawCorr

/-! ## The two-zone index shift is beq-injective -/

/-- The two-zone index shift never collides across zones: below-window indices stay below
the window while shifted indices land at or past `windowPosition + 2`. -/
private theorem windowIndexShift_beqCorr (windowPosition firstIndex secondIndex : Nat) :
    (freshShiftAbove windowPosition 2 firstIndex
        == freshShiftAbove windowPosition 2 secondIndex)
      = (firstIndex == secondIndex) := by
  cases Nat.lt_or_ge firstIndex windowPosition with
  | inl firstBelow =>
      cases Nat.lt_or_ge secondIndex windowPosition with
      | inl secondBelow =>
          rw [freshShiftAbove_ofNotLe windowPosition 2 firstIndex
              (fun windowLe => Nat.lt_irrefl windowPosition
                (Nat.lt_of_le_of_lt windowLe firstBelow)),
            freshShiftAbove_ofNotLe windowPosition 2 secondIndex
              (fun windowLe => Nat.lt_irrefl windowPosition
                (Nat.lt_of_le_of_lt windowLe secondBelow))]
      | inr secondAtWindow =>
          rw [freshShiftAbove_ofNotLe windowPosition 2 firstIndex
              (fun windowLe => Nat.lt_irrefl windowPosition
                (Nat.lt_of_le_of_lt windowLe firstBelow)),
            freshShiftAbove_ofLe windowPosition 2 secondIndex secondAtWindow]
          have firstLtSecond : firstIndex < secondIndex :=
            Nat.lt_of_lt_of_le firstBelow secondAtWindow
          have leftFalse : (firstIndex == secondIndex + 2) = false :=
            decide_eq_false (fun hitsShifted => Nat.lt_irrefl firstIndex
              (Nat.lt_of_lt_of_le
                (Nat.lt_of_lt_of_le firstLtSecond (Nat.le_add_right secondIndex 2))
                (Nat.le_of_eq hitsShifted.symm)))
          have rightFalse : (firstIndex == secondIndex) = false :=
            decide_eq_false (fun hitsSecond => Nat.lt_irrefl firstIndex
              (Nat.lt_of_lt_of_le firstLtSecond (Nat.le_of_eq hitsSecond.symm)))
          rw [leftFalse, rightFalse]
  | inr firstAtWindow =>
      cases Nat.lt_or_ge secondIndex windowPosition with
      | inl secondBelow =>
          rw [freshShiftAbove_ofLe windowPosition 2 firstIndex firstAtWindow,
            freshShiftAbove_ofNotLe windowPosition 2 secondIndex
              (fun windowLe => Nat.lt_irrefl windowPosition
                (Nat.lt_of_le_of_lt windowLe secondBelow))]
          have secondLtFirst : secondIndex < firstIndex :=
            Nat.lt_of_lt_of_le secondBelow firstAtWindow
          have leftFalse : (firstIndex + 2 == secondIndex) = false :=
            decide_eq_false (fun shiftedHits => Nat.lt_irrefl secondIndex
              (Nat.lt_of_lt_of_le
                (Nat.lt_of_lt_of_le secondLtFirst (Nat.le_add_right firstIndex 2))
                (Nat.le_of_eq shiftedHits)))
          have rightFalse : (firstIndex == secondIndex) = false :=
            decide_eq_false (fun hitsSecond => Nat.lt_irrefl secondIndex
              (Nat.lt_of_lt_of_le secondLtFirst (Nat.le_of_eq hitsSecond)))
          rw [leftFalse, rightFalse]
      | inr secondAtWindow =>
          rw [freshShiftAbove_ofLe windowPosition 2 firstIndex firstAtWindow,
            freshShiftAbove_ofLe windowPosition 2 secondIndex secondAtWindow]
          cases baseBeq : (firstIndex == secondIndex) with
          | true =>
              have indicesEqual : firstIndex = secondIndex := of_decide_eq_true baseBeq
              rw [indicesEqual]
              exact decide_eq_true rfl
          | false =>
              have indicesDiffer : firstIndex ≠ secondIndex := of_decide_eq_false baseBeq
              exact decide_eq_false (fun shiftedEqual => indicesDiffer
                (Nat.succ.inj (Nat.succ.inj shiftedEqual)))

/-- The bang-inequality face of the two-zone shift injectivity. -/
private theorem windowIndexShift_bneCorr (windowPosition firstIndex secondIndex : Nat) :
    (freshShiftAbove windowPosition 2 firstIndex
        != freshShiftAbove windowPosition 2 secondIndex)
      = (firstIndex != secondIndex) := by
  show (!(freshShiftAbove windowPosition 2 firstIndex
      == freshShiftAbove windowPosition 2 secondIndex))
    = (!(firstIndex == secondIndex))
  rw [windowIndexShift_beqCorr windowPosition firstIndex secondIndex]

/-! ## The per-candidate scan-test correspondence -/

/-- ★ **The composite scan test at a shift-image candidate IS the fresh scan test** —
stated in exactly the pointwise-hypothesis shape `findPartnerScan_mapCongr` consumes: the
exclude bang-inequality corresponds by shift injectivity, the boundary reads correspond
through the head reindexing, and the root comparison corresponds through the folded
component correspondence. -/
theorem arcCapHeadFolded_scanTestCorr
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
    ∀ candidate, candidate ∈ List.range
      (tailBoundary
        + (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          atoms).openWires.length) →
    (freshShiftAbove windowPosition 2 candidate
          != freshShiftAbove windowPosition 2 freshExclude
        && unionFindRootOf
            (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).links
            (natListGetAt
              (List.range bottomCount
                ++ (processArcSpine
                  (stepCapArc
                    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                    windowPosition) atoms).openWires)
              (freshShiftAbove windowPosition 2 candidate))
          == unionFindRootOf
              (processArcSpine
                (stepCapArc
                  (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                  windowPosition) atoms).links
              (natListGetAt
                (List.range bottomCount
                  ++ (processArcSpine
                    (stepCapArc
                      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                      windowPosition) atoms).openWires)
                (freshShiftAbove windowPosition 2 freshExclude)))
      = (candidate != freshExclude
          && unionFindRootOf
              (processArcSpine
                (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                atoms).links
              (natListGetAt
                (List.range tailBoundary
                  ++ (processArcSpine
                    (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                    atoms).openWires)
                candidate)
            == unionFindRootOf
                (processArcSpine
                  (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                  atoms).links
                (natListGetAt
                  (List.range tailBoundary
                    ++ (processArcSpine
                      (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                      atoms).openWires)
                  freshExclude)) := by
  intro candidate candidateMem
  have candidateInRange := mem_range_imp_lt candidateMem
  have readAtProbe : ∀ probeIndex : Nat,
      probeIndex
        < tailBoundary
          + (processArcSpine
            (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
            atoms).openWires.length →
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
    intro probeIndex probeInRange
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
  have readCandidate := readAtProbe candidate candidateInRange
  have readExclude := readAtProbe freshExclude excludeInRange
  have componentBeq : (unionFindRootOf
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
        (natListGetAt
          (List.range tailBoundary
            ++ (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              atoms).openWires)
          candidate))
        == unionFindRootOf
            (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).links
            (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
              (natListGetAt
                (List.range tailBoundary
                  ++ (processArcSpine
                    (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                    atoms).openWires)
                freshExclude)))
      = (unionFindRootOf
          (processArcSpine
            (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
            atoms).links
          (natListGetAt
            (List.range tailBoundary
              ++ (processArcSpine
                (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                atoms).openWires)
            candidate)
          == unionFindRootOf
              (processArcSpine
                (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                atoms).links
              (natListGetAt
                (List.range tailBoundary
                  ++ (processArcSpine
                    (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                    atoms).openWires)
                freshExclude)) :=
    arcCapHeadFolded_componentCorr bottomCount windowPosition tailBoundary windowFits
      tailBoundaryFits atoms chained
      (natListGetAt
        (List.range tailBoundary
          ++ (processArcSpine
            (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
            atoms).openWires)
        candidate)
      (natListGetAt
        (List.range tailBoundary
          ++ (processArcSpine
            (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
            atoms).openWires)
        freshExclude)
  rw [windowIndexShift_bneCorr windowPosition candidate freshExclude, readCandidate,
    readExclude, componentBeq]

/-! ## Honesty marker -/

/-- **Honesty marker — the per-candidate scan-test correspondence at the cap head (peel
campaign H, rung E-3, part 3b).**  The folded component correspondence with its degenerate
seed-join collapsed, the two-zone index shift's beq-injectivity, and the whole
exclude-and-root test correspondence in exactly `findPartnerScan_mapCongr`'s pointwise
shape.  What this marker does NOT claim: the assembled scan equality (composite scan over
the full candidate range = shifted fresh scan — the interleave, drop-middle, shift-image,
and map-congruence steps chained), the `partnerIndexOf` correspondence, and the assembled
diagram/partner leg.  `= true`. -/
def fxMode_hasArcCapScanTestCorr : Bool := true

end FX1Poly.Polygraph
