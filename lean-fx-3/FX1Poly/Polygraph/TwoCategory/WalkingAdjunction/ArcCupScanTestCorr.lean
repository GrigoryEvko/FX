import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupBoundaryReads
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcHeadFoldedCorr
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingComponentAlgebra
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcPartitionCommute

/-! # ArcCupScanTestCorr — the per-candidate scan-test correspondence at the cup head

The cup-head partner-scan correspondence (peel campaign H, cup rung 2a).  The roles flip
relative to the cap: the index shift runs COMPOSITE index -> FRESH index (the fresh side
has the two extra leg ports), and the correspondence target is the fresh links with the
legs ARTIFICIALLY JOINED (`unionFindJoin freshLinks windowPosition (windowPosition + 1)`)
— the peeled cup's fusion, which the shipped folded component correspondence carries.  For
every composite candidate index, the joined-fresh scan test at the two-zone shifted index
equals the composite scan test at the original index:

  * the exclude bang-inequality corresponds because the two-zone index shift is injective;
  * the boundary reads correspond through the head reindexing `sigma` (the cup rung 1 zone
    reads at the folded states);
  * the component-root comparison corresponds through the folded cup correspondence — the
    composite components at `sigma`-images ARE the joined-fresh components.

This is exactly the pointwise hypothesis `findPartnerScan_mapCongr` consumes, with the
JOINED-fresh world in the shifted slot and the composite world in the plain slot.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The folded component correspondence in pointwise shape -/

/-- **Folded composite components at `sigma`-images are folded JOINED-fresh components**:
the shipped cup-head folded correspondence, applied pointwise.  Unlike the cap (degenerate
`(0, 0)` seed-join, collapsed), the cup's join is REAL — the peeled cup fuses the two leg
strands, so the fresh side carries `unionFindJoin` at the window legs. -/
theorem arcCupHeadFolded_componentCorr
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat)
    (windowFits : windowPosition ≤ bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained (bottomCount + 2) atoms)
    (probeLeft probeRight : Nat) :
    isSameComponent
        (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
          [bottomCount, bottomCount + 1]) 1 probeLeft)
        (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
          [bottomCount, bottomCount + 1]) 1 probeRight)
      = isSameComponent
          (unionFindJoin
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).links
            windowPosition (windowPosition + 1))
          probeLeft probeRight :=
  arcComponentShiftCorr_cupHeadFolded bottomCount windowPosition windowFits atoms chained
    probeLeft probeRight

/-! ## The two-zone index shift is beq-injective (per-file copy, codebase pattern) -/

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

/-- ★ **The joined-fresh scan test at a shift-image candidate IS the composite scan
test** — stated in exactly the pointwise-hypothesis shape `findPartnerScan_mapCongr`
consumes, with the JOINED-fresh world in the shifted slot and the cup composite in the
plain slot: the exclude bang-inequality corresponds by shift injectivity, the boundary
reads correspond through the head reindexing, and the root comparison corresponds through
the folded cup component correspondence (the peeled cup's leg fusion carried as the
`unionFindJoin` on the fresh side). -/
theorem arcCupHeadFolded_scanTestCorr
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat)
    (windowFits : windowPosition ≤ bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained (bottomCount + 2) atoms)
    (compositeExclude : Nat)
    (excludeInRange : compositeExclude
      < bottomCount
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length) :
    ∀ candidate, candidate ∈ List.range
      (bottomCount
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length) →
    (freshShiftAbove windowPosition 2 candidate
          != freshShiftAbove windowPosition 2 compositeExclude
        && unionFindRootOf
            (unionFindJoin
              (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).links
              windowPosition (windowPosition + 1))
            (natListGetAt
              (List.range (bottomCount + 2)
                ++ (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] []) atoms).openWires)
              (freshShiftAbove windowPosition 2 candidate))
          == unionFindRootOf
              (unionFindJoin
                (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] []) atoms).links
                windowPosition (windowPosition + 1))
              (natListGetAt
                (List.range (bottomCount + 2)
                  ++ (processArcSpine
                    (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2)
                      0 [] []) atoms).openWires)
                (freshShiftAbove windowPosition 2 compositeExclude)))
      = (candidate != compositeExclude
          && unionFindRootOf
              (processArcSpine
                (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0
                  [] []) windowPosition) atoms).links
              (natListGetAt
                (List.range bottomCount
                  ++ (processArcSpine
                    (stepCupArc
                      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                      windowPosition) atoms).openWires)
                candidate)
            == unionFindRootOf
                (processArcSpine
                  (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0
                    [] []) windowPosition) atoms).links
                (natListGetAt
                  (List.range bottomCount
                    ++ (processArcSpine
                      (stepCupArc
                        (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                        windowPosition) atoms).openWires)
                  compositeExclude)) := by
  intro candidate candidateMem
  have candidateInRange := mem_range_imp_lt candidateMem
  have readAtProbe : ∀ probeIndex : Nat,
      probeIndex
        < bottomCount
          + (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).openWires.length →
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
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires)
            (freshShiftAbove windowPosition 2 probeIndex)) := by
    intro probeIndex probeInRange
    cases Nat.lt_or_ge probeIndex windowPosition with
    | inl belowWindow =>
        rw [freshShiftAbove_ofNotLe windowPosition 2 probeIndex
          (fun windowLe => Nat.lt_irrefl windowPosition
            (Nat.lt_of_le_of_lt windowLe belowWindow))]
        exact arcCupHeadFolded_boundaryRead_belowWindow bottomCount windowPosition
          windowFits atoms probeIndex belowWindow
    | inr atWindow =>
        rw [freshShiftAbove_ofLe windowPosition 2 probeIndex atWindow]
        exact arcCupHeadFolded_boundaryRead_atOrPastWindow bottomCount windowPosition
          atoms probeIndex atWindow probeInRange
  have readCandidate := readAtProbe candidate candidateInRange
  have readExclude := readAtProbe compositeExclude excludeInRange
  have componentBeq : (unionFindRootOf
      (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1
        (natListGetAt
          (List.range (bottomCount + 2)
            ++ (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                [] []) atoms).openWires)
          (freshShiftAbove windowPosition 2 candidate)))
        == unionFindRootOf
            (processArcSpine
              (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).links
            (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
              [bottomCount, bottomCount + 1]) 1
              (natListGetAt
                (List.range (bottomCount + 2)
                  ++ (processArcSpine
                    (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2)
                      0 [] []) atoms).openWires)
                (freshShiftAbove windowPosition 2 compositeExclude))))
      = (unionFindRootOf
          (unionFindJoin
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                [] []) atoms).links
            windowPosition (windowPosition + 1))
          (natListGetAt
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires)
            (freshShiftAbove windowPosition 2 candidate))
          == unionFindRootOf
              (unionFindJoin
                (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] []) atoms).links
                windowPosition (windowPosition + 1))
              (natListGetAt
                (List.range (bottomCount + 2)
                  ++ (processArcSpine
                    (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2)
                      0 [] []) atoms).openWires)
                (freshShiftAbove windowPosition 2 compositeExclude))) :=
    arcCupHeadFolded_componentCorr bottomCount windowPosition windowFits atoms chained
      (natListGetAt
        (List.range (bottomCount + 2)
          ++ (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).openWires)
        (freshShiftAbove windowPosition 2 candidate))
      (natListGetAt
        (List.range (bottomCount + 2)
          ++ (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).openWires)
        (freshShiftAbove windowPosition 2 compositeExclude))
  rw [windowIndexShift_bneCorr windowPosition candidate compositeExclude, readCandidate,
    readExclude, componentBeq]

/-! ## Honesty marker -/

/-- **Honesty marker — the per-candidate scan-test correspondence at the cup head (peel
campaign H, cup rung 2a).**  `arcCupHeadFolded_componentCorr`: composite components at
`sigma`-images are the JOINED-fresh components (the peeled cup's leg fusion as
`unionFindJoin` at the window legs — a REAL join, unlike the cap's collapsed degenerate
one).  `arcCupHeadFolded_scanTestCorr`: the whole exclude-and-root test corresponds
per-candidate, in exactly `findPartnerScan_mapCongr`'s pointwise shape with the
joined-fresh world in the shifted slot.  What this marker does NOT claim: the assembled
scan equality over the full candidate range (the shift-image of the composite range is the
fresh range MINUS the two window legs — the punctured-scan analysis is the next rung), the
relation between the JOINED-fresh partner scan and the PLAIN fresh partner list (the leg
rewiring), and the assembled cup diagram/partner leg.  `= true`. -/
def fxMode_hasArcCupScanTestCorr : Bool := true

end FX1Poly.Polygraph
