import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcEventCountTransport
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupBoundaryReads
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcPartitionCommute
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFreshShift

/-! # ArcCupInternalCounts — the composite internal-count lists through the cup transport

The internal cup/cap count LIST transports at the cup head (peel campaign H, cup rung 6).
Unlike the cap side — where count values are boundary-invariant and the composite list is
the fresh list with the consumed strand's pair spliced in — the cup head MERGES the two
fresh leg strands into one composite strand, so the composite entry at every port is the
leg-JOINED fresh census at the shifted boundary read, plus the head's own cup event
whenever the port's strand touches the window legs.  The whole per-index content is
packaged into `arcCupCountTransport` (mirroring `arcCupPartnerTransport` on the diagram
leg), and each list correspondence is a pointwise map congruence: below-window ports read
the fresh boundary at the same index, at-or-past ports read two indices higher, and both
zones close by the shipped per-strand event-count transports.

Notably the count lists correspond UNCONDITIONALLY over the chained fragment — no
legs-separate hypothesis appears, so these legs already cover the cup-cancel world.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private plumbing -/

/-- A zero-valued indicator adds nothing, whichever way it tests. -/
private theorem addIndicatorZero (base : Nat) (indicator : Bool) :
    base + (if indicator then 0 else 0) = base := by
  cases indicator with
  | true => rfl
  | false => rfl

/-! ## The per-index count transport -/

/-- **The cup-head count transport**: the composite run's internal event count at a
composite boundary port, expressed fresh-side — the leg-joined fresh census at the shifted
boundary read, plus the head's own contribution whenever the port's strand reaches the
window legs.  Instantiated with `headContribution := 1` for cup events (the head IS a cup)
and `headContribution := 0` for cap events (the head adds no cap anywhere). -/
def arcCupCountTransport (freshLinks : List (Nat × Nat))
    (freshBoundary eventNodes : List Nat)
    (windowPosition headContribution compositeIndex : Nat) : Nat :=
  countEventsInRoot (unionFindJoin freshLinks windowPosition (windowPosition + 1))
    (unionFindRootOf (unionFindJoin freshLinks windowPosition (windowPosition + 1))
      (natListGetAt freshBoundary (freshShiftAbove windowPosition 2 compositeIndex)))
    eventNodes
  + (if isSameComponent (unionFindJoin freshLinks windowPosition (windowPosition + 1))
        windowPosition
        (natListGetAt freshBoundary (freshShiftAbove windowPosition 2 compositeIndex))
      then headContribution else 0)

/-! ## The assembled internal-count list correspondences -/

/-- ★ **The composite internal CUP-count list is the transported fresh census**: at every
composite port the count equals the leg-joined fresh cup count at the shifted boundary
read plus one exactly when the port's strand reaches the window legs — the head's own cup
event rides the merged strand.  No legs-separate hypothesis: the correspondence covers the
cup-cancel world. -/
theorem arcCupHeadFolded_internalCupCountsCorr
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat) (windowFits : windowPosition ≤ bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained (bottomCount + 2) atoms) :
    (List.range
        (bottomCount
          + (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires.length)).map
      (internalEventCountAt
        (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (List.range bottomCount
          ++ (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires)
        (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).cupEventNodes)
      = (List.range
          (bottomCount
            + (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).openWires.length)).map
          (arcCupCountTransport
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).links
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
                atoms).openWires)
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).cupEventNodes
            windowPosition 1) := by
  have rangeEq : List.range
      (bottomCount
        + (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires.length)
    = List.range
        (bottomCount
          + (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).openWires.length) := by
    rw [arcCupHeadFolded_openWiresLength bottomCount windowPosition atoms]
  rw [rangeEq]
  exact listMapCongr
    (internalEventCountAt
      (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (List.range bottomCount
        ++ (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires)
      (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).cupEventNodes)
    (arcCupCountTransport
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links
      (List.range (bottomCount + 2)
        ++ (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires)
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).cupEventNodes
      windowPosition 1)
    (List.range
      (bottomCount
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length))
    (fun candidate candidateMem => by
      have candidateLt : candidate
          < bottomCount
            + (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).openWires.length :=
        mem_range_imp_lt candidateMem
      show countEventsInRoot
          (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).links
          (unionFindRootOf
            (processArcSpine
              (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).links
            (natListGetAt
              (List.range bottomCount
                ++ (processArcSpine
                  (stepCupArc
                    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                    windowPosition) atoms).openWires)
              candidate))
          (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).cupEventNodes
        = countEventsInRoot
            (unionFindJoin
              (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
                atoms).links
              windowPosition (windowPosition + 1))
            (unionFindRootOf
              (unionFindJoin
                (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] [])
                  atoms).links
                windowPosition (windowPosition + 1))
              (natListGetAt
                (List.range (bottomCount + 2)
                  ++ (processArcSpine
                    (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                      [] [])
                    atoms).openWires)
                (freshShiftAbove windowPosition 2 candidate)))
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).cupEventNodes
          + (if isSameComponent
              (unionFindJoin
                (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] [])
                  atoms).links
                windowPosition (windowPosition + 1))
              windowPosition
              (natListGetAt
                (List.range (bottomCount + 2)
                  ++ (processArcSpine
                    (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                      [] [])
                    atoms).openWires)
                (freshShiftAbove windowPosition 2 candidate))
            then 1 else 0)
      cases Nat.lt_or_ge candidate windowPosition with
      | inl candidateBelow =>
          have shiftFixed : freshShiftAbove windowPosition 2 candidate = candidate :=
            freshShiftAbove_ofNotLe windowPosition 2 candidate
              (fun windowLe =>
                Nat.lt_irrefl windowPosition (Nat.lt_of_le_of_lt windowLe candidateBelow))
          have boundaryRead := arcCupHeadFolded_boundaryRead_belowWindow bottomCount
            windowPosition windowFits atoms candidate candidateBelow
          rw [shiftFixed, boundaryRead]
          exact arcCupHeadFolded_cupEventCountAtImage bottomCount windowPosition
            windowFits atoms chained
            (natListGetAt
              (List.range (bottomCount + 2)
                ++ (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] [])
                  atoms).openWires)
              candidate)
      | inr atWindow =>
          have shiftPast : freshShiftAbove windowPosition 2 candidate = candidate + 2 :=
            freshShiftAbove_ofLe windowPosition 2 candidate atWindow
          have boundaryRead := arcCupHeadFolded_boundaryRead_atOrPastWindow bottomCount
            windowPosition atoms candidate atWindow candidateLt
          rw [shiftPast, boundaryRead]
          exact arcCupHeadFolded_cupEventCountAtImage bottomCount windowPosition
            windowFits atoms chained
            (natListGetAt
              (List.range (bottomCount + 2)
                ++ (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] [])
                  atoms).openWires)
              (candidate + 2)))

/-- ★ **The composite internal CAP-count list is the transported fresh census, with no
head contribution**: the cup head adds no cap event anywhere, so every composite port
reads exactly the leg-joined fresh cap count at the shifted boundary read.  Stated through
the same transport (at `headContribution := 0`) so the assembled capstone consumes one
uniform shape. -/
theorem arcCupHeadFolded_internalCapCountsCorr
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat) (windowFits : windowPosition ≤ bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained (bottomCount + 2) atoms) :
    (List.range
        (bottomCount
          + (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires.length)).map
      (internalEventCountAt
        (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (List.range bottomCount
          ++ (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires)
        (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).capEventNodes)
      = (List.range
          (bottomCount
            + (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).openWires.length)).map
          (arcCupCountTransport
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).links
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
                atoms).openWires)
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).capEventNodes
            windowPosition 0) := by
  have rangeEq : List.range
      (bottomCount
        + (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires.length)
    = List.range
        (bottomCount
          + (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).openWires.length) := by
    rw [arcCupHeadFolded_openWiresLength bottomCount windowPosition atoms]
  rw [rangeEq]
  exact listMapCongr
    (internalEventCountAt
      (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (List.range bottomCount
        ++ (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires)
      (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).capEventNodes)
    (arcCupCountTransport
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links
      (List.range (bottomCount + 2)
        ++ (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires)
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).capEventNodes
      windowPosition 0)
    (List.range
      (bottomCount
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length))
    (fun candidate candidateMem => by
      have candidateLt : candidate
          < bottomCount
            + (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).openWires.length :=
        mem_range_imp_lt candidateMem
      show countEventsInRoot
          (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).links
          (unionFindRootOf
            (processArcSpine
              (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).links
            (natListGetAt
              (List.range bottomCount
                ++ (processArcSpine
                  (stepCupArc
                    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                    windowPosition) atoms).openWires)
              candidate))
          (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).capEventNodes
        = countEventsInRoot
            (unionFindJoin
              (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
                atoms).links
              windowPosition (windowPosition + 1))
            (unionFindRootOf
              (unionFindJoin
                (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] [])
                  atoms).links
                windowPosition (windowPosition + 1))
              (natListGetAt
                (List.range (bottomCount + 2)
                  ++ (processArcSpine
                    (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                      [] [])
                    atoms).openWires)
                (freshShiftAbove windowPosition 2 candidate)))
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).capEventNodes
          + (if isSameComponent
              (unionFindJoin
                (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] [])
                  atoms).links
                windowPosition (windowPosition + 1))
              windowPosition
              (natListGetAt
                (List.range (bottomCount + 2)
                  ++ (processArcSpine
                    (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                      [] [])
                    atoms).openWires)
                (freshShiftAbove windowPosition 2 candidate))
            then 0 else 0)
      cases Nat.lt_or_ge candidate windowPosition with
      | inl candidateBelow =>
          have shiftFixed : freshShiftAbove windowPosition 2 candidate = candidate :=
            freshShiftAbove_ofNotLe windowPosition 2 candidate
              (fun windowLe =>
                Nat.lt_irrefl windowPosition (Nat.lt_of_le_of_lt windowLe candidateBelow))
          have boundaryRead := arcCupHeadFolded_boundaryRead_belowWindow bottomCount
            windowPosition windowFits atoms candidate candidateBelow
          rw [shiftFixed, boundaryRead, addIndicatorZero]
          exact arcCupHeadFolded_capEventCountAtImage bottomCount windowPosition
            windowFits atoms chained
            (natListGetAt
              (List.range (bottomCount + 2)
                ++ (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] [])
                  atoms).openWires)
              candidate)
      | inr atWindow =>
          have shiftPast : freshShiftAbove windowPosition 2 candidate = candidate + 2 :=
            freshShiftAbove_ofLe windowPosition 2 candidate atWindow
          have boundaryRead := arcCupHeadFolded_boundaryRead_atOrPastWindow bottomCount
            windowPosition atoms candidate atWindow candidateLt
          rw [shiftPast, boundaryRead, addIndicatorZero]
          exact arcCupHeadFolded_capEventCountAtImage bottomCount windowPosition
            windowFits atoms chained
            (natListGetAt
              (List.range (bottomCount + 2)
                ++ (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] [])
                  atoms).openWires)
              (candidate + 2)))

/-! ## Honesty marker -/

/-- **Honesty marker — the composite internal-count lists through the cup transport (peel
campaign H, cup rung 6).**  `arcCupHeadFolded_internalCupCountsCorr` /
`arcCupHeadFolded_internalCapCountsCorr`: at the cup-head folded end state the whole
per-port internal cup-count list equals the fresh census transported through
`arcCupCountTransport` at head contribution 1 (the leg-joined fresh cup count at the
shifted boundary read, plus the head's own cup event on the merged window strand), and the
cap-count list equals the same transport at head contribution 0.  Both hold with NO
legs-separate hypothesis — the count legs already cover the cup-cancel world.  What this
marker does NOT claim: the assembled cup `FullArcStructure` equality (diagram + totals +
these lists packaged — the next rung), the legs-connected partner dispatch, or the
head-location driver.  `= true`. -/
def fxMode_hasArcCupInternalCounts : Bool := true

end FX1Poly.Polygraph
