import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupFusedTarget
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupFusedFallback
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupPuncturedScan
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusPartnerUnique

/-! # ArcCupPartnerDispatch — the composite cup partner, one equation per index

The per-index dispatch master (peel campaign H, cup rung 4 close).  On the censused
chained fragment the component tests and the fresh scan values COINCIDE: an entry's fresh
read attaches to a cup leg exactly when its fresh partner IS that leg's index (the census
pins the partner at the unique same-component boundary token).  So the whole three-way
value analysis — off-fused transparency, the closed-form rewired target, the orphaned
fallback — keys on the fresh partner values alone, and the composite partner at every
in-range index is ONE function of fresh data: `arcCupPartnerTransport`.  Fused to the left
leg (fresh partner = the left leg index): the right leg's fresh partner, downshifted, or
the index itself when the right leg is orphaned.  Mirror on the right.  Off both legs: the
downshifted fresh partner at the shifted index.

Requires the legs-separate hypothesis (the fresh legs in distinct components) — the
legs-connected world is the cup-cancellation case, analyzed separately.

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

/-! ## The transported partner value -/

/-- **The cup partner transport**: the composite partner value at a composite index, as a
function of the FRESH run's partner data alone.  Fresh partner of the shifted index equal
to a cup leg means the entry is fused there (census coincidence): the value is the
OPPOSITE leg's fresh partner downshifted, or the index itself when that leg is orphaned.
Off both legs the cup is transparent: the value is the downshifted fresh partner. -/
def arcCupPartnerTransport (freshLinks : List (Nat × Nat)) (freshBoundary : List Nat)
    (freshTotal windowPosition compositeIndex : Nat) : Nat :=
  if partnerIndexOf freshLinks freshBoundary freshTotal
      (freshShiftAbove windowPosition 2 compositeIndex) = windowPosition then
    if partnerIndexOf freshLinks freshBoundary freshTotal (windowPosition + 1)
        = windowPosition + 1 then
      compositeIndex
    else
      freshUnshiftAbove windowPosition 2
        (partnerIndexOf freshLinks freshBoundary freshTotal (windowPosition + 1))
  else if partnerIndexOf freshLinks freshBoundary freshTotal
      (freshShiftAbove windowPosition 2 compositeIndex) = windowPosition + 1 then
    if partnerIndexOf freshLinks freshBoundary freshTotal windowPosition
        = windowPosition then
      compositeIndex
    else
      freshUnshiftAbove windowPosition 2
        (partnerIndexOf freshLinks freshBoundary freshTotal windowPosition)
  else
    freshUnshiftAbove windowPosition 2
      (partnerIndexOf freshLinks freshBoundary freshTotal
        (freshShiftAbove windowPosition 2 compositeIndex))

/-! ## The dispatch master -/

/-- ★ **The composite cup partner is the transported fresh partner at every in-range
index**: with separated fresh legs, `partnerIndexOf` at the cup-head folded composite
equals `arcCupPartnerTransport` of the fresh data.  Fused branches ride the census
coincidence (fresh partner = leg index exactly when the read attaches to the leg) into the
closed-form target and the orphaned fallback; the off-fused branch rides the transparency
correspondence through the downshift round trip. -/
theorem arcCupHeadFolded_partnerDispatch
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat)
    (windowFits : windowPosition ≤ bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained (bottomCount + 2) atoms)
    (legsSeparate : isSameComponent
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links windowPosition (windowPosition + 1) = false)
    (compositeIndex : Nat)
    (indexInRange : compositeIndex
      < bottomCount
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length) :
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
      compositeIndex
      = arcCupPartnerTransport
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).links
          (List.range (bottomCount + 2)
            ++ (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).openWires)
          (bottomCount + 2
            + (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).openWires.length)
          windowPosition compositeIndex := by
  have readAtLeftLeg : natListGetAt
      (List.range (bottomCount + 2)
        ++ (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires)
      windowPosition = windowPosition :=
    natListGetAt_rangeAppend_below (bottomCount + 2)
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).openWires
      windowPosition (Nat.lt_succ_of_le (Nat.le_succ_of_le windowFits))
  have readAtRightLeg : natListGetAt
      (List.range (bottomCount + 2)
        ++ (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires)
      (windowPosition + 1) = windowPosition + 1 :=
    natListGetAt_rangeAppend_below (bottomCount + 2)
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).openWires
      (windowPosition + 1) (Nat.succ_lt_succ (Nat.lt_succ_of_le windowFits))
  have shiftInTotal := shiftIndexWithinFreshTotal windowPosition bottomCount
    (processArcSpine
      (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
      atoms).openWires.length
    compositeIndex indexInRange
  have leftLegWithinTotal : windowPosition
      < bottomCount + 2
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_succ_of_le windowFits))
      (Nat.le_add_right (bottomCount + 2)
        (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length)
  have rightLegWithinTotal : windowPosition + 1
      < bottomCount + 2
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length :=
    Nat.lt_of_lt_of_le (Nat.succ_lt_succ (Nat.lt_succ_of_le windowFits))
      (Nat.le_add_right (bottomCount + 2)
        (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length)
  have freshCensus := arcBoundaryCensus_ofChainedSpineList (bottomCount + 2) atoms chained
  show partnerIndexOf
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
      compositeIndex
    = if partnerIndexOf
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).links
          (List.range (bottomCount + 2)
            ++ (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).openWires)
          (bottomCount + 2
            + (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).openWires.length)
          (freshShiftAbove windowPosition 2 compositeIndex) = windowPosition then
        if partnerIndexOf
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).links
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires)
            (bottomCount + 2
              + (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires.length)
            (windowPosition + 1) = windowPosition + 1 then
          compositeIndex
        else
          freshUnshiftAbove windowPosition 2
            (partnerIndexOf
              (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).links
              (List.range (bottomCount + 2)
                ++ (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] []) atoms).openWires)
              (bottomCount + 2
                + (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] []) atoms).openWires.length)
              (windowPosition + 1))
      else if partnerIndexOf
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).links
          (List.range (bottomCount + 2)
            ++ (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).openWires)
          (bottomCount + 2
            + (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).openWires.length)
          (freshShiftAbove windowPosition 2 compositeIndex) = windowPosition + 1 then
        if partnerIndexOf
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).links
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires)
            (bottomCount + 2
              + (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires.length)
            windowPosition = windowPosition then
          compositeIndex
        else
          freshUnshiftAbove windowPosition 2
            (partnerIndexOf
              (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).links
              (List.range (bottomCount + 2)
                ++ (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] []) atoms).openWires)
              (bottomCount + 2
                + (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] []) atoms).openWires.length)
              windowPosition)
      else
        freshUnshiftAbove windowPosition 2
          (partnerIndexOf
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).links
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires)
            (bottomCount + 2
              + (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires.length)
            (freshShiftAbove windowPosition 2 compositeIndex))
  cases Nat.decEq
      (partnerIndexOf
        (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).links
        (List.range (bottomCount + 2)
          ++ (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).openWires)
        (bottomCount + 2
          + (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).openWires.length)
        (freshShiftAbove windowPosition 2 compositeIndex))
      windowPosition with
  | isTrue shiftPartnerEqLeft =>
      rw [if_pos shiftPartnerEqLeft]
      have foundNeExclude : partnerIndexOf
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).links
          (List.range (bottomCount + 2)
            ++ (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).openWires)
          (bottomCount + 2
            + (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).openWires.length)
          (freshShiftAbove windowPosition 2 compositeIndex)
          ≠ freshShiftAbove windowPosition 2 compositeIndex :=
        fun resultEqExclude => freshShiftAbove_neWindow windowPosition compositeIndex
          ((shiftPartnerEqLeft.symm.trans resultEqExclude).symm)
      have rootFact : unionFindRootOf
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).links
          (natListGetAt
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires)
            (partnerIndexOf
              (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).links
              (List.range (bottomCount + 2)
                ++ (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] []) atoms).openWires)
              (bottomCount + 2
                + (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] []) atoms).openWires.length)
              (freshShiftAbove windowPosition 2 compositeIndex)))
          = unionFindRootOf
              (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).links
              (natListGetAt
                (List.range (bottomCount + 2)
                  ++ (processArcSpine
                    (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                      [] []) atoms).openWires)
                (freshShiftAbove windowPosition 2 compositeIndex)) :=
        findPartnerScan_root_ofFound
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).links
          (List.range (bottomCount + 2)
            ++ (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).openWires)
          (unionFindRootOf
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).links
            (natListGetAt
              (List.range (bottomCount + 2)
                ++ (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] []) atoms).openWires)
              (freshShiftAbove windowPosition 2 compositeIndex)))
          (freshShiftAbove windowPosition 2 compositeIndex)
          (List.range
            (bottomCount + 2
              + (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires.length))
          foundNeExclude
      rw [shiftPartnerEqLeft, readAtLeftLeg] at rootFact
      have excludeReachesLeftLeg : isSameComponent
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).links windowPosition
          (natListGetAt
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires)
            (freshShiftAbove windowPosition 2 compositeIndex)) = true :=
        decide_eq_true rootFact
      cases Nat.decEq
          (partnerIndexOf
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).links
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires)
            (bottomCount + 2
              + (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires.length)
            (windowPosition + 1))
          (windowPosition + 1) with
      | isTrue rightOrphaned =>
          rw [if_pos rightOrphaned]
          exact arcCupFusedEntry_partnerFallback_leftLeg bottomCount windowPosition
            windowFits atoms chained compositeIndex indexInRange excludeReachesLeftLeg
            rightOrphaned
      | isFalse rightFound =>
          rw [if_neg rightFound]
          exact arcCupFusedEntry_partnerTarget_leftLeg bottomCount windowPosition
            windowFits atoms chained compositeIndex indexInRange excludeReachesLeftLeg
            legsSeparate rightFound
  | isFalse shiftPartnerNeLeft =>
      rw [if_neg shiftPartnerNeLeft]
      cases Nat.decEq
          (partnerIndexOf
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).links
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires)
            (bottomCount + 2
              + (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires.length)
            (freshShiftAbove windowPosition 2 compositeIndex))
          (windowPosition + 1) with
      | isTrue shiftPartnerEqRight =>
          rw [if_pos shiftPartnerEqRight]
          have foundNeExclude : partnerIndexOf
              (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).links
              (List.range (bottomCount + 2)
                ++ (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] []) atoms).openWires)
              (bottomCount + 2
                + (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] []) atoms).openWires.length)
              (freshShiftAbove windowPosition 2 compositeIndex)
              ≠ freshShiftAbove windowPosition 2 compositeIndex :=
            fun resultEqExclude => freshShiftAbove_neWindowSucc windowPosition
              compositeIndex ((shiftPartnerEqRight.symm.trans resultEqExclude).symm)
          have rootFact : unionFindRootOf
              (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).links
              (natListGetAt
                (List.range (bottomCount + 2)
                  ++ (processArcSpine
                    (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                      [] []) atoms).openWires)
                (partnerIndexOf
                  (processArcSpine
                    (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                      [] []) atoms).links
                  (List.range (bottomCount + 2)
                    ++ (processArcSpine
                      (ArcWireState.mk (List.range (bottomCount + 2)) []
                        (bottomCount + 2) 0 [] []) atoms).openWires)
                  (bottomCount + 2
                    + (processArcSpine
                      (ArcWireState.mk (List.range (bottomCount + 2)) []
                        (bottomCount + 2) 0 [] []) atoms).openWires.length)
                  (freshShiftAbove windowPosition 2 compositeIndex)))
              = unionFindRootOf
                  (processArcSpine
                    (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                      [] []) atoms).links
                  (natListGetAt
                    (List.range (bottomCount + 2)
                      ++ (processArcSpine
                        (ArcWireState.mk (List.range (bottomCount + 2)) []
                          (bottomCount + 2) 0 [] []) atoms).openWires)
                    (freshShiftAbove windowPosition 2 compositeIndex)) :=
            findPartnerScan_root_ofFound
              (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).links
              (List.range (bottomCount + 2)
                ++ (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] []) atoms).openWires)
              (unionFindRootOf
                (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] []) atoms).links
                (natListGetAt
                  (List.range (bottomCount + 2)
                    ++ (processArcSpine
                      (ArcWireState.mk (List.range (bottomCount + 2)) []
                        (bottomCount + 2) 0 [] []) atoms).openWires)
                  (freshShiftAbove windowPosition 2 compositeIndex)))
              (freshShiftAbove windowPosition 2 compositeIndex)
              (List.range
                (bottomCount + 2
                  + (processArcSpine
                    (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                      [] []) atoms).openWires.length))
              foundNeExclude
          rw [shiftPartnerEqRight, readAtRightLeg] at rootFact
          have excludeReachesRightLeg : isSameComponent
              (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).links (windowPosition + 1)
              (natListGetAt
                (List.range (bottomCount + 2)
                  ++ (processArcSpine
                    (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                      [] []) atoms).openWires)
                (freshShiftAbove windowPosition 2 compositeIndex)) = true :=
            decide_eq_true rootFact
          cases Nat.decEq
              (partnerIndexOf
                (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] []) atoms).links
                (List.range (bottomCount + 2)
                  ++ (processArcSpine
                    (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                      [] []) atoms).openWires)
                (bottomCount + 2
                  + (processArcSpine
                    (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                      [] []) atoms).openWires.length)
                windowPosition)
              windowPosition with
          | isTrue leftOrphaned =>
              rw [if_pos leftOrphaned]
              exact arcCupFusedEntry_partnerFallback_rightLeg bottomCount windowPosition
                windowFits atoms chained compositeIndex indexInRange
                excludeReachesRightLeg leftOrphaned
          | isFalse leftFound =>
              rw [if_neg leftFound]
              exact arcCupFusedEntry_partnerTarget_rightLeg bottomCount windowPosition
                windowFits atoms chained compositeIndex indexInRange
                excludeReachesRightLeg legsSeparate leftFound
      | isFalse shiftPartnerNeRight =>
          rw [if_neg shiftPartnerNeRight]
          have offLeft : isSameComponent
              (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).links windowPosition
              (natListGetAt
                (List.range (bottomCount + 2)
                  ++ (processArcSpine
                    (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                      [] []) atoms).openWires)
                (freshShiftAbove windowPosition 2 compositeIndex)) = false := by
            cases legLeftTest : isSameComponent
                (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] []) atoms).links windowPosition
                (natListGetAt
                  (List.range (bottomCount + 2)
                    ++ (processArcSpine
                      (ArcWireState.mk (List.range (bottomCount + 2)) []
                        (bottomCount + 2) 0 [] []) atoms).openWires)
                  (freshShiftAbove windowPosition 2 compositeIndex)) with
            | false => rfl
            | true =>
                have sameReads : isSameComponent
                    (processArcSpine
                      (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2)
                        0 [] []) atoms).links
                    (natListGetAt
                      (List.range (bottomCount + 2)
                        ++ (processArcSpine
                          (ArcWireState.mk (List.range (bottomCount + 2)) []
                            (bottomCount + 2) 0 [] []) atoms).openWires)
                      (freshShiftAbove windowPosition 2 compositeIndex))
                    (natListGetAt
                      (List.range (bottomCount + 2)
                        ++ (processArcSpine
                          (ArcWireState.mk (List.range (bottomCount + 2)) []
                            (bottomCount + 2) 0 [] []) atoms).openWires)
                      windowPosition) = true := by
                  rw [readAtLeftLeg]
                  exact (isSameComponent_symm
                    (processArcSpine
                      (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2)
                        0 [] []) atoms).links
                    (natListGetAt
                      (List.range (bottomCount + 2)
                        ++ (processArcSpine
                          (ArcWireState.mk (List.range (bottomCount + 2)) []
                            (bottomCount + 2) 0 [] []) atoms).openWires)
                      (freshShiftAbove windowPosition 2 compositeIndex))
                    windowPosition).trans legLeftTest
                exact False.elim (shiftPartnerNeLeft
                  (partnerIndexOf_uniqueSameComponent (bottomCount + 2)
                    (processArcSpine
                      (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2)
                        0 [] []) atoms)
                    freshCensus
                    (freshShiftAbove windowPosition 2 compositeIndex) windowPosition
                    shiftInTotal leftLegWithinTotal
                    (fun windowEqShift => freshShiftAbove_neWindow windowPosition
                      compositeIndex windowEqShift.symm)
                    sameReads))
          have offRight : isSameComponent
              (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).links (windowPosition + 1)
              (natListGetAt
                (List.range (bottomCount + 2)
                  ++ (processArcSpine
                    (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                      [] []) atoms).openWires)
                (freshShiftAbove windowPosition 2 compositeIndex)) = false := by
            cases legRightTest : isSameComponent
                (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] []) atoms).links (windowPosition + 1)
                (natListGetAt
                  (List.range (bottomCount + 2)
                    ++ (processArcSpine
                      (ArcWireState.mk (List.range (bottomCount + 2)) []
                        (bottomCount + 2) 0 [] []) atoms).openWires)
                  (freshShiftAbove windowPosition 2 compositeIndex)) with
            | false => rfl
            | true =>
                have sameReads : isSameComponent
                    (processArcSpine
                      (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2)
                        0 [] []) atoms).links
                    (natListGetAt
                      (List.range (bottomCount + 2)
                        ++ (processArcSpine
                          (ArcWireState.mk (List.range (bottomCount + 2)) []
                            (bottomCount + 2) 0 [] []) atoms).openWires)
                      (freshShiftAbove windowPosition 2 compositeIndex))
                    (natListGetAt
                      (List.range (bottomCount + 2)
                        ++ (processArcSpine
                          (ArcWireState.mk (List.range (bottomCount + 2)) []
                            (bottomCount + 2) 0 [] []) atoms).openWires)
                      (windowPosition + 1)) = true := by
                  rw [readAtRightLeg]
                  exact (isSameComponent_symm
                    (processArcSpine
                      (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2)
                        0 [] []) atoms).links
                    (natListGetAt
                      (List.range (bottomCount + 2)
                        ++ (processArcSpine
                          (ArcWireState.mk (List.range (bottomCount + 2)) []
                            (bottomCount + 2) 0 [] []) atoms).openWires)
                      (freshShiftAbove windowPosition 2 compositeIndex))
                    (windowPosition + 1)).trans
                    legRightTest
                exact False.elim (shiftPartnerNeRight
                  (partnerIndexOf_uniqueSameComponent (bottomCount + 2)
                    (processArcSpine
                      (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2)
                        0 [] []) atoms)
                    freshCensus
                    (freshShiftAbove windowPosition 2 compositeIndex) (windowPosition + 1)
                    shiftInTotal rightLegWithinTotal
                    (fun succEqShift => freshShiftAbove_neWindowSucc windowPosition
                      compositeIndex succEqShift.symm)
                    sameReads))
          have offCorr := arcCupHeadFolded_partnerScan_offFused bottomCount windowPosition
            windowFits atoms chained compositeIndex indexInRange offLeft offRight
          rw [offCorr]
          exact (freshUnshiftAbove_ofShifted windowPosition
            (partnerIndexOf
              (processArcSpine
                (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0
                  [] []) windowPosition) atoms).links
              (List.range bottomCount
                ++ (processArcSpine
                  (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0
                    [] []) windowPosition) atoms).openWires)
              (bottomCount
                + (processArcSpine
                  (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0
                    [] []) windowPosition) atoms).openWires.length)
              compositeIndex)).symm

/-- **Honesty marker — the per-index cup partner dispatch is SHIPPED (peel campaign H, cup
rung 4 close).**  `arcCupPartnerTransport` packages the three-way value analysis as one
function of fresh data, and `arcCupHeadFolded_partnerDispatch` proves the composite
partner equals it at every in-range index under the legs-separate hypothesis — the census
coincidence (fresh partner = leg index iff the read attaches to the leg) keys the fused
branches, and the off-fused branch rides the transparency correspondence through the
downshift round trip.  What this marker does NOT claim: the cup partner-LIST
correspondence and diagram leg over this dispatch, and the legs-connected
(cup-cancellation) world.  `= true`. -/
def fxMode_hasArcCupPartnerDispatch : Bool := true

end FX1Poly.Polygraph
