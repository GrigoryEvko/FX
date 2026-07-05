import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupFusedRewiring
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupLegAttachment
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingPartnerScan
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFreshUnshift

/-! # ArcCupFusedTarget — the fused entry's composite partner in closed form

The rewired case of the cup partner dispatch, CLOSED (peel campaign H, cup rung 4).  The
rewiring pins (`ArcCupFusedRewiring`) pin the composite partner at ANY opposite-leg entry;
here the canonical opposite-leg entry is PRODUCED from the fresh run's own data: the fresh
partner of the opposite window leg, downshifted through `freshUnshiftAbove`.  Scan
soundness attaches that partner's read to the opposite leg's component, the leg separation
(fresh legs in distinct components) rules out the window pair itself, and the downshift's
round trip converts the fresh index into the composite index the rewiring pin needs.  The
result: a composite entry fused to one cup leg, when the OPPOSITE leg's fresh scan finds a
partner, has its composite partner equal to the downshift of that fresh partner — a closed
form in fresh data alone.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private plumbing (per-file copy, following the codebase pattern) -/

/-- The partner scan returns either the exclude fallback or a member of the scanned list. -/
private theorem findPartnerScan_memOrExclude (links : List (Nat × Nat))
    (boundaryNodes : List Nat) (rootHere excludeIndex : Nat) : (scanned : List Nat) →
    findPartnerScan links boundaryNodes rootHere excludeIndex scanned = excludeIndex
      ∨ findPartnerScan links boundaryNodes rootHere excludeIndex scanned ∈ scanned
  | [] => Or.inl rfl
  | candidate :: rest => by
      rw [findPartnerScan_cons]
      cases headTest : (candidate != excludeIndex
          && unionFindRootOf links (natListGetAt boundaryNodes candidate) == rootHere) with
      | true => exact Or.inr (List.Mem.head rest)
      | false =>
          cases findPartnerScan_memOrExclude links boundaryNodes rootHere excludeIndex
              rest with
          | inl isExclude => exact Or.inl isExclude
          | inr isMember => exact Or.inr (List.Mem.tail candidate isMember)

/-! ## The closed-form rewired partner, left-leg orientation -/

/-- ★ **The left-leg-fused entry's composite partner is the downshifted fresh partner of
the right leg**: when the composite entry's fresh read attaches to the LEFT cup leg, the
fresh legs sit in distinct components, and the RIGHT leg's fresh partner scan finds a
partner, the composite partner equals that fresh partner downshifted through the two-zone
unshift — the closed form the cup partner-list dispatch consumes. -/
theorem arcCupFusedEntry_partnerTarget_leftLeg
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
          atoms).openWires.length)
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
    (legsSeparate : isSameComponent
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links windowPosition (windowPosition + 1) = false)
    (rightLegFound : partnerIndexOf
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
      (windowPosition + 1) ≠ windowPosition + 1) :
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
      compositeExclude
      = freshUnshiftAbove windowPosition 2
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
            (windowPosition + 1)) := by
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
  have targetRoot : unionFindRootOf
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links
      (natListGetAt
        (List.range (bottomCount + 2)
          ++ (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).openWires)
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
          (windowPosition + 1)))
      = unionFindRootOf
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).links
          (natListGetAt
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires)
            (windowPosition + 1)) :=
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
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).openWires)
          (windowPosition + 1)))
      (windowPosition + 1)
      (List.range
        (bottomCount + 2
          + (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).openWires.length))
      rightLegFound
  have targetInFresh : partnerIndexOf
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
      (windowPosition + 1)
      < bottomCount + 2
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length := by
    cases findPartnerScan_memOrExclude
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
            (windowPosition + 1)))
        (windowPosition + 1)
        (List.range
          (bottomCount + 2
            + (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).openWires.length)) with
    | inl isExclude => exact False.elim (rightLegFound isExclude)
    | inr isMember => exact mem_range_imp_lt isMember
  have targetAttachment : isSameComponent
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links (windowPosition + 1)
      (natListGetAt
        (List.range (bottomCount + 2)
          ++ (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).openWires)
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
          (windowPosition + 1))) = true := by
    rw [readAtRightLeg] at targetRoot
    exact decide_eq_true targetRoot.symm
  have targetNeWindow : partnerIndexOf
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
      (windowPosition + 1) ≠ windowPosition := fun targetEqWindow => by
    rw [targetEqWindow, readAtLeftLeg] at targetAttachment
    exact Bool.noConfusion (legsSeparate.symm.trans
      ((isSameComponent_symm
        (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).links windowPosition (windowPosition + 1)).trans targetAttachment))
  have targetNeExcludeComposite : freshUnshiftAbove windowPosition 2
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
        (windowPosition + 1)) ≠ compositeExclude := fun downshiftEqExclude => by
    have targetEqShift : partnerIndexOf
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
        (windowPosition + 1)
        = freshShiftAbove windowPosition 2 compositeExclude :=
      (freshShiftAbove_ofUnshifted windowPosition
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
          (windowPosition + 1))
        targetNeWindow rightLegFound).symm.trans
        (congrArg (freshShiftAbove windowPosition 2) downshiftEqExclude)
    rw [targetEqShift] at targetAttachment
    exact Bool.noConfusion (legsSeparate.symm.trans
      (decide_eq_true ((of_decide_eq_true excludeReachesLeftLeg).trans
        (of_decide_eq_true targetAttachment).symm)))
  have targetInPadded : partnerIndexOf
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
      (windowPosition + 1)
      < bottomCount
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length + 2 := by
    rw [Nat.add_right_comm bottomCount
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).openWires.length 2]
    exact targetInFresh
  have downshiftInRange : freshUnshiftAbove windowPosition 2
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
        (windowPosition + 1))
      < bottomCount
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length :=
    freshUnshiftAbove_ltTotal windowPosition
      (bottomCount
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length)
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
        (windowPosition + 1))
      targetInPadded targetNeWindow rightLegFound
      (Nat.le_trans windowFits
        (Nat.le_add_right bottomCount
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).openWires.length))
  have shiftedTargetReachesRight : isSameComponent
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links (windowPosition + 1)
      (natListGetAt
        (List.range (bottomCount + 2)
          ++ (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).openWires)
        (freshShiftAbove windowPosition 2
          (freshUnshiftAbove windowPosition 2
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
              (windowPosition + 1))))) = true := by
    rw [freshShiftAbove_ofUnshifted windowPosition
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
        (windowPosition + 1))
      targetNeWindow rightLegFound]
    exact targetAttachment
  exact arcCupFusedEntry_partnerRewires_leftLeg bottomCount windowPosition windowFits
    atoms chained compositeExclude
    (freshUnshiftAbove windowPosition 2
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
        (windowPosition + 1)))
    excludeInRange downshiftInRange targetNeExcludeComposite
    excludeReachesLeftLeg shiftedTargetReachesRight

/-! ## The closed-form rewired partner, right-leg orientation -/

/-- ★ **The right-leg-fused entry's composite partner is the downshifted fresh partner of
the left leg** — the mirror orientation: the entry's fresh read attaches to the RIGHT cup
leg and the LEFT leg's fresh partner scan finds a partner. -/
theorem arcCupFusedEntry_partnerTarget_rightLeg
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
          atoms).openWires.length)
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
    (legsSeparate : isSameComponent
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links windowPosition (windowPosition + 1) = false)
    (leftLegFound : partnerIndexOf
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
      windowPosition ≠ windowPosition) :
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
      compositeExclude
      = freshUnshiftAbove windowPosition 2
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
            windowPosition) := by
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
  have targetRoot : unionFindRootOf
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links
      (natListGetAt
        (List.range (bottomCount + 2)
          ++ (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).openWires)
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
          windowPosition))
      = unionFindRootOf
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).links
          (natListGetAt
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires)
            windowPosition) :=
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
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).openWires)
          windowPosition))
      windowPosition
      (List.range
        (bottomCount + 2
          + (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).openWires.length))
      leftLegFound
  have targetInFresh : partnerIndexOf
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
      windowPosition
      < bottomCount + 2
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length := by
    cases findPartnerScan_memOrExclude
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
            windowPosition))
        windowPosition
        (List.range
          (bottomCount + 2
            + (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).openWires.length)) with
    | inl isExclude => exact False.elim (leftLegFound isExclude)
    | inr isMember => exact mem_range_imp_lt isMember
  have targetAttachment : isSameComponent
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links windowPosition
      (natListGetAt
        (List.range (bottomCount + 2)
          ++ (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).openWires)
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
          windowPosition)) = true := by
    rw [readAtLeftLeg] at targetRoot
    exact decide_eq_true targetRoot.symm
  have targetNeWindowSucc : partnerIndexOf
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
      windowPosition ≠ windowPosition + 1 := fun targetEqWindowSucc => by
    rw [targetEqWindowSucc, readAtRightLeg] at targetAttachment
    exact Bool.noConfusion (legsSeparate.symm.trans targetAttachment)
  have targetNeExcludeComposite : freshUnshiftAbove windowPosition 2
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
        windowPosition) ≠ compositeExclude := fun downshiftEqExclude => by
    have targetEqShift : partnerIndexOf
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
        windowPosition
        = freshShiftAbove windowPosition 2 compositeExclude :=
      (freshShiftAbove_ofUnshifted windowPosition
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
          windowPosition)
        leftLegFound targetNeWindowSucc).symm.trans
        (congrArg (freshShiftAbove windowPosition 2) downshiftEqExclude)
    rw [targetEqShift] at targetAttachment
    exact Bool.noConfusion (legsSeparate.symm.trans
      (decide_eq_true ((of_decide_eq_true targetAttachment).trans
        (of_decide_eq_true excludeReachesRightLeg).symm)))
  have targetInPadded : partnerIndexOf
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
      windowPosition
      < bottomCount
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length + 2 := by
    rw [Nat.add_right_comm bottomCount
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).openWires.length 2]
    exact targetInFresh
  have downshiftInRange : freshUnshiftAbove windowPosition 2
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
        windowPosition)
      < bottomCount
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length :=
    freshUnshiftAbove_ltTotal windowPosition
      (bottomCount
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length)
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
        windowPosition)
      targetInPadded leftLegFound targetNeWindowSucc
      (Nat.le_trans windowFits
        (Nat.le_add_right bottomCount
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).openWires.length))
  have shiftedTargetReachesLeft : isSameComponent
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links windowPosition
      (natListGetAt
        (List.range (bottomCount + 2)
          ++ (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).openWires)
        (freshShiftAbove windowPosition 2
          (freshUnshiftAbove windowPosition 2
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
              windowPosition)))) = true := by
    rw [freshShiftAbove_ofUnshifted windowPosition
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
        windowPosition)
      leftLegFound targetNeWindowSucc]
    exact targetAttachment
  exact arcCupFusedEntry_partnerRewires_rightLeg bottomCount windowPosition windowFits
    atoms chained compositeExclude
    (freshUnshiftAbove windowPosition 2
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
        windowPosition))
    excludeInRange downshiftInRange targetNeExcludeComposite
    excludeReachesRightLeg shiftedTargetReachesLeft

/-- **Honesty marker — the fused entry's composite partner is in CLOSED FORM at both leg
orientations (peel campaign H, cup rung 4).**
`arcCupFusedEntry_partnerTarget_leftLeg` / `_rightLeg`: a composite entry fused to one cup
leg, with separated fresh legs and the opposite leg's fresh scan finding a partner, has
its composite partner equal to the downshift (`freshUnshiftAbove`) of that fresh partner.
Together with the off-fused transparency and the orphaned fallback this completes the
per-index value analysis.  What this marker does NOT claim: the assembled per-index
dispatch equation over the component-test case split and the cup partner-list
correspondence.  `= true`. -/
def fxMode_hasArcCupFusedTarget : Bool := true

end FX1Poly.Polygraph
