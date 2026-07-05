import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupFusedRewiring
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupLegAttachment
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingScanFallback

/-! # ArcCupFusedFallback — the orphaned-leg fused entry falls back to itself (peel campaign H, cup rung 4)

The degenerate branch of the fused dispatch: a composite entry whose fresh read attaches to
the LEFT cup leg, while the RIGHT leg's fresh partner scan falls back (its component has no
other boundary token), has NO composite partner — its composite scan returns its own index.
The proof dissects any would-be passer through the head correspondence into the joined-fresh
three-disjunct formula and kills each disjunct: a same-component passer is a third census
token on the left leg; a right-leg passer forces the fresh scan at the right leg to find it,
contradicting the orphan hypothesis; and a crossing passer connects the legs, contradicting
the separation forced by the fused witness itself.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private plumbing -/

private theorem shiftIndexWithinFreshTotal (windowPosition bottomCount freshLength index : Nat)
    (indexInRange : index < bottomCount + freshLength) :
    freshShiftAbove windowPosition 2 index < bottomCount + 2 + freshLength := by
  cases Nat.lt_or_ge index windowPosition with
  | inl below =>
      rw [freshShiftAbove_ofNotLe windowPosition 2 index
        (fun windowLe => Nat.lt_irrefl windowPosition (Nat.lt_of_le_of_lt windowLe below))]
      exact Nat.lt_of_lt_of_le indexInRange
        (Nat.le_trans (Nat.le_add_right (bottomCount + freshLength) 2)
          (Nat.le_of_eq (Nat.add_right_comm bottomCount freshLength 2)))
  | inr atOrPast =>
      rw [freshShiftAbove_ofLe windowPosition 2 index atOrPast]
      exact Nat.lt_of_lt_of_le (Nat.succ_lt_succ (Nat.succ_lt_succ indexInRange))
        (Nat.le_of_eq (Nat.add_right_comm bottomCount freshLength 2))

/-! ## The fallback pin at the left-leg orientation -/

/-- ★ **The orphaned-leg fused entry has no composite partner (left-leg fused)**: when the
composite entry's fresh read attaches to the LEFT cup leg and the RIGHT leg's fresh partner
scan falls back, the composite partner scan at the entry also falls back — every candidate
passer dies in the joined-fresh dissection (third census token / forced right-leg find /
leg connection). -/
theorem arcCupFusedEntry_partnerFallback_leftLeg
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
    (rightLegOrphaned : partnerIndexOf
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
      (windowPosition + 1) = windowPosition + 1) :
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
      compositeExclude = compositeExclude := by
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
  have freshForest : isUnionFindForest
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links :=
    isUnionFindForest_processArcSpine atoms
      (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
      isUnionFindForest_nil
  have freshCensus := arcBoundaryCensus_ofChainedSpineList (bottomCount + 2) atoms chained
  have shiftExcludeInTotal := shiftIndexWithinFreshTotal windowPosition bottomCount
    (processArcSpine
      (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
      atoms).openWires.length
    compositeExclude excludeInRange
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
  have legsDisconnected : isSameComponent
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links windowPosition (windowPosition + 1) = false :=
    arcFreshLegsDisconnected_ofFusedWitness bottomCount windowPosition windowFits atoms
      chained (freshShiftAbove windowPosition 2 compositeExclude)
      shiftExcludeInTotal
      (freshShiftAbove_neWindow windowPosition compositeExclude)
      (freshShiftAbove_neWindowSucc windowPosition compositeExclude)
      excludeReachesLeftLeg
  show findPartnerScan
      (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (List.range bottomCount
        ++ (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires)
      (unionFindRootOf
        (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (natListGetAt
          (List.range bottomCount
            ++ (processArcSpine
              (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).openWires)
          compositeExclude))
      compositeExclude
      (List.range
        (bottomCount
          + (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires.length)) = compositeExclude
  exact findPartnerScan_eqExclude_ofNoPasser
    (processArcSpine
      (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        windowPosition) atoms).links
    (List.range bottomCount
      ++ (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).openWires)
    (unionFindRootOf
      (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (natListGetAt
        (List.range bottomCount
          ++ (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires)
        compositeExclude))
    compositeExclude
    (List.range
      (bottomCount
        + (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires.length))
    (fun passer passerMem passerNe passerRoot => by
      have passerInComposite : passer
          < bottomCount
            + (processArcSpine
              (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).openWires.length :=
        mem_range_imp_lt passerMem
      have passerInFresh : passer
          < bottomCount
            + (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).openWires.length := by
        rw [arcCupHeadFolded_openWiresLength bottomCount windowPosition atoms]
          at passerInComposite
        exact passerInComposite
      have shiftPasserInTotal := shiftIndexWithinFreshTotal windowPosition bottomCount
        (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length
        passer passerInFresh
      have excludeReadEq := arcCupHeadFolded_boundaryRead_shifted bottomCount windowPosition
        windowFits atoms compositeExclude excludeInRange
      have passerReadEq := arcCupHeadFolded_boundaryRead_shifted bottomCount windowPosition
        windowFits atoms passer passerInFresh
      have compositeSame : isSameComponent
          (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).links
          (natListGetAt
            (List.range bottomCount
              ++ (processArcSpine
                (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0
                  [] []) windowPosition) atoms).openWires)
            compositeExclude)
          (natListGetAt
            (List.range bottomCount
              ++ (processArcSpine
                (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0
                  [] []) windowPosition) atoms).openWires)
            passer) = true :=
        decide_eq_true passerRoot.symm
      rw [excludeReadEq, passerReadEq] at compositeSame
      have joinedSame := (arcComponentShiftCorr_cupHeadFolded bottomCount windowPosition
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
          (freshShiftAbove windowPosition 2 passer))).symm.trans compositeSame
      rw [isSameComponent_unionFindJoin
        (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).links
        freshForest windowPosition (windowPosition + 1)
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
          (freshShiftAbove windowPosition 2 passer))] at joinedSame
      cases directTest : isSameComponent
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).links
          (natListGetAt
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires)
            (freshShiftAbove windowPosition 2 compositeExclude))
          (natListGetAt
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires)
            (freshShiftAbove windowPosition 2 passer)) with
      | true =>
          have exclToLeg : isSameComponent
              (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).links
              (natListGetAt
                (List.range (bottomCount + 2)
                  ++ (processArcSpine
                    (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                      [] []) atoms).openWires)
                (freshShiftAbove windowPosition 2 compositeExclude))
              windowPosition = true :=
            (isSameComponent_symm
              (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).links
              (natListGetAt
                (List.range (bottomCount + 2)
                  ++ (processArcSpine
                    (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                      [] []) atoms).openWires)
                (freshShiftAbove windowPosition 2 compositeExclude))
              windowPosition).trans excludeReachesLeftLeg
          have sameReadTwelve : isSameComponent
              (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).links
              (natListGetAt
                (List.range (bottomCount + 2)
                  ++ (processArcSpine
                    (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                      [] []) atoms).openWires)
                (freshShiftAbove windowPosition 2 compositeExclude))
              (natListGetAt
                (List.range (bottomCount + 2)
                  ++ (processArcSpine
                    (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                      [] []) atoms).openWires)
                windowPosition) = true := by
            rw [readAtLeftLeg]
            exact exclToLeg
          exact arcBoundaryCensus_boundaryNodes (bottomCount + 2)
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms)
            freshCensus
            (freshShiftAbove windowPosition 2 compositeExclude) windowPosition
            (freshShiftAbove windowPosition 2 passer)
            shiftExcludeInTotal leftLegWithinTotal shiftPasserInTotal
            (fun excludeEqLeft =>
              freshShiftAbove_neWindow windowPosition compositeExclude excludeEqLeft)
            (fun excludeEqPasser => passerNe
              (freshShiftAbove_two_injective windowPosition compositeExclude passer
                excludeEqPasser).symm)
            (fun leftEqPasser =>
              freshShiftAbove_neWindow windowPosition passer leftEqPasser.symm)
            sameReadTwelve directTest
      | false =>
          rw [directTest] at joinedSame
          cases legWTest : isSameComponent
              (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).links windowPosition
              (natListGetAt
                (List.range (bottomCount + 2)
                  ++ (processArcSpine
                    (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                      [] []) atoms).openWires)
                (freshShiftAbove windowPosition 2 compositeExclude)) with
          | false =>
              rw [legWTest] at joinedSame
              cases legYTest : isSameComponent
                  (processArcSpine
                    (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                      [] []) atoms).links windowPosition
                  (natListGetAt
                    (List.range (bottomCount + 2)
                      ++ (processArcSpine
                        (ArcWireState.mk (List.range (bottomCount + 2)) []
                          (bottomCount + 2) 0 [] []) atoms).openWires)
                    (freshShiftAbove windowPosition 2 passer)) with
              | false =>
                  rw [legYTest] at joinedSame
                  exact Bool.noConfusion joinedSame
              | true =>
                  cases exclRightTest : isSameComponent
                      (processArcSpine
                        (ArcWireState.mk (List.range (bottomCount + 2)) []
                          (bottomCount + 2) 0 [] []) atoms).links
                      (natListGetAt
                        (List.range (bottomCount + 2)
                          ++ (processArcSpine
                            (ArcWireState.mk (List.range (bottomCount + 2)) []
                              (bottomCount + 2) 0 [] []) atoms).openWires)
                        (freshShiftAbove windowPosition 2 compositeExclude))
                      (windowPosition + 1) with
                  | false =>
                      rw [legYTest, exclRightTest] at joinedSame
                      exact Bool.noConfusion joinedSame
                  | true =>
                      exact Bool.noConfusion (legsDisconnected.symm.trans
                        (decide_eq_true ((of_decide_eq_true excludeReachesLeftLeg).trans
                          (of_decide_eq_true exclRightTest))))
          | true =>
              cases legW1Test : isSameComponent
                  (processArcSpine
                    (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                      [] []) atoms).links (windowPosition + 1)
                  (natListGetAt
                    (List.range (bottomCount + 2)
                      ++ (processArcSpine
                        (ArcWireState.mk (List.range (bottomCount + 2)) []
                          (bottomCount + 2) 0 [] []) atoms).openWires)
                    (freshShiftAbove windowPosition 2 passer)) with
              | true =>
                  have sameRightReads : isSameComponent
                      (processArcSpine
                        (ArcWireState.mk (List.range (bottomCount + 2)) []
                          (bottomCount + 2) 0 [] []) atoms).links
                      (natListGetAt
                        (List.range (bottomCount + 2)
                          ++ (processArcSpine
                            (ArcWireState.mk (List.range (bottomCount + 2)) []
                              (bottomCount + 2) 0 [] []) atoms).openWires)
                        (windowPosition + 1))
                      (natListGetAt
                        (List.range (bottomCount + 2)
                          ++ (processArcSpine
                            (ArcWireState.mk (List.range (bottomCount + 2)) []
                              (bottomCount + 2) 0 [] []) atoms).openWires)
                        (freshShiftAbove windowPosition 2 passer)) = true := by
                    rw [readAtRightLeg]
                    exact legW1Test
                  have forcedPartner : partnerIndexOf
                      (processArcSpine
                        (ArcWireState.mk (List.range (bottomCount + 2)) []
                          (bottomCount + 2) 0 [] []) atoms).links
                      (List.range (bottomCount + 2)
                        ++ (processArcSpine
                          (ArcWireState.mk (List.range (bottomCount + 2)) []
                            (bottomCount + 2) 0 [] []) atoms).openWires)
                      (bottomCount + 2
                        + (processArcSpine
                          (ArcWireState.mk (List.range (bottomCount + 2)) []
                            (bottomCount + 2) 0 [] []) atoms).openWires.length)
                      (windowPosition + 1) = freshShiftAbove windowPosition 2 passer :=
                    partnerIndexOf_uniqueSameComponent (bottomCount + 2)
                      (processArcSpine
                        (ArcWireState.mk (List.range (bottomCount + 2)) []
                          (bottomCount + 2) 0 [] []) atoms)
                      freshCensus (windowPosition + 1)
                      (freshShiftAbove windowPosition 2 passer)
                      rightLegWithinTotal shiftPasserInTotal
                      (freshShiftAbove_neWindowSucc windowPosition passer)
                      sameRightReads
                  exact freshShiftAbove_neWindowSucc windowPosition passer
                    (forcedPartner.symm.trans rightLegOrphaned)
              | false =>
                  rw [legWTest, legW1Test] at joinedSame
                  cases legYTest : isSameComponent
                      (processArcSpine
                        (ArcWireState.mk (List.range (bottomCount + 2)) []
                          (bottomCount + 2) 0 [] []) atoms).links windowPosition
                      (natListGetAt
                        (List.range (bottomCount + 2)
                          ++ (processArcSpine
                            (ArcWireState.mk (List.range (bottomCount + 2)) []
                              (bottomCount + 2) 0 [] []) atoms).openWires)
                        (freshShiftAbove windowPosition 2 passer)) with
                  | false =>
                      rw [legYTest] at joinedSame
                      exact Bool.noConfusion joinedSame
                  | true =>
                      cases exclRightTest : isSameComponent
                          (processArcSpine
                            (ArcWireState.mk (List.range (bottomCount + 2)) []
                              (bottomCount + 2) 0 [] []) atoms).links
                          (natListGetAt
                            (List.range (bottomCount + 2)
                              ++ (processArcSpine
                                (ArcWireState.mk (List.range (bottomCount + 2)) []
                                  (bottomCount + 2) 0 [] []) atoms).openWires)
                            (freshShiftAbove windowPosition 2 compositeExclude))
                          (windowPosition + 1) with
                      | false =>
                          rw [legYTest, exclRightTest] at joinedSame
                          exact Bool.noConfusion joinedSame
                      | true =>
                          exact Bool.noConfusion (legsDisconnected.symm.trans
                            (decide_eq_true
                              ((of_decide_eq_true excludeReachesLeftLeg).trans
                                (of_decide_eq_true exclRightTest)))))

/-- **Honesty marker — the orphaned-leg fused fallback is SHIPPED at the left-leg
orientation (peel campaign H, cup rung 4).**  `arcCupFusedEntry_partnerFallback_leftLeg`:
a composite entry fused to the LEFT cup leg whose RIGHT leg is orphaned falls back to its
own index in the composite partner scan.  What this marker does NOT claim: the mirror
right-leg orientation, the assembled per-index dispatch, and the cup partner-list
correspondence.  `= true`. -/
def fxMode_hasArcCupFusedFallbackLeft : Bool := true

end FX1Poly.Polygraph
