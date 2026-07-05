import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcLoopFreedom
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupSeedCorr
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupReindexValues
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcHeadReindex

/-! # ArcCupHeadLoops — the composite cup-head fold never closes a loop

The loops leg of the cup-head transport (peel campaign H, cup rung 3).  Unlike the cap
seed (all survivors disconnected, discipline vacuous), the cup seed is genuinely
DISCIPLINED-NON-VACUOUSLY: the two inserted legs sit at window positions
`windowPosition`, `windowPosition + 1` in the SAME component, and the typed-ends
discipline holds because the peeled cup fires at `base` parity — the pair is typed
`base`/`tip` exactly as the discipline demands, so no later cap can consume it and no
loop ever closes.  The seed discipline routes every same-component query through the
shipped seed correspondence down to the one-join base query `unionFindJoin []
windowPosition (windowPosition + 1)`, whose characterization pins the pair to the legs.
With the discipline in hand the shipped chained-fold loop constancy gives the composite
`loops = 0`.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The non-vacuous discipline at the cup-head seed -/

/-- ★ **The typed open-ends discipline holds at the post-cup seed.**  Every same-component
open pair reduces (through the seed correspondence and the one-join characterization) to
the inserted leg pair `(windowPosition, windowPosition + 1)` — and that pair is typed
`base`/`tip` by the peeled cup's window parity, exactly as the discipline demands. -/
theorem arcOpenEndsDiscipline_cupHeadSeed (sourceMode : AdjunctionMode)
    (bottomCount windowPosition : Nat)
    (windowFits : windowPosition ≤ bottomCount)
    (windowParityIsBase :
      adjunctionModeAtDistance sourceMode windowPosition = AdjunctionMode.base) :
    ArcOpenEndsDiscipline sourceMode
      (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        windowPosition) := by
  intro lowPosition highPosition lowBelowHigh highInRange sameComponentHolds
  have highBelowWidth : highPosition < bottomCount + 2 := by
    have highRaw : highPosition < (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]).length := highInRange
    rw [cupHeadOpenWires_length] at highRaw
    exact highRaw
  have lowBelowWidth : lowPosition < bottomCount + 2 :=
    Nat.lt_trans lowBelowHigh highBelowWidth
  have lowReadIsImage : natListGetAt
      (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) lowPosition
    = arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1 lowPosition :=
    (arcHeadReindex_readsBelow
      (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1 lowPosition
      (by rw [cupHeadOpenWires_length]; exact lowBelowWidth)).symm
  have highReadIsImage : natListGetAt
      (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) highPosition
    = arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1 highPosition :=
    (arcHeadReindex_readsBelow
      (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1 highPosition
      (by rw [cupHeadOpenWires_length]; exact highBelowWidth)).symm
  have imageQuery : isSameComponent
      (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        windowPosition).links
      (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1 lowPosition)
      (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1 highPosition) = true := by
    have rawQuery : isSameComponent
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition).links
        (natListGetAt (natListInsertAt (List.range bottomCount) windowPosition
          [bottomCount, bottomCount + 1]) lowPosition)
        (natListGetAt (natListInsertAt (List.range bottomCount) windowPosition
          [bottomCount, bottomCount + 1]) highPosition) = true := sameComponentHolds
    rw [lowReadIsImage, highReadIsImage] at rawQuery
    exact rawQuery
  have baseQuery : isSameComponent (unionFindJoin [] windowPosition (windowPosition + 1))
      lowPosition highPosition = true :=
    (arcComponentShiftCorr_cupHeadSeedState bottomCount windowPosition windowFits
      lowPosition highPosition).symm.trans imageQuery
  rw [isSameComponent_unionFindJoin [] isUnionFindForest_nil windowPosition
    (windowPosition + 1) lowPosition highPosition] at baseQuery
  have lowHighSeparate : isSameComponent [] lowPosition highPosition = false :=
    decide_eq_false (fun valuesEqual =>
      Nat.lt_irrefl highPosition
        ((show lowPosition = highPosition from valuesEqual) ▸ lowBelowHigh))
  cases Nat.decEq lowPosition windowPosition with
  | isTrue lowIsWindow =>
      cases Nat.decEq highPosition (windowPosition + 1) with
      | isTrue highIsRight =>
          refine ⟨?_, ?_⟩
          · rw [lowIsWindow]
            exact windowParityIsBase
          · rw [highIsRight]
            show adjunctionOppositeMode (adjunctionModeAtDistance sourceMode windowPosition)
              = AdjunctionMode.tip
            rw [windowParityIsBase]
            rfl
      | isFalse highNotRight =>
          have windowLowSame : isSameComponent [] windowPosition lowPosition = true :=
            decide_eq_true lowIsWindow.symm
          have rightHighSeparate :
              isSameComponent [] (windowPosition + 1) highPosition = false :=
            decide_eq_false (fun legEqualsHigh => highNotRight legEqualsHigh.symm)
          have windowBelowHigh : windowPosition < highPosition :=
            lowIsWindow ▸ lowBelowHigh
          have windowHighSeparate :
              isSameComponent [] windowPosition highPosition = false :=
            decide_eq_false (fun windowEqualsHigh =>
              Nat.lt_irrefl highPosition
                ((show windowPosition = highPosition from windowEqualsHigh)
                  ▸ windowBelowHigh))
          rw [lowHighSeparate, windowLowSame, rightHighSeparate,
            windowHighSeparate] at baseQuery
          have queryIsFalse : false = true := baseQuery
          exact Bool.noConfusion queryIsFalse
  | isFalse lowNotWindow =>
      have windowLowSeparate : isSameComponent [] windowPosition lowPosition = false :=
        decide_eq_false (fun windowEqualsLow => lowNotWindow windowEqualsLow.symm)
      cases Nat.decEq highPosition windowPosition with
      | isTrue highIsWindow =>
          have windowHighSame : isSameComponent [] windowPosition highPosition = true :=
            decide_eq_true highIsWindow.symm
          have lowBelowRight : lowPosition < windowPosition + 1 :=
            Nat.lt_trans (highIsWindow ▸ lowBelowHigh) (Nat.lt_succ_self windowPosition)
          have lowRightSeparate :
              isSameComponent [] lowPosition (windowPosition + 1) = false :=
            decide_eq_false (fun lowEqualsRight =>
              Nat.lt_irrefl (windowPosition + 1)
                ((show lowPosition = windowPosition + 1 from lowEqualsRight)
                  ▸ lowBelowRight))
          rw [lowHighSeparate, windowLowSeparate, windowHighSame,
            lowRightSeparate] at baseQuery
          have queryIsFalse : false = true := baseQuery
          exact Bool.noConfusion queryIsFalse
      | isFalse highNotWindow =>
          have windowHighSeparate :
              isSameComponent [] windowPosition highPosition = false :=
            decide_eq_false (fun windowEqualsHigh => highNotWindow windowEqualsHigh.symm)
          rw [lowHighSeparate, windowLowSeparate, windowHighSeparate] at baseQuery
          have queryIsFalse : false = true := baseQuery
          exact Bool.noConfusion queryIsFalse

/-! ## The loops leg -/

/-- ★ **The composite cup-head fold never closes a loop**: from the disciplined post-cup
seed (the legs typed `base`/`tip` by the peeled cup's window parity), the shipped
chained-fold loop constancy keeps the counter at the seed's zero. -/
theorem arcCupHeadFolded_loops_zero
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat)
    (windowFits : windowPosition ≤ bottomCount)
    (windowParityIsBase :
      adjunctionModeAtDistance overallSource windowPosition = AdjunctionMode.base)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained (bottomCount + 2) atoms) :
    (processArcSpine
      (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        windowPosition) atoms).loops = 0 :=
  processArcSpine_loops_ofChained atoms
    (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      windowPosition)
    (bottomCount + 2)
    (stepCupArc_arcStateFresh
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition
      (arcStateFresh_initial bottomCount))
    (isUnionFindForest_stepCupArc
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition
      isUnionFindForest_nil)
    (cupHeadOpenWires_length bottomCount windowPosition)
    chained
    (arcOpenEndsDiscipline_cupHeadSeed overallSource bottomCount windowPosition windowFits
      windowParityIsBase)

/-! ## Honesty marker -/

/-- **Honesty marker — the cup-head loops leg (peel campaign H, cup rung 3).**
`arcOpenEndsDiscipline_cupHeadSeed`: the typed-ends discipline holds NON-vacuously at the
post-cup seed — the seed correspondence plus the one-join characterization pin every
same-component open pair to the inserted legs `(windowPosition, windowPosition + 1)`,
typed `base`/`tip` by the peeled cup's window parity.  `arcCupHeadFolded_loops_zero`: the
composite cup-head fold therefore keeps `loops = 0` along any chained tail.  What this
marker does NOT claim: the cup partner-scan/window-partner legs, the cup
diagram/count/extract assembly rungs, or the head-cancellation assembly — the remaining
cup rungs.  `= true`. -/
def fxMode_hasArcCupHeadLoopLeg : Bool := true

end FX1Poly.Polygraph
