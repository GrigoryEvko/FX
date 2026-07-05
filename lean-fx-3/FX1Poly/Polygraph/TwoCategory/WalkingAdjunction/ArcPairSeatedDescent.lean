import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWindowLocality
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWindowSuffix
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFreshShift
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapRenameable
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.AdjunctionModeParity

/-! # ArcPairSeatedDescent — the backward seating descent through one arc step

The witness-construction campaign's positional kernel: if the tracked pair of seed ports
sits ADJACENT (`ArcPairSeated`) after a cup or cap fires, it sat adjacent BEFORE, at a seat
shifted by the step's width change — with one exception per arm, each refuted:

* a cup splicing INTO the seat window would put a fresh leg at a seat read, but the pair's
  nodes are below `nextFresh` (`arcPairSeated_beforeCupStep`);
* a cap at the seat's successor would CLOSE A GAP — a pre-state pair at distance three
  fuses to adjacency.  Positionally this is the one genuinely new-adjacency case
  (`arcPairSeated_beforeCapStep` excludes it by hypothesis), and at the walking adjunction
  it dies on PARITY: a cap window has `tip` parity while the successor of a `tip` seat has
  `base` parity (`arcPairSeated_beforeCapStep_ofTipParities`).

The side dichotomy in each conclusion (seat pair strictly below the window, or window
at-or-before the seat) is exactly the bubble-to-front step data: the descent recursion
reads off the `stepLeftOf`/`stepRightOf` inert distances from these inequalities.

Raw Lean 4 + Init; structural recursion only; per-declaration `#assert_no_axioms` gated in
the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- The tracked pair sits ADJACENT in the state's open-wire list: the left node read at
`seatPosition`, the right node read at `seatPosition + 1`, with the seat window in range. -/
def ArcPairSeated (leftNode rightNode seatPosition : Nat) (state : ArcWireState) : Prop :=
  natListGetAt state.openWires seatPosition = leftNode
    ∧ natListGetAt state.openWires (seatPosition + 1) = rightNode
    ∧ seatPosition + 2 ≤ state.openWires.length

/-- **Backward descent through a cup.**  A pair of below-fresh nodes seated after a cup
step was seated before it: strictly below the splice window at the SAME seat, or past it
at the seat two lower.  A splice into the seat window is impossible — both spliced legs
are at-or-above `nextFresh`, and the seat reads are below it. -/
theorem arcPairSeated_beforeCupStep (state : ArcWireState) (windowPosition : Nat)
    {leftNode rightNode seatAfter : Nat}
    (isLeftBelowFresh : leftNode < state.nextFresh)
    (isRightBelowFresh : rightNode < state.nextFresh)
    (windowFits : windowPosition ≤ state.openWires.length)
    (seatedAfter : ArcPairSeated leftNode rightNode seatAfter
      (stepCupArc state windowPosition)) :
    (ArcPairSeated leftNode rightNode seatAfter state ∧ seatAfter + 2 ≤ windowPosition)
      ∨ (∃ seatBefore, seatBefore + 2 = seatAfter
          ∧ ArcPairSeated leftNode rightNode seatBefore state
          ∧ windowPosition ≤ seatBefore) := by
  have readLeft : natListGetAt (natListInsertAt state.openWires windowPosition
      [state.nextFresh, state.nextFresh + 1]) seatAfter = leftNode := seatedAfter.1
  have readRight : natListGetAt (natListInsertAt state.openWires windowPosition
      [state.nextFresh, state.nextFresh + 1]) (seatAfter + 1) = rightNode := seatedAfter.2.1
  have boundAfter : seatAfter + 2 ≤ (natListInsertAt state.openWires windowPosition
      [state.nextFresh, state.nextFresh + 1]).length := seatedAfter.2.2
  cases Nat.lt_or_ge (seatAfter + 1) windowPosition with
  | inl isPairBelowWindow =>
      exact Or.inl ⟨⟨(natListGetAt_natListInsertAt_below state.openWires windowPosition
            [state.nextFresh, state.nextFresh + 1] seatAfter
            (Nat.lt_of_succ_lt isPairBelowWindow)
            (Nat.lt_of_lt_of_le (Nat.lt_of_succ_lt isPairBelowWindow) windowFits)).symm.trans
            readLeft,
          (natListGetAt_natListInsertAt_below state.openWires windowPosition
            [state.nextFresh, state.nextFresh + 1] (seatAfter + 1) isPairBelowWindow
            (Nat.lt_of_lt_of_le isPairBelowWindow windowFits)).symm.trans readRight,
          Nat.le_trans isPairBelowWindow windowFits⟩,
        isPairBelowWindow⟩
  | inr isWindowAtOrBeforePairEnd =>
      cases Nat.lt_or_ge seatAfter windowPosition with
      | inl isSeatBelowWindow =>
          have windowEq : windowPosition = seatAfter + 1 :=
            Nat.le_antisymm isWindowAtOrBeforePairEnd isSeatBelowWindow
          rw [windowEq] at readRight windowFits
          have rightIsFresh : rightNode = state.nextFresh :=
            readRight.symm.trans
              (natListGetAt_natListInsertAt_inside state.openWires (seatAfter + 1)
                [state.nextFresh, state.nextFresh + 1] 0 (Nat.zero_lt_succ 1) windowFits)
          exact absurd (rightIsFresh ▸ isRightBelowFresh) (Nat.lt_irrefl state.nextFresh)
      | inr isWindowAtOrBeforeSeat =>
          cases Nat.lt_or_ge seatAfter (windowPosition + 1) with
          | inl isSeatAtWindow =>
              have seatEq : seatAfter = windowPosition :=
                Nat.le_antisymm (Nat.le_of_lt_succ isSeatAtWindow) isWindowAtOrBeforeSeat
              rw [seatEq] at readLeft
              have leftIsFresh : leftNode = state.nextFresh :=
                readLeft.symm.trans
                  (natListGetAt_natListInsertAt_inside state.openWires windowPosition
                    [state.nextFresh, state.nextFresh + 1] 0 (Nat.zero_lt_succ 1)
                    windowFits)
              exact absurd (leftIsFresh ▸ isLeftBelowFresh) (Nat.lt_irrefl state.nextFresh)
          | inr isWindowStrictlyBeforeSeat =>
              cases Nat.lt_or_ge seatAfter (windowPosition + 2) with
              | inl isSeatAtSecondLeg =>
                  have seatEq : seatAfter = windowPosition + 1 :=
                    Nat.le_antisymm (Nat.le_of_lt_succ isSeatAtSecondLeg)
                      isWindowStrictlyBeforeSeat
                  rw [seatEq] at readLeft
                  have leftIsSecondFresh : leftNode = state.nextFresh + 1 :=
                    readLeft.symm.trans
                      (natListGetAt_natListInsertAt_inside state.openWires windowPosition
                        [state.nextFresh, state.nextFresh + 1] 1 (Nat.lt_succ_self 1)
                        windowFits)
                  have isSecondLegBelowSelf : state.nextFresh + 1 < state.nextFresh :=
                    leftIsSecondFresh ▸ isLeftBelowFresh
                  exact absurd
                    (Nat.lt_trans (Nat.lt_succ_self state.nextFresh) isSecondLegBelowSelf)
                    (Nat.lt_irrefl state.nextFresh)
              | inr isWindowPairBeforeSeat =>
                  obtain ⟨offset, offsetEq⟩ := Nat.le.dest isWindowPairBeforeSeat
                  subst offsetEq
                  rw [← Nat.add_right_comm windowPosition offset 2] at readLeft readRight
                  have beforeLeft : natListGetAt state.openWires (windowPosition + offset)
                      = leftNode :=
                    (natListGetAt_natListInsertAt_pastBlock state.openWires windowPosition
                      [state.nextFresh, state.nextFresh + 1] offset windowFits).symm.trans
                      readLeft
                  have beforeRight : natListGetAt state.openWires
                      (windowPosition + offset + 1) = rightNode :=
                    (natListGetAt_natListInsertAt_pastBlock state.openWires windowPosition
                      [state.nextFresh, state.nextFresh + 1] (offset + 1)
                      windowFits).symm.trans readRight
                  rw [natListInsertAt_length state.openWires windowPosition
                    [state.nextFresh, state.nextFresh + 1]] at boundAfter
                  have beforeBound : windowPosition + offset + 2
                      ≤ state.openWires.length := by
                    rw [Nat.add_right_comm windowPosition offset 2]
                    exact Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ boundAfter)
                  exact Or.inr ⟨windowPosition + offset,
                    Nat.add_right_comm windowPosition offset 2,
                    ⟨beforeLeft, beforeRight, beforeBound⟩,
                    Nat.le_add_right windowPosition offset⟩

/-- **Backward descent through a cap, positional core.**  A pair seated after a cap step
was seated before it — strictly below the removal window at the SAME seat, or at-or-past
it at the seat two higher — PROVIDED the cap is not the gap-closing one at the seat's
successor (the only removal that creates new adjacency; excluded here by hypothesis,
refuted by parity in the walking-adjunction wrapper below). -/
theorem arcPairSeated_beforeCapStep (state : ArcWireState) (windowPosition : Nat)
    {leftNode rightNode seatAfter : Nat}
    (gapSeatNe : windowPosition ≠ seatAfter + 1)
    (windowFits : windowPosition + 2 ≤ state.openWires.length)
    (seatedAfter : ArcPairSeated leftNode rightNode seatAfter
      (stepCapArc state windowPosition)) :
    (ArcPairSeated leftNode rightNode seatAfter state ∧ seatAfter + 2 ≤ windowPosition)
      ∨ (ArcPairSeated leftNode rightNode (seatAfter + 2) state
          ∧ windowPosition ≤ seatAfter) := by
  have readLeft : natListGetAt (natListRemoveTwoAt state.openWires windowPosition) seatAfter
      = leftNode := seatedAfter.1
  have readRight : natListGetAt (natListRemoveTwoAt state.openWires windowPosition)
      (seatAfter + 1) = rightNode := seatedAfter.2.1
  have boundAfter : seatAfter + 2
      ≤ (natListRemoveTwoAt state.openWires windowPosition).length := seatedAfter.2.2
  cases Nat.lt_or_ge (seatAfter + 1) windowPosition with
  | inl isPairBelowWindow =>
      exact Or.inl ⟨⟨(natListGetAt_natListRemoveTwoAt_below state.openWires windowPosition
            seatAfter (Nat.lt_of_succ_lt isPairBelowWindow)).symm.trans readLeft,
          (natListGetAt_natListRemoveTwoAt_below state.openWires windowPosition
            (seatAfter + 1) isPairBelowWindow).symm.trans readRight,
          Nat.le_trans isPairBelowWindow
            (Nat.le_trans (Nat.le_add_right windowPosition 2) windowFits)⟩,
        isPairBelowWindow⟩
  | inr isWindowAtOrBeforePairEnd =>
      cases Nat.lt_or_ge seatAfter windowPosition with
      | inl isSeatBelowWindow =>
          exact absurd (Nat.le_antisymm isWindowAtOrBeforePairEnd isSeatBelowWindow)
            gapSeatNe
      | inr isWindowAtOrBeforeSeat =>
          obtain ⟨offset, offsetEq⟩ := Nat.le.dest isWindowAtOrBeforeSeat
          subst offsetEq
          have beforeLeft : natListGetAt state.openWires (windowPosition + offset + 2)
              = leftNode :=
            (natListGetAt_natListRemoveTwoAt_pastPair state.openWires windowPosition offset
              windowFits).symm.trans readLeft
          have beforeRight : natListGetAt state.openWires (windowPosition + offset + 2 + 1)
              = rightNode :=
            (natListGetAt_natListRemoveTwoAt_pastPair state.openWires windowPosition
              (offset + 1) windowFits).symm.trans readRight
          have lengthEq := natListRemoveTwoAt_length state.openWires windowPosition
            windowFits
          exact Or.inr ⟨⟨beforeLeft, beforeRight,
              lengthEq ▸ Nat.add_le_add_right boundAfter 2⟩,
            Nat.le_add_right windowPosition offset⟩

/-- ★ **Backward descent through a cap at the walking adjunction.**  The gap-closing
exclusion is FREE from parity: a consuming cap's window position has `tip` parity, but the
successor of a `tip`-parity seat has `base` parity — so a cap at the seat's successor
cannot exist, and a seated pair descends through EVERY cap of the spine. -/
theorem arcPairSeated_beforeCapStep_ofTipParities (state : ArcWireState)
    (windowPosition : Nat) {leftNode rightNode seatAfter : Nat}
    {sourceMode : AdjunctionMode}
    (hasSeatTipParity :
      adjunctionModeAtDistance sourceMode seatAfter = AdjunctionMode.tip)
    (hasWindowTipParity :
      adjunctionModeAtDistance sourceMode windowPosition = AdjunctionMode.tip)
    (windowFits : windowPosition + 2 ≤ state.openWires.length)
    (seatedAfter : ArcPairSeated leftNode rightNode seatAfter
      (stepCapArc state windowPosition)) :
    (ArcPairSeated leftNode rightNode seatAfter state ∧ seatAfter + 2 ≤ windowPosition)
      ∨ (ArcPairSeated leftNode rightNode (seatAfter + 2) state
          ∧ windowPosition ≤ seatAfter) := by
  refine arcPairSeated_beforeCapStep state windowPosition ?_ windowFits seatedAfter
  intro isGapClosing
  rw [isGapClosing] at hasWindowTipParity
  have oppositeIsTip : adjunctionOppositeMode (adjunctionModeAtDistance sourceMode seatAfter)
      = AdjunctionMode.tip := hasWindowTipParity
  rw [hasSeatTipParity] at oppositeIsTip
  exact AdjunctionMode.noConfusion oppositeIsTip

/-! ## Honesty marker -/

/-- **Honesty marker — the backward seating descent is SHIPPED.**  A pair of below-fresh
nodes seated adjacent after one arc step was seated adjacent before it, with the seat
shifted by the step's width change and the window/seat side dichotomy read off: the cup's
splice-into-seat case dies on freshness, and the cap's gap-closing case dies on the
tip/base parity clash at the walking adjunction.  NOT yet shipped: threading the descent
backward through a whole untouched prefix (parity + freshness bookkeeping per step) and
assembling the bubble-to-front witness from the located `ArcPairCapWindow` certificate.
`= true`. -/
def fxMode_hasArcPairSeatedDescent : Bool := true

end FX1Poly.Polygraph
