import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingBoundaryReads

/-! # mode-3 — connectivity-view stability under a cap (the view-sim cap arm)

The MODE3-C congruence fields need two runs related only through the CONNECTIVITY VIEW —
`openWires.length`, `loops`, and the boundary same-component relation `matchingSameComponent` on
in-range index pairs — to stay related through disciplined steps.  This file ships the CAP arm's
three transports:

  * ★ `matchingViewAgrees_stepCap` — the crux: if two states' views agree on all in-range pairs,
    the post-cap views agree on all post-cap in-range pairs.  Both post-cap reads factor through
    the SAME `capBoundaryReindex` (the reindex is state-independent), both post-cap link tables
    are unconditional joins on the two window reads, and the flat-disjunction characterization
    `isSameComponent_unionFindJoin` reduces each side to five view atoms at old in-range indices
    — where the premise closes them pointwise;
  * `matchingViewLoops_stepCap` — the loop counts stay equal: each side increments by ITS view's
    boolean at the window (`stepCap_loops_eq_addViewIncrement`), and the window indices are in
    range, so the premise equates the increments;
  * `matchingViewLength_stepCap` — the open-wire counts stay equal (additive length bookkeeping;
    the cancellation is two `Nat.succ.inj` applications — core `Nat.add_right_cancel` leaks).

The cup arm (fresh-leg isolation) and the fold are the next bricks.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **View agreement is stable under a cap.**  Two states whose connectivity views agree on all
in-range boundary-index pairs keep agreeing after capping at the same in-range window: both
post-cap reads factor through the state-independent `capBoundaryReindex`, both post-cap link
tables are the unconditional join on the two window reads, and the flat-disjunction
characterization reduces each side to five pre-cap view atoms — all at in-range indices, where
the agreement premise closes them pointwise. -/
theorem matchingViewAgrees_stepCap (bottomCount : Nat) (stateS stateT : WireState)
    (position : Nat) (windowS : position + 2 ≤ stateS.openWires.length)
    (lengthEq : stateT.openWires.length = stateS.openWires.length)
    (forestS : isUnionFindForest stateS.links) (forestT : isUnionFindForest stateT.links)
    (viewAgrees : ∀ firstIndex secondIndex,
      firstIndex < bottomCount + stateS.openWires.length →
      secondIndex < bottomCount + stateS.openWires.length →
      matchingSameComponent bottomCount stateT firstIndex secondIndex
        = matchingSameComponent bottomCount stateS firstIndex secondIndex)
    (firstIndex secondIndex : Nat)
    (firstInRange : firstIndex < bottomCount + (stepCap stateS position).openWires.length)
    (secondInRange : secondIndex < bottomCount + (stepCap stateS position).openWires.length) :
    matchingSameComponent bottomCount (stepCap stateT position) firstIndex secondIndex
      = matchingSameComponent bottomCount (stepCap stateS position) firstIndex secondIndex := by
  have windowT : position + 2 ≤ stateT.openWires.length := by
    rw [lengthEq]
    exact windowS
  have firstOldLt := capBoundaryReindex_lt_ofNewRange bottomCount stateS position firstIndex
    windowS firstInRange
  have secondOldLt := capBoundaryReindex_lt_ofNewRange bottomCount stateS position secondIndex
    windowS secondInRange
  have legFirstLt : bottomCount + position < bottomCount + stateS.openWires.length :=
    Nat.add_lt_add_left
      (Nat.lt_of_lt_of_le
        (Nat.lt_of_lt_of_le (Nat.lt_succ_self position) (Nat.le_succ (position + 1)))
        windowS)
      bottomCount
  have legSecondLt : bottomCount + (position + 1) < bottomCount + stateS.openWires.length :=
    Nat.add_lt_add_left (Nat.lt_of_lt_of_le (Nat.lt_succ_self (position + 1)) windowS)
      bottomCount
  show isSameComponent (stepCap stateT position).links
      (natListGetAt (matchingBoundaryNodes bottomCount (stepCap stateT position)) firstIndex)
      (natListGetAt (matchingBoundaryNodes bottomCount (stepCap stateT position)) secondIndex)
    = isSameComponent (stepCap stateS position).links
      (natListGetAt (matchingBoundaryNodes bottomCount (stepCap stateS position)) firstIndex)
      (natListGetAt (matchingBoundaryNodes bottomCount (stepCap stateS position)) secondIndex)
  rw [matchingBoundaryNodes_stepCap_getAt_reindex bottomCount stateT position firstIndex
      windowT,
    matchingBoundaryNodes_stepCap_getAt_reindex bottomCount stateT position secondIndex
      windowT,
    matchingBoundaryNodes_stepCap_getAt_reindex bottomCount stateS position firstIndex
      windowS,
    matchingBoundaryNodes_stepCap_getAt_reindex bottomCount stateS position secondIndex
      windowS,
    stepCap_links_eq_unionFindJoin_boundaryReads bottomCount stateT position,
    stepCap_links_eq_unionFindJoin_boundaryReads bottomCount stateS position,
    isSameComponent_unionFindJoin stateT.links forestT,
    isSameComponent_unionFindJoin stateS.links forestS]
  have atomProbes : isSameComponent stateT.links
        (natListGetAt (matchingBoundaryNodes bottomCount stateT)
          (capBoundaryReindex bottomCount position firstIndex))
        (natListGetAt (matchingBoundaryNodes bottomCount stateT)
          (capBoundaryReindex bottomCount position secondIndex))
      = isSameComponent stateS.links
        (natListGetAt (matchingBoundaryNodes bottomCount stateS)
          (capBoundaryReindex bottomCount position firstIndex))
        (natListGetAt (matchingBoundaryNodes bottomCount stateS)
          (capBoundaryReindex bottomCount position secondIndex)) :=
    viewAgrees _ _ firstOldLt secondOldLt
  have atomLegFirst : isSameComponent stateT.links
        (natListGetAt (matchingBoundaryNodes bottomCount stateT) (bottomCount + position))
        (natListGetAt (matchingBoundaryNodes bottomCount stateT)
          (capBoundaryReindex bottomCount position firstIndex))
      = isSameComponent stateS.links
        (natListGetAt (matchingBoundaryNodes bottomCount stateS) (bottomCount + position))
        (natListGetAt (matchingBoundaryNodes bottomCount stateS)
          (capBoundaryReindex bottomCount position firstIndex)) :=
    viewAgrees _ _ legFirstLt firstOldLt
  have atomLegSecond : isSameComponent stateT.links
        (natListGetAt (matchingBoundaryNodes bottomCount stateT)
          (bottomCount + (position + 1)))
        (natListGetAt (matchingBoundaryNodes bottomCount stateT)
          (capBoundaryReindex bottomCount position secondIndex))
      = isSameComponent stateS.links
        (natListGetAt (matchingBoundaryNodes bottomCount stateS)
          (bottomCount + (position + 1)))
        (natListGetAt (matchingBoundaryNodes bottomCount stateS)
          (capBoundaryReindex bottomCount position secondIndex)) :=
    viewAgrees _ _ legSecondLt secondOldLt
  have atomCrossFirst : isSameComponent stateT.links
        (natListGetAt (matchingBoundaryNodes bottomCount stateT) (bottomCount + position))
        (natListGetAt (matchingBoundaryNodes bottomCount stateT)
          (capBoundaryReindex bottomCount position secondIndex))
      = isSameComponent stateS.links
        (natListGetAt (matchingBoundaryNodes bottomCount stateS) (bottomCount + position))
        (natListGetAt (matchingBoundaryNodes bottomCount stateS)
          (capBoundaryReindex bottomCount position secondIndex)) :=
    viewAgrees _ _ legFirstLt secondOldLt
  have atomCrossSecond : isSameComponent stateT.links
        (natListGetAt (matchingBoundaryNodes bottomCount stateT)
          (capBoundaryReindex bottomCount position firstIndex))
        (natListGetAt (matchingBoundaryNodes bottomCount stateT)
          (bottomCount + (position + 1)))
      = isSameComponent stateS.links
        (natListGetAt (matchingBoundaryNodes bottomCount stateS)
          (capBoundaryReindex bottomCount position firstIndex))
        (natListGetAt (matchingBoundaryNodes bottomCount stateS)
          (bottomCount + (position + 1))) :=
    viewAgrees _ _ firstOldLt legSecondLt
  rw [atomProbes, atomLegFirst, atomLegSecond, atomCrossFirst, atomCrossSecond]

/-- **Loop counts stay equal under a cap**: each side increments by its own view's boolean at
the window, the window indices are in range, and the view agreement equates the increments. -/
theorem matchingViewLoops_stepCap (bottomCount : Nat) (stateS stateT : WireState)
    (position : Nat) (windowS : position + 2 ≤ stateS.openWires.length)
    (loopsEq : stateT.loops = stateS.loops)
    (viewAgrees : ∀ firstIndex secondIndex,
      firstIndex < bottomCount + stateS.openWires.length →
      secondIndex < bottomCount + stateS.openWires.length →
      matchingSameComponent bottomCount stateT firstIndex secondIndex
        = matchingSameComponent bottomCount stateS firstIndex secondIndex) :
    (stepCap stateT position).loops = (stepCap stateS position).loops := by
  have legFirstLt : bottomCount + position < bottomCount + stateS.openWires.length :=
    Nat.add_lt_add_left
      (Nat.lt_of_lt_of_le
        (Nat.lt_of_lt_of_le (Nat.lt_succ_self position) (Nat.le_succ (position + 1)))
        windowS)
      bottomCount
  have legSecondLt : bottomCount + (position + 1) < bottomCount + stateS.openWires.length :=
    Nat.add_lt_add_left (Nat.lt_of_lt_of_le (Nat.lt_succ_self (position + 1)) windowS)
      bottomCount
  rw [stepCap_loops_eq_addViewIncrement bottomCount stateT position,
    stepCap_loops_eq_addViewIncrement bottomCount stateS position, loopsEq,
    viewAgrees (bottomCount + position) (bottomCount + (position + 1)) legFirstLt legSecondLt]

/-- **Open-wire counts stay equal under a cap** (additive bookkeeping; the cancellation is two
`Nat.succ.inj` applications — core `Nat.add_right_cancel` leaks `propext`). -/
theorem matchingViewLength_stepCap (stateS stateT : WireState) (position : Nat)
    (windowS : position + 2 ≤ stateS.openWires.length)
    (lengthEq : stateT.openWires.length = stateS.openWires.length) :
    (stepCap stateT position).openWires.length
      = (stepCap stateS position).openWires.length := by
  have windowT : position + 2 ≤ stateT.openWires.length := by
    rw [lengthEq]
    exact windowS
  have combined : (stepCap stateT position).openWires.length + 2
      = (stepCap stateS position).openWires.length + 2 :=
    ((stepCap_openWiresLength stateT position windowT).trans lengthEq).trans
      (stepCap_openWiresLength stateS position windowS).symm
  exact Nat.succ.inj (Nat.succ.inj combined)

/-! ## Honesty marker -/

/-- **Honesty marker — the connectivity view's CAP stability is SHIPPED.**  The three cap-arm
transports of the view data: in-range view agreement is preserved
(`matchingViewAgrees_stepCap`, via the state-independent reindex factoring + the unconditional
join legs + the flat-disjunction characterization reducing to five in-range pre-cap atoms), loop
counts stay equal (the increment IS the view boolean at the window), and open-wire counts stay
equal.  NOT yet covered: the CUP arm (fresh-leg isolation makes the spliced pair a fresh
component; the old atoms survive untouched), the bundled view-sim structure + the fold over a
disciplined atom list, and the run-composition law behind the `MatchingSaturatedCongruence`
fields — the remaining MODE3-C bricks.  `= true`. -/
def fxMode_hasMatchingViewCapStability : Bool := true

end FX1Poly.Polygraph
