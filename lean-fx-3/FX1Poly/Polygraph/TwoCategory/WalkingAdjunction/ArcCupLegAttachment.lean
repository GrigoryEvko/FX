import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusCupHeadFolded
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingComponentAlgebra

/-! # ArcCupLegAttachment — the leg separation forced by a fused witness (peel campaign H, cup rung 4 opener)

The cup partner-list dispatch needs three facts about the FRESH run's window legs (the fresh
bottom ports at the window indices, whose reads are the leg nodes themselves).  First, a
FUSED witness — any non-leg boundary index whose read shares a leg's component — forces the
two legs DISCONNECTED in the fresh links: were they connected, the witness and the two leg
indices would be three pairwise-distinct same-component boundary tokens, violating the
census.  Second and third, once the legs are separate, no index reaching one leg's component
can BE the other leg — the leg-exclusion corollaries the rewiring targets dispatch with.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private plumbing (per-file copies, following the codebase pattern) -/

private theorem rangeLoopLength : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLength count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length
        = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1,
        Nat.add_right_comm count accumulated.length 1]

private theorem rangeLength (count : Nat) : (List.range count).length = count :=
  rangeLoopLength count []

private theorem rangeLoopGetAt_past : (count : Nat) → (accumulated : List Nat) →
    (offset : Nat) →
    natListGetAt (List.range.loop count accumulated) (offset + count)
      = natListGetAt accumulated offset
  | 0, _, _ => rfl
  | count + 1, accumulated, offset => by
      have inner := rangeLoopGetAt_past count (count :: accumulated) (offset + 1)
      rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
      exact inner

private theorem rangeLoopGetAt_below : (count : Nat) → (accumulated : List Nat) →
    (index : Nat) → index < count →
    natListGetAt (List.range.loop count accumulated) index = index
  | 0, _, _, indexBelow => absurd indexBelow (Nat.not_succ_le_zero _)
  | count + 1, accumulated, index, indexBelow => by
      cases Nat.lt_or_ge index count with
      | inl below => exact rangeLoopGetAt_below count (count :: accumulated) index below
      | inr atLeast =>
          have indexEq : index = count :=
            Nat.le_antisymm (Nat.le_of_succ_le_succ indexBelow) atLeast
          have pastRead := rangeLoopGetAt_past count (count :: accumulated) 0
          rw [Nat.zero_add count] at pastRead
          rw [indexEq]
          exact pastRead

private theorem rangeGetAt_below (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  rangeLoopGetAt_below count [] index indexBelow

/-! ## The bottom-port read -/

/-- **A bottom-port boundary read is the port itself**: reading a range-prefixed boundary
below the range block returns the index. -/
theorem natListGetAt_rangeAppend_below (count : Nat) (wires : List Nat) (index : Nat)
    (indexBelow : index < count) :
    natListGetAt (List.range count ++ wires) index = index := by
  have indexInBlock : index < (List.range count).length := by
    rw [rangeLength count]
    exact indexBelow
  exact (natListGetAt_append_inside (List.range count) wires index indexInBlock).trans
    (rangeGetAt_below count index indexBelow)

/-! ## A fused witness forces the legs disconnected -/

/-- ★ **A left-fused witness separates the legs**: if some non-leg boundary index of the
FRESH run reads into the LEFT leg's component, the two window legs are NOT same-component —
were they connected, the witness and both leg indices would be three pairwise-distinct
same-component boundary tokens, violating the census. -/
theorem arcFreshLegsDisconnected_ofFusedWitness
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat)
    (windowFits : windowPosition ≤ bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained (bottomCount + 2) atoms)
    (witnessIndex : Nat)
    (witnessInRange : witnessIndex
      < bottomCount + 2
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length)
    (witnessNeLeft : witnessIndex ≠ windowPosition)
    (witnessNeRight : witnessIndex ≠ windowPosition + 1)
    (witnessReachesLeftLeg : isSameComponent
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links windowPosition
      (natListGetAt
        (List.range (bottomCount + 2)
          ++ (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).openWires)
        witnessIndex) = true) :
    isSameComponent
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links windowPosition (windowPosition + 1) = false := by
  cases legsTest : isSameComponent
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links windowPosition (windowPosition + 1) with
  | false => rfl
  | true =>
      have readAtLeft : natListGetAt
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
      have readAtRight : natListGetAt
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
      have witnessToLeft : isSameComponent
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).links
          (natListGetAt
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires)
            witnessIndex) windowPosition = true :=
        (isSameComponent_symm
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).links
          (natListGetAt
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires)
            witnessIndex) windowPosition).trans witnessReachesLeftLeg
      have witnessToRead12 : isSameComponent
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).links
          (natListGetAt
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires)
            witnessIndex)
          (natListGetAt
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires)
            windowPosition) = true := by
        rw [readAtLeft]
        exact witnessToLeft
      have witnessToRead13 : isSameComponent
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).links
          (natListGetAt
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires)
            witnessIndex)
          (natListGetAt
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires)
            (windowPosition + 1)) = true := by
        rw [readAtRight]
        exact decide_eq_true ((of_decide_eq_true witnessToLeft).trans
          (of_decide_eq_true legsTest))
      exact False.elim (arcBoundaryCensus_boundaryNodes (bottomCount + 2)
        (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms)
        (arcBoundaryCensus_ofChainedSpineList (bottomCount + 2) atoms chained)
        witnessIndex windowPosition (windowPosition + 1)
        witnessInRange
        (Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_succ_of_le windowFits))
          (Nat.le_add_right (bottomCount + 2)
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).openWires.length))
        (Nat.lt_of_lt_of_le (Nat.succ_lt_succ (Nat.lt_succ_of_le windowFits))
          (Nat.le_add_right (bottomCount + 2)
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).openWires.length))
        (fun witnessEqLeft => witnessNeLeft witnessEqLeft)
        (fun witnessEqRight => witnessNeRight witnessEqRight)
        (fun legsEq => Nat.lt_irrefl windowPosition
          (Nat.lt_of_lt_of_le (Nat.lt_succ_self windowPosition)
            (Nat.le_of_eq legsEq.symm)))
        witnessToRead12 witnessToRead13)

/-- ★ **A right-fused witness separates the legs** — the mirror: a non-leg boundary index
reading into the RIGHT leg's component forces the legs disconnected. -/
theorem arcFreshLegsDisconnected_ofFusedWitnessRight
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat)
    (windowFits : windowPosition ≤ bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained (bottomCount + 2) atoms)
    (witnessIndex : Nat)
    (witnessInRange : witnessIndex
      < bottomCount + 2
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length)
    (witnessNeLeft : witnessIndex ≠ windowPosition)
    (witnessNeRight : witnessIndex ≠ windowPosition + 1)
    (witnessReachesRightLeg : isSameComponent
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links (windowPosition + 1)
      (natListGetAt
        (List.range (bottomCount + 2)
          ++ (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).openWires)
        witnessIndex) = true) :
    isSameComponent
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links windowPosition (windowPosition + 1) = false := by
  cases legsTest : isSameComponent
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links windowPosition (windowPosition + 1) with
  | false => rfl
  | true =>
      have readAtLeft : natListGetAt
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
      have readAtRight : natListGetAt
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
      have witnessToRight : isSameComponent
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).links
          (natListGetAt
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires)
            witnessIndex) (windowPosition + 1) = true :=
        (isSameComponent_symm
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).links
          (natListGetAt
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires)
            witnessIndex) (windowPosition + 1)).trans witnessReachesRightLeg
      have witnessToRead12 : isSameComponent
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).links
          (natListGetAt
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires)
            witnessIndex)
          (natListGetAt
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires)
            windowPosition) = true := by
        rw [readAtLeft]
        exact decide_eq_true ((of_decide_eq_true witnessToRight).trans
          (of_decide_eq_true legsTest).symm)
      have witnessToRead13 : isSameComponent
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).links
          (natListGetAt
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires)
            witnessIndex)
          (natListGetAt
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] []) atoms).openWires)
            (windowPosition + 1)) = true := by
        rw [readAtRight]
        exact witnessToRight
      exact False.elim (arcBoundaryCensus_boundaryNodes (bottomCount + 2)
        (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms)
        (arcBoundaryCensus_ofChainedSpineList (bottomCount + 2) atoms chained)
        witnessIndex windowPosition (windowPosition + 1)
        witnessInRange
        (Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_succ_of_le windowFits))
          (Nat.le_add_right (bottomCount + 2)
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).openWires.length))
        (Nat.lt_of_lt_of_le (Nat.succ_lt_succ (Nat.lt_succ_of_le windowFits))
          (Nat.le_add_right (bottomCount + 2)
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms).openWires.length))
        (fun witnessEqLeft => witnessNeLeft witnessEqLeft)
        (fun witnessEqRight => witnessNeRight witnessEqRight)
        (fun legsEq => Nat.lt_irrefl windowPosition
          (Nat.lt_of_lt_of_le (Nat.lt_succ_self windowPosition)
            (Nat.le_of_eq legsEq.symm)))
        witnessToRead12 witnessToRead13)

/-! ## The leg-exclusion corollaries -/

/-- **Reaching the right leg's component excludes being the left leg**: over separated legs,
a boundary index whose read shares the RIGHT leg's component cannot be the left window
index — its read there would be the left leg node, connecting the legs. -/
theorem arcLegReach_neOppositeLeg (links : List (Nat × Nat)) (portCount : Nat)
    (wires : List Nat) (windowPosition : Nat)
    (leftLegBelow : windowPosition < portCount)
    (legsDisconnected : isSameComponent links windowPosition (windowPosition + 1) = false)
    (reachIndex : Nat)
    (reachesRightLeg : isSameComponent links (windowPosition + 1)
      (natListGetAt (List.range portCount ++ wires) reachIndex) = true) :
    reachIndex ≠ windowPosition :=
  fun reachEqLeft => by
    rw [reachEqLeft,
      natListGetAt_rangeAppend_below portCount wires windowPosition leftLegBelow]
      at reachesRightLeg
    exact Bool.noConfusion (legsDisconnected.symm.trans
      ((isSameComponent_symm links windowPosition (windowPosition + 1)).trans
        reachesRightLeg))

/-- **Reaching the left leg's component excludes being the right leg** — the mirror. -/
theorem arcLegReach_neRightLeg (links : List (Nat × Nat)) (portCount : Nat)
    (wires : List Nat) (windowPosition : Nat)
    (rightLegBelow : windowPosition + 1 < portCount)
    (legsDisconnected : isSameComponent links windowPosition (windowPosition + 1) = false)
    (reachIndex : Nat)
    (reachesLeftLeg : isSameComponent links windowPosition
      (natListGetAt (List.range portCount ++ wires) reachIndex) = true) :
    reachIndex ≠ windowPosition + 1 :=
  fun reachEqRight => by
    rw [reachEqRight,
      natListGetAt_rangeAppend_below portCount wires (windowPosition + 1) rightLegBelow]
      at reachesLeftLeg
    exact Bool.noConfusion (legsDisconnected.symm.trans reachesLeftLeg)

/-- **Honesty marker — the leg-attachment separation kit is SHIPPED (peel campaign H, cup
rung 4 opener).**  The bottom-port read (`natListGetAt_rangeAppend_below`), the
census-powered leg separation from a fused witness on either leg
(`arcFreshLegsDisconnected_ofFusedWitness` / `...Right`), and the leg-exclusion corollaries
(`arcLegReach_neOppositeLeg` / `arcLegReach_neRightLeg`).  What this marker does NOT claim:
the leg-attachment partner witnesses from the fresh scan, the assembled cup partner list,
and the cup diagram leg.  `= true`. -/
def fxMode_hasArcCupLegAttachment : Bool := true

end FX1Poly.Polygraph
