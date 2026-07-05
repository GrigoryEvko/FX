import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcLoopFreedom
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapSeedClosure

/-! # ArcCapHeadLoops — the composite cap-head fold never closes a loop

The loops leg of the cap-head extract correspondence (peel campaign H, rung E-3, part 7).
The composite fold starts from the POST-CAP seed — the peeled cap has consumed the window
pair into a closed three-node component (left wire, right wire, event node) — and the loop
counter stands at zero there: at empty links the consumed pair was never same-component.
The whole-fold constancy then rides the disciplined-fold machinery, with the post-cap
seed's typed-ends discipline holding VACUOUSLY: every surviving open wire reads a range
value off the closed strand, and the seed links separate every off-strand pair, so no two
open wires are ever same-component at the seed.

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

/-- A strict inequality separates its endpoints, smaller side first. -/
private theorem neOfLtLeft {smaller larger : Nat} (isSmaller : smaller < larger) :
    smaller ≠ larger :=
  fun valuesEqual =>
    Nat.lt_irrefl smaller (Nat.lt_of_lt_of_le isSmaller (Nat.le_of_eq valuesEqual.symm))

/-- A strict inequality separates its endpoints, larger side first. -/
private theorem neOfLtRight {smaller larger : Nat} (isSmaller : smaller < larger) :
    larger ≠ smaller :=
  fun valuesEqual =>
    Nat.lt_irrefl smaller (Nat.lt_of_lt_of_le isSmaller (Nat.le_of_eq valuesEqual))

/-- **The cap-head seed links separate every off-strand pair**: two distinct values, each
off the consumed strand (not the left wire, not the event node), are never same-component
at the seed links — the seed's only merges are the consumed pair and its event node, and
the right-wire conjuncts of the join-query disjunction short-circuit on the left-wire
misses. -/
private theorem capSeedLinks_offStrandPairSeparate
    (bottomCount windowPosition firstValue secondValue : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (valuesDiffer : firstValue ≠ secondValue)
    (firstOffLeftWire : firstValue ≠ windowPosition)
    (secondOffLeftWire : secondValue ≠ windowPosition)
    (firstOffEvent : firstValue ≠ bottomCount)
    (secondOffEvent : secondValue ≠ bottomCount) :
    isSameComponent
      (unionFindJoin (unionFindJoin [] windowPosition (windowPosition + 1))
        bottomCount windowPosition)
      firstValue secondValue = false := by
  have leftWireBelowBoundary : windowPosition < bottomCount :=
    Nat.lt_of_lt_of_le
      (Nat.lt_trans (Nat.lt_succ_self windowPosition)
        (Nat.lt_succ_self (windowPosition + 1)))
      windowFits
  have baseFirstSecond : isSameComponent [] firstValue secondValue = false :=
    decide_eq_false valuesDiffer
  have baseLeftFirst : isSameComponent [] windowPosition firstValue = false :=
    decide_eq_false (fun leftHitsFirst => firstOffLeftWire leftHitsFirst.symm)
  have baseLeftSecond : isSameComponent [] windowPosition secondValue = false :=
    decide_eq_false (fun leftHitsSecond => secondOffLeftWire leftHitsSecond.symm)
  have baseEventFirst : isSameComponent [] bottomCount firstValue = false :=
    decide_eq_false (fun eventHitsFirst => firstOffEvent eventHitsFirst.symm)
  have baseEventSecond : isSameComponent [] bottomCount secondValue = false :=
    decide_eq_false (fun eventHitsSecond => secondOffEvent eventHitsSecond.symm)
  have baseLeftEvent : isSameComponent [] windowPosition bottomCount = false :=
    decide_eq_false (neOfLtLeft leftWireBelowBoundary)
  have innerFirstSecond : isSameComponent
      (unionFindJoin [] windowPosition (windowPosition + 1)) firstValue secondValue
      = false := by
    rw [isSameComponent_unionFindJoin [] isUnionFindForest_nil windowPosition
        (windowPosition + 1) firstValue secondValue,
      baseFirstSecond, baseLeftFirst, baseLeftSecond]
    exact rfl
  have innerEventFirst : isSameComponent
      (unionFindJoin [] windowPosition (windowPosition + 1)) bottomCount firstValue
      = false := by
    rw [isSameComponent_unionFindJoin [] isUnionFindForest_nil windowPosition
        (windowPosition + 1) bottomCount firstValue,
      baseEventFirst, baseLeftEvent, baseLeftFirst]
    exact rfl
  have innerEventSecond : isSameComponent
      (unionFindJoin [] windowPosition (windowPosition + 1)) bottomCount secondValue
      = false := by
    rw [isSameComponent_unionFindJoin [] isUnionFindForest_nil windowPosition
        (windowPosition + 1) bottomCount secondValue,
      baseEventSecond, baseLeftEvent, baseLeftSecond]
    exact rfl
  rw [isSameComponent_unionFindJoin
      (unionFindJoin [] windowPosition (windowPosition + 1))
      (isUnionFindForest_unionFindJoin [] windowPosition (windowPosition + 1)
        isUnionFindForest_nil)
      bottomCount windowPosition firstValue secondValue,
    innerFirstSecond, innerEventFirst, innerEventSecond]
  exact rfl

/-! ## The vacuous typed-ends discipline at the post-cap seed -/

/-- ★ **The post-cap seed satisfies the typed-ends discipline vacuously** (for ANY source
mode): every surviving open wire reads a below-boundary range value off the consumed
strand — below-window positions read themselves, at-or-past positions read two above — and
the seed links separate every such off-strand pair, so no same-component open pair
exists. -/
theorem arcOpenEndsDiscipline_capHeadSeed (sourceMode : AdjunctionMode)
    (bottomCount windowPosition : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount) :
    ArcOpenEndsDiscipline sourceMode
      (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        windowPosition) := by
  intro lowPosition highPosition lowLtHigh highInRange sameTrue
  have leftWireBelowBoundary : windowPosition < bottomCount :=
    Nat.lt_of_lt_of_le
      (Nat.lt_trans (Nat.lt_succ_self windowPosition)
        (Nat.lt_succ_self (windowPosition + 1)))
      windowFits
  have leftWireRead : natListGetAt (List.range bottomCount) windowPosition
      = windowPosition :=
    rangeGetAt_below bottomCount windowPosition leftWireBelowBoundary
  have rightWireRead : natListGetAt (List.range bottomCount) (windowPosition + 1)
      = windowPosition + 1 :=
    rangeGetAt_below bottomCount (windowPosition + 1) windowFits
  have windowFitsRange : windowPosition + 2 ≤ (List.range bottomCount).length := by
    rw [rangeLength]
    exact windowFits
  have removedShift : (natListRemoveTwoAt (List.range bottomCount)
        windowPosition).length + 2
      = bottomCount :=
    (natListRemoveTwoAt_length (List.range bottomCount) windowPosition
      windowFitsRange).trans (rangeLength bottomCount)
  have highInRemovedRange : highPosition
      < (natListRemoveTwoAt (List.range bottomCount) windowPosition).length :=
    highInRange
  have lowInRemovedRange : lowPosition
      < (natListRemoveTwoAt (List.range bottomCount) windowPosition).length :=
    Nat.lt_trans lowLtHigh highInRemovedRange
  cases Nat.lt_or_ge lowPosition windowPosition with
  | inl lowBelow =>
      have lowRead : natListGetAt
          (natListRemoveTwoAt (List.range bottomCount) windowPosition) lowPosition
          = lowPosition :=
        (natListGetAt_natListRemoveTwoAt_below (List.range bottomCount) windowPosition
            lowPosition lowBelow).trans
          (rangeGetAt_below bottomCount lowPosition
            (Nat.lt_trans lowBelow leftWireBelowBoundary))
      cases Nat.lt_or_ge highPosition windowPosition with
      | inl highBelow =>
          have highRead : natListGetAt
              (natListRemoveTwoAt (List.range bottomCount) windowPosition) highPosition
              = highPosition :=
            (natListGetAt_natListRemoveTwoAt_below (List.range bottomCount)
                windowPosition highPosition highBelow).trans
              (rangeGetAt_below bottomCount highPosition
                (Nat.lt_trans highBelow leftWireBelowBoundary))
          have sameFalse : isSameComponent
              (unionFindJoin
                (unionFindJoin [] (natListGetAt (List.range bottomCount) windowPosition)
                  (natListGetAt (List.range bottomCount) (windowPosition + 1)))
                bottomCount (natListGetAt (List.range bottomCount) windowPosition))
              (natListGetAt (natListRemoveTwoAt (List.range bottomCount) windowPosition)
                lowPosition)
              (natListGetAt (natListRemoveTwoAt (List.range bottomCount) windowPosition)
                highPosition)
              = false := by
            rw [leftWireRead, rightWireRead, lowRead, highRead]
            exact capSeedLinks_offStrandPairSeparate bottomCount windowPosition
              lowPosition highPosition windowFits (neOfLtLeft lowLtHigh)
              (neOfLtLeft lowBelow) (neOfLtLeft highBelow)
              (neOfLtLeft (Nat.lt_trans lowBelow leftWireBelowBoundary))
              (neOfLtLeft (Nat.lt_trans highBelow leftWireBelowBoundary))
          exact Bool.noConfusion (sameFalse.symm.trans sameTrue)
      | inr highAtOrPast =>
          obtain ⟨highOffset, highOffsetEq⟩ := Nat.le.dest highAtOrPast
          have highBoundShifted : windowPosition + highOffset
              < (natListRemoveTwoAt (List.range bottomCount) windowPosition).length := by
            rw [highOffsetEq]
            exact highInRemovedRange
          have highValueBelowBoundary : windowPosition + highOffset + 2 < bottomCount :=
            Nat.lt_of_lt_of_le
              (Nat.succ_lt_succ (Nat.succ_lt_succ highBoundShifted))
              (Nat.le_of_eq removedShift)
          have highRead : natListGetAt
              (natListRemoveTwoAt (List.range bottomCount) windowPosition) highPosition
              = windowPosition + highOffset + 2 := by
            rw [← highOffsetEq]
            exact (natListGetAt_natListRemoveTwoAt_pastPair (List.range bottomCount)
                windowPosition highOffset windowFitsRange).trans
              (rangeGetAt_below bottomCount (windowPosition + highOffset + 2)
                highValueBelowBoundary)
          have windowLtHighValue : windowPosition
              < windowPosition + highOffset + 2 :=
            Nat.lt_of_le_of_lt (Nat.le_add_right windowPosition highOffset)
              (Nat.lt_trans (Nat.lt_succ_self (windowPosition + highOffset))
                (Nat.lt_succ_self (windowPosition + highOffset + 1)))
          have sameFalse : isSameComponent
              (unionFindJoin
                (unionFindJoin [] (natListGetAt (List.range bottomCount) windowPosition)
                  (natListGetAt (List.range bottomCount) (windowPosition + 1)))
                bottomCount (natListGetAt (List.range bottomCount) windowPosition))
              (natListGetAt (natListRemoveTwoAt (List.range bottomCount) windowPosition)
                lowPosition)
              (natListGetAt (natListRemoveTwoAt (List.range bottomCount) windowPosition)
                highPosition)
              = false := by
            rw [leftWireRead, rightWireRead, lowRead, highRead]
            exact capSeedLinks_offStrandPairSeparate bottomCount windowPosition
              lowPosition (windowPosition + highOffset + 2) windowFits
              (neOfLtLeft (Nat.lt_trans lowBelow windowLtHighValue))
              (neOfLtLeft lowBelow)
              (neOfLtRight windowLtHighValue)
              (neOfLtLeft (Nat.lt_trans lowBelow leftWireBelowBoundary))
              (neOfLtLeft highValueBelowBoundary)
          exact Bool.noConfusion (sameFalse.symm.trans sameTrue)
  | inr lowAtOrPast =>
      obtain ⟨lowOffset, lowOffsetEq⟩ := Nat.le.dest lowAtOrPast
      have highAtOrPast : windowPosition ≤ highPosition :=
        Nat.le_trans lowAtOrPast (Nat.le_of_lt lowLtHigh)
      obtain ⟨highOffset, highOffsetEq⟩ := Nat.le.dest highAtOrPast
      have lowBoundShifted : windowPosition + lowOffset
          < (natListRemoveTwoAt (List.range bottomCount) windowPosition).length := by
        rw [lowOffsetEq]
        exact lowInRemovedRange
      have highBoundShifted : windowPosition + highOffset
          < (natListRemoveTwoAt (List.range bottomCount) windowPosition).length := by
        rw [highOffsetEq]
        exact highInRemovedRange
      have lowValueBelowBoundary : windowPosition + lowOffset + 2 < bottomCount :=
        Nat.lt_of_lt_of_le (Nat.succ_lt_succ (Nat.succ_lt_succ lowBoundShifted))
          (Nat.le_of_eq removedShift)
      have highValueBelowBoundary : windowPosition + highOffset + 2 < bottomCount :=
        Nat.lt_of_lt_of_le (Nat.succ_lt_succ (Nat.succ_lt_succ highBoundShifted))
          (Nat.le_of_eq removedShift)
      have lowRead : natListGetAt
          (natListRemoveTwoAt (List.range bottomCount) windowPosition) lowPosition
          = windowPosition + lowOffset + 2 := by
        rw [← lowOffsetEq]
        exact (natListGetAt_natListRemoveTwoAt_pastPair (List.range bottomCount)
            windowPosition lowOffset windowFitsRange).trans
          (rangeGetAt_below bottomCount (windowPosition + lowOffset + 2)
            lowValueBelowBoundary)
      have highRead : natListGetAt
          (natListRemoveTwoAt (List.range bottomCount) windowPosition) highPosition
          = windowPosition + highOffset + 2 := by
        rw [← highOffsetEq]
        exact (natListGetAt_natListRemoveTwoAt_pastPair (List.range bottomCount)
            windowPosition highOffset windowFitsRange).trans
          (rangeGetAt_below bottomCount (windowPosition + highOffset + 2)
            highValueBelowBoundary)
      have positionsLt : windowPosition + lowOffset < windowPosition + highOffset := by
        rw [lowOffsetEq, highOffsetEq]
        exact lowLtHigh
      have valuesLt : windowPosition + lowOffset + 2
          < windowPosition + highOffset + 2 :=
        Nat.succ_lt_succ (Nat.succ_lt_succ positionsLt)
      have windowLtLowValue : windowPosition < windowPosition + lowOffset + 2 :=
        Nat.lt_of_le_of_lt (Nat.le_add_right windowPosition lowOffset)
          (Nat.lt_trans (Nat.lt_succ_self (windowPosition + lowOffset))
            (Nat.lt_succ_self (windowPosition + lowOffset + 1)))
      have windowLtHighValue : windowPosition < windowPosition + highOffset + 2 :=
        Nat.lt_of_le_of_lt (Nat.le_add_right windowPosition highOffset)
          (Nat.lt_trans (Nat.lt_succ_self (windowPosition + highOffset))
            (Nat.lt_succ_self (windowPosition + highOffset + 1)))
      have sameFalse : isSameComponent
          (unionFindJoin
            (unionFindJoin [] (natListGetAt (List.range bottomCount) windowPosition)
              (natListGetAt (List.range bottomCount) (windowPosition + 1)))
            bottomCount (natListGetAt (List.range bottomCount) windowPosition))
          (natListGetAt (natListRemoveTwoAt (List.range bottomCount) windowPosition)
            lowPosition)
          (natListGetAt (natListRemoveTwoAt (List.range bottomCount) windowPosition)
            highPosition)
          = false := by
        rw [leftWireRead, rightWireRead, lowRead, highRead]
        exact capSeedLinks_offStrandPairSeparate bottomCount windowPosition
          (windowPosition + lowOffset + 2) (windowPosition + highOffset + 2) windowFits
          (neOfLtLeft valuesLt)
          (neOfLtRight windowLtLowValue)
          (neOfLtRight windowLtHighValue)
          (neOfLtLeft lowValueBelowBoundary)
          (neOfLtLeft highValueBelowBoundary)
      exact Bool.noConfusion (sameFalse.symm.trans sameTrue)

/-! ## The composite loops leg -/

/-- ★ **The composite cap-head fold never closes a loop**: the peeled cap's seed step
keeps the counter at zero (at empty links the consumed pair was never same-component), and
the chained fold over the remaining atoms keeps it end-to-end — the post-cap seed carries
the freshness, forest, boundary-tracking, and (vacuous) typed-ends discipline companions
the disciplined-fold constancy consumes. -/
theorem arcCapHeadFolded_loops_zero
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained tailBoundary atoms) :
    (processArcSpine
      (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        windowPosition) atoms).loops = 0 := by
  have leftWireBelowBoundary : windowPosition < bottomCount :=
    Nat.lt_of_lt_of_le
      (Nat.lt_trans (Nat.lt_succ_self windowPosition)
        (Nat.lt_succ_self (windowPosition + 1)))
      windowFits
  have windowFitsRange : windowPosition + 2 ≤ (List.range bottomCount).length := by
    rw [rangeLength]
    exact windowFits
  have seedTracks : (stepCapArc
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      windowPosition).openWires.length = tailBoundary := by
    show (natListRemoveTwoAt (List.range bottomCount) windowPosition).length
      = tailBoundary
    have removedShift : (natListRemoveTwoAt (List.range bottomCount)
          windowPosition).length + 2
        = tailBoundary + 2 :=
      ((natListRemoveTwoAt_length (List.range bottomCount) windowPosition
          windowFitsRange).trans (rangeLength bottomCount)).trans tailBoundaryFits.symm
    exact Nat.succ.inj (Nat.succ.inj removedShift)
  have foldKeepsLoops := processArcSpine_loops_ofChained atoms
    (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      windowPosition)
    tailBoundary
    (stepCapArc_arcStateFresh
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition
      (arcStateFresh_initial bottomCount))
    (isUnionFindForest_stepCapArc
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition
      isUnionFindForest_nil)
    seedTracks chained
    (arcOpenEndsDiscipline_capHeadSeed overallSource bottomCount windowPosition
      windowFits)
  have consumedWiresSeparate : isSameComponent []
      (natListGetAt (List.range bottomCount) windowPosition)
      (natListGetAt (List.range bottomCount) (windowPosition + 1)) = false := by
    rw [rangeGetAt_below bottomCount windowPosition leftWireBelowBoundary,
      rangeGetAt_below bottomCount (windowPosition + 1) windowFits]
    exact decide_eq_false (neOfLtLeft (Nat.lt_succ_self windowPosition))
  have seedLoops : (stepCapArc
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      windowPosition).loops = 0 := by
    show (if isSameComponent []
            (natListGetAt (List.range bottomCount) windowPosition)
            (natListGetAt (List.range bottomCount) (windowPosition + 1))
          then 0 + 1 else 0)
        = 0
    rw [consumedWiresSeparate]
    exact if_neg (fun falseEqTrue => Bool.noConfusion falseEqTrue)
  exact foldKeepsLoops.trans seedLoops

/-! ## Honesty marker -/

/-- **Honesty marker — the composite cap-head fold never closes a loop (peel campaign H,
rung E-3, part 7).**  `arcCapHeadFolded_loops_zero`: the post-cap seed's loop counter is
zero (the consumed pair was never same-component at empty links), the seed carries the
freshness / forest / tracking companions, its typed-ends discipline holds VACUOUSLY
(`arcOpenEndsDiscipline_capHeadSeed` — the seed links separate every off-strand open
pair), and the disciplined-fold constancy carries zero to the end state.  Together with
`arcFoldLoops_zero_ofChainedSpineList` this closes the loops leg of the cap-head
`DiagramType` correspondence: both extracts report zero.  What this marker does NOT
claim: the assembled `DiagramType` / `FullArcStructure` equality.  `= true`. -/
def fxMode_hasArcCapHeadLoopLeg : Bool := true

end FX1Poly.Polygraph
