import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcHeadReindex
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWindowLocality

/-! # ArcCupReindexValues — the cup-head reindexing's value zones

The seed component correspondence (the links leg of the head cancellation) reduces, through
the join-transport kit, to VALUE facts about the cup-head reindexing: what it reads in each
zone of the post-cup boundary, that every below-boundary value stays below the tail seed's
width, and that no probe ever hits the cup's event node.  This brick pins those zones:

  * below the window the reindexing is the identity (the untouched range prefix);
  * at the window it reads the two fresh legs `bottomCount`, `bottomCount + 1`;
  * past the window it shifts DOWN by the block width (the displaced range suffix);
  * at or above the tail boundary it translates up by the allocation delta (shipped earlier);
  * every below-boundary value is below `bottomCount + 2`, so the event node `bottomCount + 2`
    is never a reindex image — the absorption atom that kills the outer event join.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private range plumbing (per-file copy, following the codebase pattern) -/

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

private theorem rangeLength (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLength count []]
  exact Nat.add_zero count

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

/-! ## The below-width unfolding -/

/-- Below the composite boundary's width the reindexing IS the stored read — the generic
if-positive unfolding, complementing `arcHeadReindex_shiftsAboveLength`. -/
theorem arcHeadReindex_readsBelow (compositeWires : List Nat) (freshDelta identifier : Nat)
    (belowWidth : identifier < compositeWires.length) :
    arcHeadReindex compositeWires freshDelta identifier
      = natListGetAt compositeWires identifier :=
  if_pos belowWidth

/-! ## The cup-head zone reads -/

/-- **Zone I — below the window the cup-head reindexing is the identity**: the untouched
range prefix reads itself back. -/
theorem arcCupHeadReindex_belowWindow (bottomCount windowPosition probeIndex : Nat)
    (windowFits : windowPosition ≤ bottomCount) (belowWindow : probeIndex < windowPosition) :
    arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
      [bottomCount, bottomCount + 1]) 1 probeIndex = probeIndex :=
  (arcHeadReindex_readsBelow
      (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1 probeIndex
      (by
        rw [cupHeadOpenWires_length]
        exact Nat.lt_of_lt_of_le belowWindow
          (Nat.le_trans windowFits (Nat.le_add_right bottomCount 2)))).trans
    ((natListGetAt_natListInsertAt_below (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1] probeIndex belowWindow
        (by
          rw [rangeLength]
          exact Nat.lt_of_lt_of_le belowWindow windowFits)).trans
      (rangeGetAt_below bottomCount probeIndex
        (Nat.lt_of_lt_of_le belowWindow windowFits)))

/-- **Zone II left — the window position reads the cup's LEFT leg** `bottomCount`. -/
theorem arcCupHeadReindex_leftLeg (bottomCount windowPosition : Nat)
    (windowFits : windowPosition ≤ bottomCount) :
    arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
      [bottomCount, bottomCount + 1]) 1 windowPosition = bottomCount :=
  (arcHeadReindex_readsBelow
      (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1 windowPosition
      (by
        rw [cupHeadOpenWires_length]
        exact Nat.lt_of_le_of_lt windowFits
          (Nat.lt_succ_of_lt (Nat.lt_succ_self bottomCount)))).trans
    (natListGetAt_natListInsertAt_inside (List.range bottomCount) windowPosition
      [bottomCount, bottomCount + 1] 0 (Nat.zero_lt_succ 1)
      (by
        rw [rangeLength]
        exact windowFits))

/-- **Zone II right — the window's successor reads the cup's RIGHT leg** `bottomCount + 1`. -/
theorem arcCupHeadReindex_rightLeg (bottomCount windowPosition : Nat)
    (windowFits : windowPosition ≤ bottomCount) :
    arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
      [bottomCount, bottomCount + 1]) 1 (windowPosition + 1) = bottomCount + 1 :=
  (arcHeadReindex_readsBelow
      (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1 (windowPosition + 1)
      (by
        rw [cupHeadOpenWires_length]
        exact Nat.succ_lt_succ (Nat.lt_succ_of_le windowFits))).trans
    (natListGetAt_natListInsertAt_inside (List.range bottomCount) windowPosition
      [bottomCount, bottomCount + 1] 1 (Nat.le_refl 2)
      (by
        rw [rangeLength]
        exact windowFits))

/-- **Zone III — past the window the cup-head reindexing shifts DOWN by two**: the displaced
range suffix reads its original range value. -/
theorem arcCupHeadReindex_pastWindow (bottomCount windowPosition pastOffset : Nat)
    (pastBound : windowPosition + pastOffset < bottomCount) :
    arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
      [bottomCount, bottomCount + 1]) 1 (windowPosition + pastOffset + 2)
      = windowPosition + pastOffset :=
  (arcHeadReindex_readsBelow
      (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1 (windowPosition + pastOffset + 2)
      (by
        rw [cupHeadOpenWires_length]
        exact Nat.succ_lt_succ (Nat.succ_lt_succ pastBound))).trans
    ((natListGetAt_natListInsertAt_pastBlock (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1] pastOffset
        (by
          rw [rangeLength]
          exact Nat.le_of_lt (Nat.lt_of_le_of_lt
            (Nat.le_add_right windowPosition pastOffset) pastBound))).trans
      (rangeGetAt_below bottomCount (windowPosition + pastOffset) pastBound))

/-! ## The value bound and the event-node avoidance -/

/-- **Every below-boundary probe's value stays below the tail seed's width** — the range
prefix and displaced suffix read below `bottomCount`, the two legs read `bottomCount` and
`bottomCount + 1`.  Four-zone trichotomy on the probe. -/
theorem arcCupHeadReindex_valueBelowBoundary (bottomCount windowPosition probeIndex : Nat)
    (windowFits : windowPosition ≤ bottomCount) (probeBelow : probeIndex < bottomCount + 2) :
    arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
      [bottomCount, bottomCount + 1]) 1 probeIndex < bottomCount + 2 := by
  cases Nat.lt_or_ge probeIndex windowPosition with
  | inl belowWindow =>
      rw [arcCupHeadReindex_belowWindow bottomCount windowPosition probeIndex windowFits
        belowWindow]
      exact Nat.lt_of_lt_of_le belowWindow
        (Nat.le_trans windowFits (Nat.le_add_right bottomCount 2))
  | inr atWindowOrPast =>
      cases Nat.lt_or_ge probeIndex (windowPosition + 1) with
      | inl belowSucc =>
          have probeIsWindow : probeIndex = windowPosition :=
            Nat.le_antisymm (Nat.le_of_succ_le_succ belowSucc) atWindowOrPast
          rw [probeIsWindow,
            arcCupHeadReindex_leftLeg bottomCount windowPosition windowFits]
          exact Nat.lt_succ_of_lt (Nat.lt_succ_self bottomCount)
      | inr atLeastSucc =>
          cases Nat.lt_or_ge probeIndex (windowPosition + 2) with
          | inl belowTwo =>
              have probeIsRight : probeIndex = windowPosition + 1 :=
                Nat.le_antisymm (Nat.le_of_succ_le_succ belowTwo) atLeastSucc
              rw [probeIsRight,
                arcCupHeadReindex_rightLeg bottomCount windowPosition windowFits]
              exact Nat.succ_lt_succ (Nat.lt_succ_self bottomCount)
          | inr pastWindow =>
              obtain ⟨pastOffset, offsetSpec⟩ := Nat.le.dest pastWindow
              have indexForm : windowPosition + pastOffset + 2 = probeIndex := by
                rw [Nat.add_right_comm windowPosition pastOffset 2]
                exact offsetSpec
              have pastBound : windowPosition + pastOffset < bottomCount := by
                have shifted : windowPosition + pastOffset + 2 < bottomCount + 2 := by
                  rw [indexForm]
                  exact probeBelow
                exact Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ shifted)
              rw [← indexForm,
                arcCupHeadReindex_pastWindow bottomCount windowPosition pastOffset pastBound]
              exact Nat.lt_of_lt_of_le pastBound (Nat.le_add_right bottomCount 2)

/-- ★ **No probe ever reads the cup's event node** `bottomCount + 2`: below-boundary values
stay below it, above-boundary values translate past it.  The absorption atom that removes the
outer event join from the seed component correspondence. -/
theorem arcCupHeadReindex_missesEventNode (bottomCount windowPosition probeIndex : Nat)
    (windowFits : windowPosition ≤ bottomCount) :
    (bottomCount + 2 == arcHeadReindex (natListInsertAt (List.range bottomCount)
      windowPosition [bottomCount, bottomCount + 1]) 1 probeIndex) = false := by
  cases Nat.lt_or_ge probeIndex (bottomCount + 2) with
  | inl probeBelow =>
      have valueBelow := arcCupHeadReindex_valueBelowBoundary bottomCount windowPosition
        probeIndex windowFits probeBelow
      exact decide_eq_false (fun eventHit =>
        Nat.lt_irrefl (bottomCount + 2)
          (Nat.lt_of_le_of_lt (Nat.le_of_eq eventHit) valueBelow))
  | inr probeAtLeast =>
      rw [arcHeadReindex_cupSeedShifts bottomCount windowPosition probeIndex probeAtLeast]
      exact decide_eq_false (fun eventHit =>
        have probeIsBelow : probeIndex = bottomCount + 1 := Nat.succ.inj eventHit.symm
        Nat.lt_irrefl (bottomCount + 1)
          (Nat.lt_of_lt_of_le (Nat.lt_succ_self (bottomCount + 1))
            (Nat.le_trans probeAtLeast (Nat.le_of_eq probeIsBelow))))

/-! ## Honesty marker -/

/-- **Honesty marker — the cup-head reindexing's value zones (peel campaign H, seed rung,
LINKS-leg atoms, part 1).**  The below-width unfolding, the four zone reads (identity prefix,
the two legs, the shifted suffix), the below-boundary value bound, and the event-node
avoidance atom.  What this marker does NOT claim: the reindexing's injectivity atom
(`(sigma p == sigma q) = (p == q)`, via the value-recovery left inverse), the assembled seed
`ArcComponentShiftCorr` at the cup head, and the cap-head analogues.  `= true`. -/
def fxMode_hasArcCupHeadReindexValues : Bool := true

end FX1Poly.Polygraph
