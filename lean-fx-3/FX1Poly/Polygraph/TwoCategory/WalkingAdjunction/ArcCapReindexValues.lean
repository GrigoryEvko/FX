import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupReindexValues

/-! # ArcCapReindexValues — the cap-head reindexing's value zones

The cap-head mirror of the cup value zones: firing the peeled CAP at the canonical seed
consumes the window pair, so the cap-head reindexing (over the two-narrower wire list, with
allocation delta `3`) reads

  * below the window: the identity (the untouched range prefix);
  * past the window: UP by two (the displaced range suffix — the removal's complement);
  * at or above the tail boundary: up by three (shipped earlier as the seed translation).

The three zones' values are `[0, windowPosition)`, `[windowPosition + 2, bottomCount)`, and
`[bottomCount + 1, ...)` — all avoiding the cap component `{windowPosition,
windowPosition + 1, bottomCount}`.  This brick ships the two avoidance atoms the cap seed
correspondence consumes: no reindexed probe hits the LEFT WIRE `windowPosition` (the joined
legs' anchor) and none hits the EVENT NODE `bottomCount`.

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

/-! ## The cap-head zone reads -/

/-- **Zone I — below the window the cap-head reindexing is the identity**: the untouched
range prefix reads itself back. -/
theorem arcCapHeadReindex_belowWindow
    (bottomCount windowPosition tailBoundary probeIndex : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (belowWindow : probeIndex < windowPosition) :
    arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3 probeIndex
      = probeIndex := by
  have windowLeTail : windowPosition ≤ tailBoundary :=
    Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ
      (Nat.le_trans windowFits (Nat.le_of_eq tailBoundaryFits.symm)))
  exact (arcHeadReindex_readsBelow
      (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3 probeIndex
      (by
        rw [capHeadOpenWires_length bottomCount windowPosition tailBoundary windowFits
          tailBoundaryFits]
        exact Nat.lt_of_lt_of_le belowWindow windowLeTail)).trans
    ((natListGetAt_natListRemoveTwoAt_below (List.range bottomCount) windowPosition
        probeIndex belowWindow).trans
      (rangeGetAt_below bottomCount probeIndex
        (Nat.lt_of_lt_of_le belowWindow
          (Nat.le_trans (Nat.le_add_right windowPosition 2) windowFits))))

/-- **Zone II — past the window the cap-head reindexing shifts UP by two**: the displaced
range suffix reads its pre-removal position. -/
theorem arcCapHeadReindex_pastWindow
    (bottomCount windowPosition tailBoundary pastOffset : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (pastBound : windowPosition + pastOffset < tailBoundary) :
    arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
      (windowPosition + pastOffset) = windowPosition + pastOffset + 2 :=
  (arcHeadReindex_readsBelow
      (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
      (windowPosition + pastOffset)
      (by
        rw [capHeadOpenWires_length bottomCount windowPosition tailBoundary windowFits
          tailBoundaryFits]
        exact pastBound)).trans
    ((natListGetAt_natListRemoveTwoAt_pastPair (List.range bottomCount) windowPosition
        pastOffset
        (by
          rw [rangeLength]
          exact windowFits)).trans
      (rangeGetAt_below bottomCount (windowPosition + pastOffset + 2)
        (Nat.lt_of_lt_of_le (Nat.succ_lt_succ (Nat.succ_lt_succ pastBound))
          (Nat.le_of_eq tailBoundaryFits))))

/-! ## The component-avoidance atoms -/

/-- ★ **No reindexed probe hits the left wire `windowPosition`** — zone I values stay
strictly below it, zone II values sit at least two above it, zone III values sit past the
whole boundary. -/
theorem arcCapHeadReindex_missesLeftWire
    (bottomCount windowPosition tailBoundary probeIndex : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount) :
    (windowPosition == arcHeadReindex
      (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3 probeIndex) = false := by
  cases Nat.lt_or_ge probeIndex windowPosition with
  | inl belowWindow =>
      rw [arcCapHeadReindex_belowWindow bottomCount windowPosition tailBoundary probeIndex
        windowFits tailBoundaryFits belowWindow]
      exact decide_eq_false (fun windowHitsProbe => Nat.lt_irrefl windowPosition
        (Nat.lt_of_le_of_lt (Nat.le_of_eq windowHitsProbe) belowWindow))
  | inr atWindow =>
      cases Nat.lt_or_ge probeIndex tailBoundary with
      | inl belowTail =>
          obtain ⟨pastOffset, offsetSpec⟩ := Nat.le.dest atWindow
          have pastBound : windowPosition + pastOffset < tailBoundary := by
            rw [offsetSpec]
            exact belowTail
          rw [← offsetSpec,
            arcCapHeadReindex_pastWindow bottomCount windowPosition tailBoundary pastOffset
              windowFits tailBoundaryFits pastBound]
          exact decide_eq_false (fun windowHitsValue => Nat.lt_irrefl windowPosition
            (Nat.lt_of_lt_of_le
              (Nat.lt_of_le_of_lt (Nat.le_add_right windowPosition pastOffset)
                (Nat.lt_of_lt_of_le (Nat.lt_succ_self (windowPosition + pastOffset))
                  (Nat.le_succ (windowPosition + pastOffset + 1))))
              (Nat.le_of_eq windowHitsValue.symm)))
      | inr atTail =>
          rw [arcHeadReindex_capSeedShifts bottomCount windowPosition tailBoundary
            windowFits tailBoundaryFits probeIndex atTail]
          exact decide_eq_false (fun windowHitsShifted => Nat.lt_irrefl windowPosition
            (Nat.lt_of_lt_of_le
              (Nat.lt_of_lt_of_le
                (Nat.lt_of_lt_of_le
                  (Nat.lt_of_lt_of_le (Nat.lt_succ_self windowPosition)
                    (Nat.le_succ (windowPosition + 1)))
                  windowFits)
                (Nat.le_trans (Nat.le_of_eq tailBoundaryFits.symm)
                  (Nat.le_trans (Nat.succ_le_succ (Nat.succ_le_succ atTail))
                    (Nat.le_succ (probeIndex + 2)))))
              (Nat.le_of_eq windowHitsShifted.symm)))

/-- ★ **No reindexed probe hits the event node `bottomCount`** — zone I and II values stay
strictly below the source boundary, zone III values translate strictly past it. -/
theorem arcCapHeadReindex_missesEventNode
    (bottomCount windowPosition tailBoundary probeIndex : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount) :
    (bottomCount == arcHeadReindex
      (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3 probeIndex) = false := by
  cases Nat.lt_or_ge probeIndex windowPosition with
  | inl belowWindow =>
      rw [arcCapHeadReindex_belowWindow bottomCount windowPosition tailBoundary probeIndex
        windowFits tailBoundaryFits belowWindow]
      exact decide_eq_false (fun eventHitsProbe => Nat.lt_irrefl bottomCount
        (Nat.lt_of_le_of_lt (Nat.le_of_eq eventHitsProbe)
          (Nat.lt_of_lt_of_le belowWindow
            (Nat.le_trans (Nat.le_add_right windowPosition 2) windowFits))))
  | inr atWindow =>
      cases Nat.lt_or_ge probeIndex tailBoundary with
      | inl belowTail =>
          obtain ⟨pastOffset, offsetSpec⟩ := Nat.le.dest atWindow
          have pastBound : windowPosition + pastOffset < tailBoundary := by
            rw [offsetSpec]
            exact belowTail
          rw [← offsetSpec,
            arcCapHeadReindex_pastWindow bottomCount windowPosition tailBoundary pastOffset
              windowFits tailBoundaryFits pastBound]
          exact decide_eq_false (fun eventHitsValue => Nat.lt_irrefl bottomCount
            (Nat.lt_of_le_of_lt (Nat.le_of_eq eventHitsValue)
              (Nat.lt_of_lt_of_le (Nat.succ_lt_succ (Nat.succ_lt_succ pastBound))
                (Nat.le_of_eq tailBoundaryFits))))
      | inr atTail =>
          rw [arcHeadReindex_capSeedShifts bottomCount windowPosition tailBoundary
            windowFits tailBoundaryFits probeIndex atTail]
          exact decide_eq_false (fun eventHitsShifted => Nat.lt_irrefl bottomCount
            (Nat.lt_of_lt_of_le
              (Nat.lt_of_le_of_lt (Nat.le_of_eq tailBoundaryFits.symm)
                (Nat.lt_of_lt_of_le (Nat.lt_succ_self (tailBoundary + 2))
                  (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ atTail)))))
              (Nat.le_of_eq eventHitsShifted.symm)))

/-! ## Honesty marker -/

/-- **Honesty marker — the cap-head reindexing's value zones (peel campaign H, seed rung,
cap LINKS-leg atoms, part 1).**  The below-window identity read, the past-window up-by-two
read (through the pair-removal suffix), and the two component-avoidance atoms: no reindexed
probe hits the left wire `windowPosition` or the event node `bottomCount` — the cap
component's anchors in the composite links.  What this marker does NOT claim: the cap
injectivity atom and beq correspondence, the assembled cap-seed `ArcComponentShiftCorr`
(with its degenerate legs), and the extract correspondence.  `= true`. -/
def fxMode_hasArcCapHeadReindexValues : Bool := true

end FX1Poly.Polygraph
