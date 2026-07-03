import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingSwapRenameable
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFreshShift
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingComponentAlgebra

/-! # mode-3 — the boundary-node read-through kit (the connectivity-view substrate)

The MODE3-C congruence fields (`MatchingSaturatedCongruence`) require relating runs whose
intermediate states agree only through the CONNECTIVITY VIEW — `openWires.length`, `loops`, and
the same-component relation on the boundary nodes (`matchingBoundaryNodes bottomCount state =
List.range bottomCount ++ state.openWires`).  Establishing that the view is step-stable needs
INDEX-level reads of the boundary-node list before and after each cup/cap step.  This file ships
that read-through kit:

  * `matchingBoundaryNodes_length` — the boundary-node count is `bottomCount +
    openWires.length` (hand-rolled lengths; core `List.length_append` / `List.length_range`
    leak `propext`);
  * `matchingBoundaryNodes_getAt_bottomAgrees` — ANY two states read the same node below
    `bottomCount` (both read the shared `List.range` prefix);
  * `matchingBoundaryNodes_getAt_top` — a read at `bottomCount + offset` is the open-wire read
    at `offset` (the workhorse: every step lemma below factors through it);
  * cap zone reads — `…_stepCap_getAt_below` (top-zone reads below the window survive) and
    `…_stepCap_getAt_pastPair` (reads at or beyond the window shift down by the dropped pair);
  * cup zone reads — `…_stepCup_getAt_below`, `…_stepCup_getAt_leftLeg` / `…_rightLeg` (the
    spliced window reads the two fresh ids), and `…_stepCup_getAt_pastBlock` (reads beyond the
    splice shift up by the block).

Together with the shipped join algebra (`isSameComponent_unionFindJoin`,
`stepCap_loops_eq_addIncrement`) and the fresh-leg isolation (`isSameComponent_freshPair_eq_false`,
`unionFindRootOf_eq_self_ofFresh`), these reads let the next brick express the post-step view as
a pure function of the pre-step view at reindexed positions.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## List-length helpers (hand-rolled; core `List.length_append` / `List.length_range` leak) -/

private theorem natListAppendLength : (front back : List Nat) →
    (front ++ back).length = front.length + back.length
  | [], back => (Nat.zero_add back.length).symm
  | head :: tail, back => by
      show (tail ++ back).length + 1 = tail.length + 1 + back.length
      rw [natListAppendLength tail back,
        Nat.add_right_comm tail.length back.length 1]

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

/-! ## The boundary-node list: length and the two zone reads -/

/-- The boundary-node list counts the bottom boundary plus the open wires. -/
theorem matchingBoundaryNodes_length (bottomCount : Nat) (state : WireState) :
    (matchingBoundaryNodes bottomCount state).length
      = bottomCount + state.openWires.length := by
  show (List.range bottomCount ++ state.openWires).length
    = bottomCount + state.openWires.length
  rw [natListAppendLength (List.range bottomCount) state.openWires, rangeLength bottomCount]

/-- **The bottom zone is state-independent** — any two states read the same boundary node below
`bottomCount`, because both read the shared `List.range bottomCount` prefix. -/
theorem matchingBoundaryNodes_getAt_bottomAgrees (bottomCount : Nat)
    (stateA stateB : WireState) (index : Nat) (belowBottom : index < bottomCount) :
    natListGetAt (matchingBoundaryNodes bottomCount stateA) index
      = natListGetAt (matchingBoundaryNodes bottomCount stateB) index := by
  have indexInRange : index < (List.range bottomCount).length := by
    rw [rangeLength bottomCount]
    exact belowBottom
  show natListGetAt (List.range bottomCount ++ stateA.openWires) index
    = natListGetAt (List.range bottomCount ++ stateB.openWires) index
  rw [natListGetAt_append_inside (List.range bottomCount) stateA.openWires index indexInRange,
    natListGetAt_append_inside (List.range bottomCount) stateB.openWires index indexInRange]

/-- **The top-zone read is the open-wire read** — the workhorse: a boundary-node read at
`bottomCount + offset` is exactly the open-wire read at `offset`. -/
theorem matchingBoundaryNodes_getAt_top (bottomCount : Nat) (state : WireState)
    (offset : Nat) :
    natListGetAt (matchingBoundaryNodes bottomCount state) (bottomCount + offset)
      = natListGetAt state.openWires offset := by
  have indexForm : bottomCount + offset = offset + (List.range bottomCount).length := by
    rw [rangeLength bottomCount]
    exact Nat.add_comm bottomCount offset
  show natListGetAt (List.range bottomCount ++ state.openWires) (bottomCount + offset)
    = natListGetAt state.openWires offset
  rw [indexForm]
  exact natListGetAt_append_pastBlock (List.range bottomCount) state.openWires offset

/-! ## Cap zone reads (the pair at the window drops; reads reindex down by two past it) -/

/-- A cap leaves top-zone boundary reads strictly below its window untouched. -/
theorem matchingBoundaryNodes_stepCap_getAt_below (bottomCount : Nat) (state : WireState)
    (position offset : Nat) (belowWindow : offset < position) :
    natListGetAt (matchingBoundaryNodes bottomCount (stepCap state position))
        (bottomCount + offset)
      = natListGetAt (matchingBoundaryNodes bottomCount state) (bottomCount + offset) := by
  rw [matchingBoundaryNodes_getAt_top bottomCount (stepCap state position) offset,
    matchingBoundaryNodes_getAt_top bottomCount state offset,
    stepCap_openWires state position]
  exact natListGetAt_natListRemoveTwoAt_below state.openWires position offset belowWindow

/-- A cap (with its window in range) shifts every top-zone boundary read at or beyond the window
down by the dropped pair: reading at `bottomCount + (position + offset)` after equals reading at
`bottomCount + (position + offset + 2)` before. -/
theorem matchingBoundaryNodes_stepCap_getAt_pastPair (bottomCount : Nat) (state : WireState)
    (position offset : Nat) (windowInRange : position + 2 ≤ state.openWires.length) :
    natListGetAt (matchingBoundaryNodes bottomCount (stepCap state position))
        (bottomCount + (position + offset))
      = natListGetAt (matchingBoundaryNodes bottomCount state)
        (bottomCount + (position + offset + 2)) := by
  rw [matchingBoundaryNodes_getAt_top bottomCount (stepCap state position) (position + offset),
    matchingBoundaryNodes_getAt_top bottomCount state (position + offset + 2),
    stepCap_openWires state position]
  exact natListGetAt_natListRemoveTwoAt_pastPair state.openWires position offset windowInRange

/-! ## Cup zone reads (two fresh legs splice in at the window; reads reindex up by two past it) -/

/-- A cup leaves top-zone boundary reads strictly below its window untouched (in-range reads —
an out-of-range splice lands early, hence the length bound). -/
theorem matchingBoundaryNodes_stepCup_getAt_below (bottomCount : Nat) (state : WireState)
    (position offset : Nat) (belowWindow : offset < position)
    (belowLength : offset < state.openWires.length) :
    natListGetAt (matchingBoundaryNodes bottomCount (stepCup state position))
        (bottomCount + offset)
      = natListGetAt (matchingBoundaryNodes bottomCount state) (bottomCount + offset) := by
  rw [matchingBoundaryNodes_getAt_top bottomCount (stepCup state position) offset,
    matchingBoundaryNodes_getAt_top bottomCount state offset,
    stepCup_openWires state position]
  exact natListGetAt_natListInsertAt_below state.openWires position
    [state.nextFresh, state.nextFresh + 1] offset belowWindow belowLength

/-- A cup's spliced window reads the LEFT fresh leg at its position. -/
theorem matchingBoundaryNodes_stepCup_getAt_leftLeg (bottomCount : Nat) (state : WireState)
    (position : Nat) (positionLe : position ≤ state.openWires.length) :
    natListGetAt (matchingBoundaryNodes bottomCount (stepCup state position))
        (bottomCount + position)
      = state.nextFresh := by
  rw [matchingBoundaryNodes_getAt_top bottomCount (stepCup state position) position,
    stepCup_openWires state position]
  exact natListGetAt_natListInsertAt_inside state.openWires position
    [state.nextFresh, state.nextFresh + 1] 0 (Nat.succ_le_succ (Nat.zero_le 1)) positionLe

/-- A cup's spliced window reads the RIGHT fresh leg one past its position. -/
theorem matchingBoundaryNodes_stepCup_getAt_rightLeg (bottomCount : Nat) (state : WireState)
    (position : Nat) (positionLe : position ≤ state.openWires.length) :
    natListGetAt (matchingBoundaryNodes bottomCount (stepCup state position))
        (bottomCount + (position + 1))
      = state.nextFresh + 1 := by
  rw [matchingBoundaryNodes_getAt_top bottomCount (stepCup state position) (position + 1),
    stepCup_openWires state position]
  exact natListGetAt_natListInsertAt_inside state.openWires position
    [state.nextFresh, state.nextFresh + 1] 1 (Nat.le_refl 2) positionLe

/-- A cup (with its position in range) shifts every top-zone boundary read at or beyond the
window up by the spliced pair: reading at `bottomCount + (position + offset + 2)` after equals
reading at `bottomCount + (position + offset)` before. -/
theorem matchingBoundaryNodes_stepCup_getAt_pastBlock (bottomCount : Nat) (state : WireState)
    (position offset : Nat) (positionLe : position ≤ state.openWires.length) :
    natListGetAt (matchingBoundaryNodes bottomCount (stepCup state position))
        (bottomCount + (position + offset + 2))
      = natListGetAt (matchingBoundaryNodes bottomCount state)
        (bottomCount + (position + offset)) := by
  rw [matchingBoundaryNodes_getAt_top bottomCount (stepCup state position)
      (position + offset + 2),
    matchingBoundaryNodes_getAt_top bottomCount state (position + offset),
    stepCup_openWires state position]
  exact natListGetAt_natListInsertAt_pastBlock state.openWires position
    [state.nextFresh, state.nextFresh + 1] offset positionLe

/-! ## The cap reindex function (the total read factoring the view proof consumes) -/

/-- The cap's boundary-index reindexing: indices strictly below the window survive unchanged,
indices at or beyond it shift up by the dropped pair.  The post-cap boundary read at `index`
IS the pre-cap boundary read at `capBoundaryReindex bottomCount position index` — one total
function, no zone case-split at the consumer. -/
def capBoundaryReindex (bottomCount position index : Nat) : Nat :=
  if index < bottomCount + position then index else index + 2

/-- ★ **The post-cap boundary read factors through the reindex** — unconditional in the index
(given the window in range): below the window via the bottom-zone/below reads, at or beyond it
via the past-pair shift. -/
theorem matchingBoundaryNodes_stepCap_getAt_reindex (bottomCount : Nat) (state : WireState)
    (position index : Nat) (windowInRange : position + 2 ≤ state.openWires.length) :
    natListGetAt (matchingBoundaryNodes bottomCount (stepCap state position)) index
      = natListGetAt (matchingBoundaryNodes bottomCount state)
        (capBoundaryReindex bottomCount position index) := by
  show natListGetAt (matchingBoundaryNodes bottomCount (stepCap state position)) index
    = natListGetAt (matchingBoundaryNodes bottomCount state)
      (if index < bottomCount + position then index else index + 2)
  cases Nat.lt_or_ge index (bottomCount + position) with
  | inl belowWindow =>
      rw [if_pos belowWindow]
      cases Nat.lt_or_ge index bottomCount with
      | inl belowBottom =>
          exact matchingBoundaryNodes_getAt_bottomAgrees bottomCount
            (stepCap state position) state index belowBottom
      | inr atLeastBottom =>
          obtain ⟨offset, rfl⟩ := Nat.le.dest atLeastBottom
          exact matchingBoundaryNodes_stepCap_getAt_below bottomCount state position offset
            (Nat.lt_of_add_lt_add_left belowWindow)
  | inr atOrPastWindow =>
      rw [if_neg (fun contra =>
        Nat.lt_irrefl index (Nat.lt_of_lt_of_le contra atOrPastWindow))]
      obtain ⟨offset, rfl⟩ := Nat.le.dest atOrPastWindow
      rw [Nat.add_assoc bottomCount position offset,
        Nat.add_assoc bottomCount (position + offset) 2]
      exact matchingBoundaryNodes_stepCap_getAt_pastPair bottomCount state position offset
        windowInRange

/-! ## Step length bookkeeping (additive forms — no subtraction) -/

/-- An in-range cap drops exactly two open wires (additive form). -/
theorem stepCap_openWiresLength (state : WireState) (position : Nat)
    (windowInRange : position + 2 ≤ state.openWires.length) :
    (stepCap state position).openWires.length + 2 = state.openWires.length := by
  rw [stepCap_openWires state position]
  exact natListRemoveTwoAt_length state.openWires position windowInRange

/-- A cup splices in exactly two open wires (unconditional). -/
theorem stepCup_openWiresLength (state : WireState) (position : Nat) :
    (stepCup state position).openWires.length = state.openWires.length + 2 := by
  rw [stepCup_openWires state position]
  exact natListInsertAt_length state.openWires position
    [state.nextFresh, state.nextFresh + 1]

/-- **The cap reindex lands in the pre-cap range**: a post-cap in-range boundary index
reindexes to a pre-cap in-range one — below the window because the window itself is in range,
at or beyond it because the shift by the dropped pair restores the old count. -/
theorem capBoundaryReindex_lt_ofNewRange (bottomCount : Nat) (state : WireState)
    (position index : Nat) (windowInRange : position + 2 ≤ state.openWires.length)
    (indexInNewRange : index < bottomCount + (stepCap state position).openWires.length) :
    capBoundaryReindex bottomCount position index
      < bottomCount + state.openWires.length := by
  show (if index < bottomCount + position then index else index + 2)
    < bottomCount + state.openWires.length
  cases Nat.lt_or_ge index (bottomCount + position) with
  | inl belowWindow =>
      rw [if_pos belowWindow]
      exact Nat.lt_of_lt_of_le belowWindow
        (Nat.add_le_add_left
          (Nat.le_trans (Nat.le_add_right position 2) windowInRange) bottomCount)
  | inr atOrPastWindow =>
      rw [if_neg (fun contra =>
        Nat.lt_irrefl index (Nat.lt_of_lt_of_le contra atOrPastWindow))]
      have shiftedBound : index + 2
          < bottomCount + (stepCap state position).openWires.length + 2 :=
        Nat.add_lt_add_right indexInNewRange 2
      rw [Nat.add_assoc bottomCount (stepCap state position).openWires.length 2,
        stepCap_openWiresLength state position windowInRange] at shiftedBound
      exact shiftedBound

/-! ## The cap's link and loop updates in boundary-index (view) form -/

/-- The cap's unconditional join, with its two legs as BOUNDARY reads: the join legs are the
boundary nodes at indices `bottomCount + position` and `bottomCount + (position + 1)`. -/
theorem stepCap_links_eq_unionFindJoin_boundaryReads (bottomCount : Nat) (state : WireState)
    (position : Nat) :
    (stepCap state position).links
      = unionFindJoin state.links
          (natListGetAt (matchingBoundaryNodes bottomCount state) (bottomCount + position))
          (natListGetAt (matchingBoundaryNodes bottomCount state)
            (bottomCount + (position + 1))) := by
  rw [matchingBoundaryNodes_getAt_top bottomCount state position,
    matchingBoundaryNodes_getAt_top bottomCount state (position + 1)]
  exact stepCap_links_eq_unionFindJoin state position

/-- The cap's loop increment IS the connectivity view's boolean at the window: loops after =
loops before + the same-component view at boundary indices `bottomCount + position`,
`bottomCount + (position + 1)`. -/
theorem stepCap_loops_eq_addViewIncrement (bottomCount : Nat) (state : WireState)
    (position : Nat) :
    (stepCap state position).loops
      = state.loops
          + (matchingSameComponent bottomCount state (bottomCount + position)
              (bottomCount + (position + 1))).toNat := by
  have viewForm : matchingSameComponent bottomCount state (bottomCount + position)
        (bottomCount + (position + 1))
      = isSameComponent state.links (natListGetAt state.openWires position)
        (natListGetAt state.openWires (position + 1)) := by
    show (unionFindRootOf state.links
          (natListGetAt (matchingBoundaryNodes bottomCount state) (bottomCount + position))
        == unionFindRootOf state.links
          (natListGetAt (matchingBoundaryNodes bottomCount state)
            (bottomCount + (position + 1))))
      = (unionFindRootOf state.links (natListGetAt state.openWires position)
        == unionFindRootOf state.links (natListGetAt state.openWires (position + 1)))
    rw [matchingBoundaryNodes_getAt_top bottomCount state position,
      matchingBoundaryNodes_getAt_top bottomCount state (position + 1)]
  rw [stepCap_loops_eq_addIncrement state position, viewForm]

/-! ## Honesty marker -/

/-- **Honesty marker — the boundary-node read-through kit is SHIPPED.**  Index-level reads of
`matchingBoundaryNodes` before and after a cup/cap step: the length count, the state-independent
bottom zone, the top-zone/open-wire factoring, the cap's below/past-pair reindexing, and the
cup's below/fresh-legs/past-block reindexing — plus the TOTAL cap reindex factoring
(`capBoundaryReindex` + `matchingBoundaryNodes_stepCap_getAt_reindex` + its range transport),
the additive step length bookkeeping, and the cap's join legs / loop increment re-read in
boundary-index (view) form.  NOT yet covered: the connectivity-view step-stability consuming
these reads (the post-step view as a pure function of the pre-step view, via the shipped join
algebra) and the run-composition law behind the `MatchingSaturatedCongruence` fields — the
remaining MODE3-C bricks.  `= true`. -/
def fxMode_hasMatchingBoundaryReadKit : Bool := true

end FX1Poly.Polygraph
