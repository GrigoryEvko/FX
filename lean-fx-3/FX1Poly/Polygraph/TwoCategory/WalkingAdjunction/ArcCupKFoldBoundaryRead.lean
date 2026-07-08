import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupDisjointCapWindowPin
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupLegAttachment

/-! # ArcCupKFoldBoundaryRead — the OFF-ZONE boundary read past an ARBITRARY window-disjoint cap tail

`ArcCupDisjointCapWindowPin` shipped the single-cap boundary reads: `twoAtomBoundaryRead_atLeftLeg` (the cup's
left leg still reads `bottomCount` through ONE disjoint cap's `natListRemoveTwoAt`) and `_belowWindow` (every
port strictly below the cup window still reads `< bottomCount`).  Both route through EXACTLY ONE
`natListGetAt_natListRemoveTwoAt_below` (the cap's removal at a higher position leaves the read below it
untouched).  This brick lifts the REMOVAL side of those reads from ONE cap to an ARBITRARY window-disjoint cap
tail — the boundary-read dual of the shipped r6 JOIN-side `isSameComponent_foldJoins_offProbe` /
`foldJoins` (`ArcCupDisjointTailJoinInvariance`), and exactly the open honesty-marker item (1) there: "the
`k`-fold composition of `natListRemoveTwoAt` disjoint removals leaving the leg read `1` and the below-window
reads `0`".

## The k-fold removal invariant

  * ★ `foldRemovals` — fold a list of removal positions onto a base wire list, each contributing one
    `natListRemoveTwoAt` (the arc-fold's open-wire evolution when every tail atom is a cap;
    `stepCap_openWires` makes each open-wire update a single `natListRemoveTwoAt`).  This is the removal-side
    dual of the r6 `foldJoins`.
  * ★ `natListGetAt_foldRemovals_below` — the ★ kernel: reading strictly below EVERY (fold-time) removal
    position is preserved through the WHOLE list of removals.  Structural induction on `positions`, reusing
    the single-removal `natListGetAt_natListRemoveTwoAt_below` at the head — the line-for-line mirror of the
    join-side `isSameComponent_foldJoins_offProbe`.
  * ★ `kCapBoundaryRead_atLeftLeg` / `_belowWindow` — the single-cap reads lifted: the cup's left leg reads
    `bottomCount` (leg read `= bottomCount`), and every port strictly below the cup window reads `< bottomCount`,
    through an ARBITRARY window-disjoint cap tail (every cap position strictly above the cup window).  Both are
    the shipped single-cap proof body with the one removal replaced by the fold.

The window-disjointness hypothesis `∀ pos ∈ capWindows, cupWindow < pos` is the OFF-ZONE condition: each cap's
live window sits strictly above the leg strand, so the fold-time positions all exceed `cupWindow` and the leg /
below-window reads flow past every removal.  Composed with the r6 `isSameComponent_foldJoins_offZone` (the
links side), this is the boundary-read half of the head-cup `internalCupCounts` census read-off for arbitrarily
many disjoint caps — the OFF-ZONE census locator.

Raw Lean 4 + Init; structural on the position list, the same range/insert/removal kit as the single-cap brick,
no `omega` / `simp`-AC / `WellFounded.fix`.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Range-read plumbing (the established per-file private idiom; core `List.length_range` leaks propext) -/

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

/-! ## The k-fold removal and its below-invariance -/

/-- Fold a list of removal positions onto a base wire list: each position `pos` contributes one
`natListRemoveTwoAt · pos`.  This is the arc-fold's open-wire evolution when every tail atom is a cap — each
cap's open-wire update is a single `natListRemoveTwoAt` (`stepCap_openWires`).  The removal-side dual of the r6
`foldJoins`. -/
def foldRemovals (wires : List Nat) (positions : List Nat) : List Nat :=
  positions.foldl natListRemoveTwoAt wires

/-- ★ **Reading strictly below every removal position survives the WHOLE fold.**  If `index` is strictly below
every position in `positions`, then `natListGetAt (foldRemovals wires positions) index = natListGetAt wires
index`.  Structural induction on `positions`, reusing the single-removal `natListGetAt_natListRemoveTwoAt_below`
at the head; the tail's below-hypotheses transfer verbatim (they never mention the wires).  The boundary-read
dual of the join-side `isSameComponent_foldJoins_offProbe`. -/
theorem natListGetAt_foldRemovals_below (index : Nat) :
    (positions : List Nat) → (wires : List Nat) →
    (∀ pos, pos ∈ positions → index < pos) →
    natListGetAt (foldRemovals wires positions) index = natListGetAt wires index
  | [], _, _ => rfl
  | pos :: rest, wires, allAbove =>
      (natListGetAt_foldRemovals_below index rest (natListRemoveTwoAt wires pos)
          (fun laterPos laterMember => allAbove laterPos (List.Mem.tail pos laterMember))).trans
        (natListGetAt_natListRemoveTwoAt_below wires pos index (allAbove pos (List.Mem.head rest)))

/-! ## The single-cup open-wire list (the base carrier the cap tail folds over) -/

/-- The inserted open-wire list after a lone cup step — the seed range with the two legs spliced at the cup
window.  (Local re-statement of the single-cap file's private `cupOpenWires`, so this brick stands alone.) -/
def cupOpenWiresK (bottomCount cupWindow : Nat) : List Nat :=
  natListInsertAt (List.range bottomCount) cupWindow [bottomCount, bottomCount + 1]

/-! ## The two boundary reads, lifted past a k-cap window-disjoint tail -/

/-- ★ **The cup's left leg reads `bottomCount` past an arbitrary window-disjoint cap tail.**  For the boundary
list `List.range bottomCount ++ foldRemovals (cupOpenWiresK ...) capWindows`, reading at the left-leg index
`bottomCount + cupWindow` returns the left leg `bottomCount`, provided the cup window fits
(`cupWindow ≤ bottomCount`) and every cap position sits strictly above the cup window
(`∀ pos ∈ capWindows, cupWindow < pos`).  The single-cap `twoAtomBoundaryRead_atLeftLeg` with the one removal
replaced by the fold (`natListGetAt_foldRemovals_below`). -/
theorem kCapBoundaryRead_atLeftLeg (bottomCount cupWindow : Nat) (capWindows : List Nat)
    (cupFits : cupWindow ≤ bottomCount)
    (allAbove : ∀ pos, pos ∈ capWindows → cupWindow < pos) :
    natListGetAt
        (List.range bottomCount ++ foldRemovals (cupOpenWiresK bottomCount cupWindow) capWindows)
        (bottomCount + cupWindow) = bottomCount := by
  have hIdx : bottomCount + cupWindow = cupWindow + (List.range bottomCount).length := by
    rw [rangeLength, Nat.add_comm cupWindow bottomCount]
  rw [hIdx, natListGetAt_append_pastBlock (List.range bottomCount)
      (foldRemovals (cupOpenWiresK bottomCount cupWindow) capWindows) cupWindow]
  rw [natListGetAt_foldRemovals_below cupWindow capWindows (cupOpenWiresK bottomCount cupWindow) allAbove]
  show natListGetAt (natListInsertAt (List.range bottomCount) cupWindow [bottomCount, bottomCount + 1])
      cupWindow = bottomCount
  have hInner := natListGetAt_natListInsertAt_inside (List.range bottomCount) cupWindow
    [bottomCount, bottomCount + 1] 0 (Nat.succ_pos 1) (by rw [rangeLength]; exact cupFits)
  rw [Nat.add_zero] at hInner
  exact hInner

/-- ★ **Every port strictly below the cup window reads `< bottomCount` past an arbitrary window-disjoint cap
tail.**  For the boundary list `List.range bottomCount ++ foldRemovals (cupOpenWiresK ...) capWindows`, reading
at any `index < bottomCount + cupWindow` returns a value strictly below `bottomCount` (a bottom port or a
below-window seed wire), provided the cup window fits and every cap position sits strictly above it.  The
single-cap `twoAtomBoundaryRead_belowWindow` with the one removal replaced by the fold. -/
theorem kCapBoundaryRead_belowWindow (bottomCount cupWindow index : Nat) (capWindows : List Nat)
    (cupFits : cupWindow ≤ bottomCount) (indexBelow : index < bottomCount + cupWindow)
    (allAbove : ∀ pos, pos ∈ capWindows → cupWindow < pos) :
    natListGetAt
        (List.range bottomCount ++ foldRemovals (cupOpenWiresK bottomCount cupWindow) capWindows)
        index < bottomCount := by
  cases Nat.lt_or_ge index bottomCount with
  | inl indexInPrefix =>
      rw [natListGetAt_rangeAppend_below bottomCount
        (foldRemovals (cupOpenWiresK bottomCount cupWindow) capWindows) index indexInPrefix]
      exact indexInPrefix
  | inr indexAtLeast =>
      obtain ⟨offset, offsetEq⟩ := Nat.le.dest indexAtLeast
      have offsetLtWindow : offset < cupWindow :=
        Nat.lt_of_add_lt_add_left
          (show bottomCount + offset < bottomCount + cupWindow by rw [offsetEq]; exact indexBelow)
      have hIdx : bottomCount + offset = offset + (List.range bottomCount).length := by
        rw [rangeLength, Nat.add_comm]
      have readVal : natListGetAt
          (List.range bottomCount ++ foldRemovals (cupOpenWiresK bottomCount cupWindow) capWindows)
          (bottomCount + offset) < bottomCount := by
        rw [hIdx, natListGetAt_append_pastBlock (List.range bottomCount)
            (foldRemovals (cupOpenWiresK bottomCount cupWindow) capWindows) offset]
        rw [natListGetAt_foldRemovals_below offset capWindows (cupOpenWiresK bottomCount cupWindow)
            (fun pos posMember => Nat.lt_trans offsetLtWindow (allAbove pos posMember))]
        show natListGetAt (natListInsertAt (List.range bottomCount) cupWindow [bottomCount, bottomCount + 1])
            offset < bottomCount
        rw [natListGetAt_natListInsertAt_below (List.range bottomCount) cupWindow
            [bottomCount, bottomCount + 1] offset offsetLtWindow
            (by rw [rangeLength]; exact Nat.lt_of_lt_of_le offsetLtWindow cupFits),
          rangeGetAt_below bottomCount offset (Nat.lt_of_lt_of_le offsetLtWindow cupFits)]
        exact Nat.lt_of_lt_of_le offsetLtWindow cupFits
      rw [← offsetEq]; exact readVal

/-! ## Honesty marker -/

/-- **Honesty marker — the BOUNDARY-READ side of the census read-off holds past an ARBITRARY window-disjoint
cap tail.**  `natListGetAt_foldRemovals_below` lifts the single-cap `natListGetAt_natListRemoveTwoAt_below`
from ONE removal to a fold of arbitrarily many removals, each strictly above the read index; `kCapBoundaryRead_atLeftLeg`
/ `_belowWindow` package it as the head-cup boundary reads (leg `= bottomCount`, below-window `< bottomCount`)
through a window-disjoint cap tail of ANY length.  This is the removal-side dual of the r6 JOIN-side
`isSameComponent_foldJoins_offProbe` (`foldJoins` / `ArcCupDisjointTailJoinInvariance`), closing that file's
open honesty-marker item (1).  Composed with `isSameComponent_foldJoins_offZone` (the links side, the census
being `if isSameComponent ... then 1 else 0`), the two together are the OFF-ZONE census locator: for a cup
followed by an arbitrary window-disjoint cap tail, `internalCupCounts` reads `1` at the left leg and `0` below,
locating the head cup's window by census.

What this marker does NOT claim — the on-zone completion the OFF-ZONE readoff cannot reach:
  (1) the ON-ZONE (interacting, window-adjacent) cap — where cup and cap ARE a zigzag and CANCEL via the snake,
      NOT a census read-off (census REFUTED there by `headCupWindowReadoff_isFalse`); that is the swap-normal-form
      route, not this fold.
  (2) the state-level accounting tying a REAL k-cap spine's open-wire field to `foldRemovals` and its links
      field to `foldJoins`, discharging the window-disjointness hypotheses from real cap `leftContext.length`s.
No gate flip: `fxMode_hasArcStructureReconstruction` and `fxMode_hasModeRelativeConvDecision` stay as is — this
is the OFF-ZONE boundary-read ingredient, not the full mixed reconstruction.  `= true`. -/
def fxMode_hasArcCupKFoldBoundaryRead : Bool := true

end FX1Poly.Polygraph
