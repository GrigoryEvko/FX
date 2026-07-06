import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupFoldedInternalCountFold
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFreshShift

/-! # ArcCupFoldedInternalCountFreshArc — the internal count legs from FRESH-SEED ARC EQUALITY (peel campaign H)

`ArcCupFoldedInternalCountFold` ships the two internal-count folds
(`arcCupFoldedInternalCupCountList_agrees` / `…Cap…`): from a per-index agreement of the fresh
`internalEventCountAt` readoff over the whole composite range, the two folded count lists coincide.  Its
honesty marker leaves owed "the per-index count agreements themselves … under the orbit's
`sameClassification`".  This brick discharges that residual for BOTH count legs — and reveals it is far
cheaper than the diagram leg's:

DECISIVE OBSERVATION.  The fold reads off `internalEventCountAt (fresh run).links (fresh boundary)
(fresh run).cupEventNodes (freshShiftAbove windowPosition 2 compositeIndex)`, and — because
`extractArc` builds `internalCupCounts := (List.range total).map (internalEventCountAt links boundary
cupEventNodes)` — that readoff at an in-range index is EXACTLY the `internalCupCounts` field entry of
`arcStructureOfSpineList (bottomCount + 2) (fresh run)` at that index.  So if the two fresh runs carry
EQUAL arc structure at the `bottomCount + 2` seed, their `internalCupCounts` fields are equal as lists,
hence their per-index readoffs agree — with no `sameClassification` classifier anywhere.  Contrast the
diagram leg, which reads the RAW `partnerIndexOf` (strictly finer than the extracted `DiagramType`
`.diagram` field) and therefore genuinely needs the through-the-head orbit's leg-attachment
classification.

So the residual map sharpens: the cup tails-cancel's two INTERNAL count legs need only FRESH-SEED ARC
EQUALITY — a trace invariant already delivered by the shipped soundness (arc-structure invariance under
trace equivalence) — while only the DIAGRAM leg still owes the deep orbit `sameClassification`.

  * `arcCupFoldedInternalCupCountList_agrees_ofFreshArcEqual` — the cup-count leg from fresh arc equality;
  * `arcCupFoldedInternalCapCountList_agrees_ofFreshArcEqual` — the cap-count leg, identically.

Raw Lean 4 + Init; the range-read kit is the established per-file idiom; per-declaration `#assert_no_axioms`
gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The range-read kit (the established per-file private idiom) -/

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

/-- Reading the `index`-th entry of `(List.range total).map mappedFunction` at an in-range index is
`mappedFunction index` — the map commutes with the range read, then the range read is the index. -/
private theorem natRangeMapGetAt (total : Nat) (mappedFunction : Nat → Nat) (index : Nat)
    (indexInRange : index < total) :
    natListGetAt ((List.range total).map mappedFunction) index = mappedFunction index := by
  rw [natListGetAt_map_inRange mappedFunction (List.range total) index
      (by rw [rangeLength total]; exact indexInRange),
    rangeGetAt_below total index indexInRange]

/-- The fresh shift lands at most `delta` above its argument (it shifts by exactly `delta` at or above the
threshold, and fixes below). -/
private theorem freshShiftLeAddDelta (threshold delta identifier : Nat) :
    freshShiftAbove threshold delta identifier ≤ identifier + delta := by
  cases Nat.lt_or_ge identifier threshold with
  | inl isBelow =>
      rw [freshShiftAbove_ofNotLe threshold delta identifier (Nat.not_le_of_lt isBelow)]
      exact Nat.le_add_right identifier delta
  | inr isAtOrAbove =>
      exact Nat.le_of_eq (freshShiftAbove_ofLe threshold delta identifier isAtOrAbove)

/-! ## The arc-structure field unfoldings (definitional) -/

/-- The internal cup-count field of `arcStructureOfSpineList` IS the range-map of the fresh
`internalEventCountAt` cup readoff — definitional, straight from `extractArc`'s field. -/
private theorem arcInternalCupCountsUnfold {overallSource overallTarget : adjunctionGraph.Mode}
    (seed : Nat)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) :
    (arcStructureOfSpineList seed atoms).internalCupCounts
      = (List.range
          (seed
            + (processArcSpine (ArcWireState.mk (List.range seed) [] seed 0 [] [])
                atoms).openWires.length)).map
          (internalEventCountAt
            (processArcSpine (ArcWireState.mk (List.range seed) [] seed 0 [] []) atoms).links
            (List.range seed
              ++ (processArcSpine (ArcWireState.mk (List.range seed) [] seed 0 [] []) atoms).openWires)
            (processArcSpine (ArcWireState.mk (List.range seed) [] seed 0 [] []) atoms).cupEventNodes) :=
  rfl

/-- The cap sibling of `arcInternalCupCountsUnfold`. -/
private theorem arcInternalCapCountsUnfold {overallSource overallTarget : adjunctionGraph.Mode}
    (seed : Nat)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) :
    (arcStructureOfSpineList seed atoms).internalCapCounts
      = (List.range
          (seed
            + (processArcSpine (ArcWireState.mk (List.range seed) [] seed 0 [] [])
                atoms).openWires.length)).map
          (internalEventCountAt
            (processArcSpine (ArcWireState.mk (List.range seed) [] seed 0 [] []) atoms).links
            (List.range seed
              ++ (processArcSpine (ArcWireState.mk (List.range seed) [] seed 0 [] []) atoms).openWires)
            (processArcSpine (ArcWireState.mk (List.range seed) [] seed 0 [] []) atoms).capEventNodes) :=
  rfl

/-! ## The two internal-count legs from fresh-seed arc equality -/

/-- ★ **The folded internal CUP-count list agrees from fresh-seed arc equality.**  With the two fresh runs
(at the `bottomCount + 2` seed) carrying EQUAL arc structure and sharing a fresh boundary length, the two
folded cup-count lists coincide: the fold's per-index readoff at `freshShiftAbove windowPosition 2
compositeIndex` is exactly the `internalCupCounts` field entry there, and equal arc structures have equal
fields.  No `sameClassification` — the count leg rides only the shipped soundness (arc invariance). -/
theorem arcCupFoldedInternalCupCountList_agrees_ofFreshArcEqual
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat)
    (firstAtoms secondAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (freshArcEqual : arcStructureOfSpineList (bottomCount + 2) firstAtoms
        = arcStructureOfSpineList (bottomCount + 2) secondAtoms)
    (freshLengthAgree :
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        firstAtoms).openWires.length
      = (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          secondAtoms).openWires.length) :
    (List.range
          (bottomCount
            + (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              firstAtoms).openWires.length)).map
        (fun compositeIndex =>
          internalEventCountAt
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              firstAtoms).links
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
                firstAtoms).openWires)
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              firstAtoms).cupEventNodes
            (freshShiftAbove windowPosition 2 compositeIndex))
      = (List.range
            (bottomCount
              + (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
                firstAtoms).openWires.length)).map
          (fun compositeIndex =>
            internalEventCountAt
              (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
                secondAtoms).links
              (List.range (bottomCount + 2)
                ++ (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
                  secondAtoms).openWires)
              (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
                secondAtoms).cupEventNodes
              (freshShiftAbove windowPosition 2 compositeIndex)) := by
  apply arcCupFoldedInternalCupCountList_agrees bottomCount windowPosition firstAtoms secondAtoms
  intro compositeIndex indexInRange
  have shiftBoundFirst : freshShiftAbove windowPosition 2 compositeIndex
      < (bottomCount + 2)
        + (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            firstAtoms).openWires.length := by
    have step : compositeIndex + 2
        < (bottomCount
            + (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              firstAtoms).openWires.length) + 2 :=
      Nat.add_lt_add_right indexInRange 2
    rw [Nat.add_right_comm bottomCount
        (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          firstAtoms).openWires.length 2] at step
    exact Nat.lt_of_le_of_lt (freshShiftLeAddDelta windowPosition 2 compositeIndex) step
  have shiftBoundSecond : freshShiftAbove windowPosition 2 compositeIndex
      < (bottomCount + 2)
        + (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            secondAtoms).openWires.length := by
    rw [← freshLengthAgree]; exact shiftBoundFirst
  have firstRead :
      internalEventCountAt
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            firstAtoms).links
          (List.range (bottomCount + 2)
            ++ (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              firstAtoms).openWires)
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            firstAtoms).cupEventNodes
          (freshShiftAbove windowPosition 2 compositeIndex)
        = natListGetAt (arcStructureOfSpineList (bottomCount + 2) firstAtoms).internalCupCounts
            (freshShiftAbove windowPosition 2 compositeIndex) := by
    rw [arcInternalCupCountsUnfold (bottomCount + 2) firstAtoms]
    exact (natRangeMapGetAt _ _ _ shiftBoundFirst).symm
  have secondRead :
      internalEventCountAt
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            secondAtoms).links
          (List.range (bottomCount + 2)
            ++ (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              secondAtoms).openWires)
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            secondAtoms).cupEventNodes
          (freshShiftAbove windowPosition 2 compositeIndex)
        = natListGetAt (arcStructureOfSpineList (bottomCount + 2) secondAtoms).internalCupCounts
            (freshShiftAbove windowPosition 2 compositeIndex) := by
    rw [arcInternalCupCountsUnfold (bottomCount + 2) secondAtoms]
    exact (natRangeMapGetAt _ _ _ shiftBoundSecond).symm
  rw [firstRead, secondRead]
  exact congrArg
    (fun theList => natListGetAt theList (freshShiftAbove windowPosition 2 compositeIndex))
    (congrArg FullArcStructure.internalCupCounts freshArcEqual)

/-- ★ **The folded internal CAP-count list agrees from fresh-seed arc equality.**  The cap sibling of
`arcCupFoldedInternalCupCountList_agrees_ofFreshArcEqual`, identically: the fold's per-index cap readoff
is the `internalCapCounts` field entry, and equal arc structures have equal fields. -/
theorem arcCupFoldedInternalCapCountList_agrees_ofFreshArcEqual
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat)
    (firstAtoms secondAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (freshArcEqual : arcStructureOfSpineList (bottomCount + 2) firstAtoms
        = arcStructureOfSpineList (bottomCount + 2) secondAtoms)
    (freshLengthAgree :
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        firstAtoms).openWires.length
      = (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          secondAtoms).openWires.length) :
    (List.range
          (bottomCount
            + (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              firstAtoms).openWires.length)).map
        (fun compositeIndex =>
          internalEventCountAt
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              firstAtoms).links
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
                firstAtoms).openWires)
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              firstAtoms).capEventNodes
            (freshShiftAbove windowPosition 2 compositeIndex))
      = (List.range
            (bottomCount
              + (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
                firstAtoms).openWires.length)).map
          (fun compositeIndex =>
            internalEventCountAt
              (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
                secondAtoms).links
              (List.range (bottomCount + 2)
                ++ (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
                  secondAtoms).openWires)
              (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
                secondAtoms).capEventNodes
              (freshShiftAbove windowPosition 2 compositeIndex)) := by
  apply arcCupFoldedInternalCapCountList_agrees bottomCount windowPosition firstAtoms secondAtoms
  intro compositeIndex indexInRange
  have shiftBoundFirst : freshShiftAbove windowPosition 2 compositeIndex
      < (bottomCount + 2)
        + (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            firstAtoms).openWires.length := by
    have step : compositeIndex + 2
        < (bottomCount
            + (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              firstAtoms).openWires.length) + 2 :=
      Nat.add_lt_add_right indexInRange 2
    rw [Nat.add_right_comm bottomCount
        (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          firstAtoms).openWires.length 2] at step
    exact Nat.lt_of_le_of_lt (freshShiftLeAddDelta windowPosition 2 compositeIndex) step
  have shiftBoundSecond : freshShiftAbove windowPosition 2 compositeIndex
      < (bottomCount + 2)
        + (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            secondAtoms).openWires.length := by
    rw [← freshLengthAgree]; exact shiftBoundFirst
  have firstRead :
      internalEventCountAt
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            firstAtoms).links
          (List.range (bottomCount + 2)
            ++ (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              firstAtoms).openWires)
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            firstAtoms).capEventNodes
          (freshShiftAbove windowPosition 2 compositeIndex)
        = natListGetAt (arcStructureOfSpineList (bottomCount + 2) firstAtoms).internalCapCounts
            (freshShiftAbove windowPosition 2 compositeIndex) := by
    rw [arcInternalCapCountsUnfold (bottomCount + 2) firstAtoms]
    exact (natRangeMapGetAt _ _ _ shiftBoundFirst).symm
  have secondRead :
      internalEventCountAt
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            secondAtoms).links
          (List.range (bottomCount + 2)
            ++ (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              secondAtoms).openWires)
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            secondAtoms).capEventNodes
          (freshShiftAbove windowPosition 2 compositeIndex)
        = natListGetAt (arcStructureOfSpineList (bottomCount + 2) secondAtoms).internalCapCounts
            (freshShiftAbove windowPosition 2 compositeIndex) := by
    rw [arcInternalCapCountsUnfold (bottomCount + 2) secondAtoms]
    exact (natRangeMapGetAt _ _ _ shiftBoundSecond).symm
  rw [firstRead, secondRead]
  exact congrArg
    (fun theList => natListGetAt theList (freshShiftAbove windowPosition 2 compositeIndex))
    (congrArg FullArcStructure.internalCapCounts freshArcEqual)

/-! ## Honesty marker -/

/-- **Honesty marker — the cup tails-cancel's two INTERNAL count legs follow from FRESH-SEED ARC EQUALITY
(peel campaign H).**  `arcCupFoldedInternalCupCountList_agrees_ofFreshArcEqual` /
`…Cap…`: with the two fresh runs carrying equal arc structure at the `bottomCount + 2` seed (and a shared
fresh boundary length), the two folded internal cup- and cap-count lists coincide — because the fold's
per-index readoff is exactly the arc-structure `internalCupCounts` / `internalCapCounts` field entry, and
equal structures have equal fields.  This SHARPENS the residual map: the two internal count legs need only
arc-structure invariance (the shipped soundness), NOT the through-the-head orbit's `sameClassification`,
which is now owed by the DIAGRAM leg alone (its `partnerIndexOf` readoff is strictly finer than the
`.diagram` field).  What this marker does NOT claim: the fresh-seed arc equality itself (delivered by the
orbit's trace equivalence via arc invariance), nor the folded↔clean transport down to the seed.  `= true`. -/
def fxMode_hasArcCupFoldedInternalCountFreshArc : Bool := true

end FX1Poly.Polygraph
