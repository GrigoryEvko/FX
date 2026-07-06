import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupFoldedDiagramFold
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFreshShift

/-! # ArcCupFoldedDiagramFreshArc — the DIAGRAM leg from FRESH-SEED ARC EQUALITY (peel campaign H)

The companion of `ArcCupFoldedInternalCountFreshArc` for the diagram partner leg — and it retires the
`sameClassification` detour.  `ArcCupDiagramSameClassificationFold` reduced the diagram leg to the
through-the-head orbit's per-index leg-attachment classification (`arcCupFreshPartnerLandsOnWindowLeg`
iff), on the premise that the raw `partnerIndexOf` readoff is strictly finer than the `.diagram` field.
That premise is FALSE at the folded level:

DECISIVE OBSERVATION.  `extractDiagram` builds `partner := (List.range total).map (partnerIndexOf
state.links boundaryNodes total)` (MatchingDecision) — the SAME `(List.range total).map (…)` field shape
as `internalCupCounts`.  So the diagram fold's readoff `partnerIndexOf (fresh run).links (fresh boundary)
total (freshShiftAbove windowPosition 2 compositeIndex)` at an in-range index IS the `.diagram.partner`
field entry of `arcStructureOfSpineList (bottomCount + 2) (fresh run)` there.  Equal fresh arc structures
have equal `.diagram` fields, hence equal `.diagram.partner` lists, hence equal per-index partner readoffs
— the STRONGER per-index partner EQUALITY, not merely the window-leg classification iff.

So the diagram leg needs only FRESH-SEED ARC EQUALITY — exactly like the two count legs
(`ArcCupFoldedInternalCountFreshArc`).  All THREE folded legs of the cup tails-cancel now rest on the ONE
uniform premise `arcStructureOfSpineList (bottomCount + 2) firstAtoms = … secondAtoms` (a trace invariant
the orbit delivers via the shipped soundness).  The `sameClassification` re-selection — the "deep orbit
core" the earlier honesty markers named — is NOT on the critical path; the direct field route bypasses it.

  * `arcCupFoldedDiagramPartnerList_agrees_ofFreshArcEqual` — the diagram leg from fresh arc equality,
    feeding the raw per-index fold `arcCupFoldedDiagramPartnerList_agrees` (NOT the `_ofSameClassification`
    detour).

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
`mappedFunction index`. -/
private theorem natRangeMapGetAt (total : Nat) (mappedFunction : Nat → Nat) (index : Nat)
    (indexInRange : index < total) :
    natListGetAt ((List.range total).map mappedFunction) index = mappedFunction index := by
  rw [natListGetAt_map_inRange mappedFunction (List.range total) index
      (by rw [rangeLength total]; exact indexInRange),
    rangeGetAt_below total index indexInRange]

/-- The fresh shift lands at most `delta` above its argument. -/
private theorem freshShiftLeAddDelta (threshold delta identifier : Nat) :
    freshShiftAbove threshold delta identifier ≤ identifier + delta := by
  cases Nat.lt_or_ge identifier threshold with
  | inl isBelow =>
      rw [freshShiftAbove_ofNotLe threshold delta identifier (Nat.not_le_of_lt isBelow)]
      exact Nat.le_add_right identifier delta
  | inr isAtOrAbove =>
      exact Nat.le_of_eq (freshShiftAbove_ofLe threshold delta identifier isAtOrAbove)

/-- The `.diagram.partner` field of `arcStructureOfSpineList` IS the range-map of the fresh
`partnerIndexOf` readoff — definitional, straight from `extractDiagram`'s field. -/
private theorem arcDiagramPartnerUnfold {overallSource overallTarget : adjunctionGraph.Mode}
    (seed : Nat)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) :
    (arcStructureOfSpineList seed atoms).diagram.partner
      = (List.range
          (seed
            + (processArcSpine (ArcWireState.mk (List.range seed) [] seed 0 [] [])
                atoms).openWires.length)).map
          (partnerIndexOf
            (processArcSpine (ArcWireState.mk (List.range seed) [] seed 0 [] []) atoms).links
            (List.range seed
              ++ (processArcSpine (ArcWireState.mk (List.range seed) [] seed 0 [] []) atoms).openWires)
            (seed
              + (processArcSpine (ArcWireState.mk (List.range seed) [] seed 0 [] [])
                  atoms).openWires.length)) :=
  rfl

/-! ## The diagram leg from fresh-seed arc equality -/

/-- ★ **The folded diagram partner list agrees from fresh-seed arc equality.**  With the two fresh runs
(at the `bottomCount + 2` seed) carrying EQUAL arc structure and sharing a fresh boundary length, the two
folded partner lists coincide: the fold's per-index readoff at `freshShiftAbove windowPosition 2
compositeIndex` is exactly the `.diagram.partner` field entry there, and equal arc structures have equal
fields.  No `sameClassification` — this is the direct route, retiring the leg-attachment detour: the
diagram leg rides only the shipped soundness (arc invariance), the same premise as the two count legs. -/
theorem arcCupFoldedDiagramPartnerList_agrees_ofFreshArcEqual
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
          partnerIndexOf
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              firstAtoms).links
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
                firstAtoms).openWires)
            (bottomCount + 2
              + (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
                firstAtoms).openWires.length)
            (freshShiftAbove windowPosition 2 compositeIndex))
      = (List.range
            (bottomCount
              + (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
                firstAtoms).openWires.length)).map
          (fun compositeIndex =>
            partnerIndexOf
              (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
                secondAtoms).links
              (List.range (bottomCount + 2)
                ++ (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
                  secondAtoms).openWires)
              (bottomCount + 2
                + (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
                  secondAtoms).openWires.length)
              (freshShiftAbove windowPosition 2 compositeIndex)) := by
  apply arcCupFoldedDiagramPartnerList_agrees bottomCount windowPosition firstAtoms secondAtoms
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
      partnerIndexOf
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            firstAtoms).links
          (List.range (bottomCount + 2)
            ++ (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              firstAtoms).openWires)
          (bottomCount + 2
            + (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              firstAtoms).openWires.length)
          (freshShiftAbove windowPosition 2 compositeIndex)
        = natListGetAt (arcStructureOfSpineList (bottomCount + 2) firstAtoms).diagram.partner
            (freshShiftAbove windowPosition 2 compositeIndex) := by
    rw [arcDiagramPartnerUnfold (bottomCount + 2) firstAtoms]
    exact (natRangeMapGetAt _ _ _ shiftBoundFirst).symm
  have secondRead :
      partnerIndexOf
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            secondAtoms).links
          (List.range (bottomCount + 2)
            ++ (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              secondAtoms).openWires)
          (bottomCount + 2
            + (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              secondAtoms).openWires.length)
          (freshShiftAbove windowPosition 2 compositeIndex)
        = natListGetAt (arcStructureOfSpineList (bottomCount + 2) secondAtoms).diagram.partner
            (freshShiftAbove windowPosition 2 compositeIndex) := by
    rw [arcDiagramPartnerUnfold (bottomCount + 2) secondAtoms]
    exact (natRangeMapGetAt _ _ _ shiftBoundSecond).symm
  rw [firstRead, secondRead]
  exact congrArg
    (fun theList => natListGetAt theList (freshShiftAbove windowPosition 2 compositeIndex))
    (congrArg DiagramType.partner (congrArg FullArcStructure.diagram freshArcEqual))

/-! ## Honesty marker -/

/-- **Honesty marker — the cup tails-cancel's DIAGRAM leg follows from FRESH-SEED ARC EQUALITY, retiring the
`sameClassification` detour (peel campaign H).**  `arcCupFoldedDiagramPartnerList_agrees_ofFreshArcEqual`:
with the two fresh runs carrying equal arc structure at the `bottomCount + 2` seed (and a shared fresh
boundary length), the two folded partner lists coincide — because the fold's per-index readoff is exactly
the arc-structure `.diagram.partner` field entry (`extractDiagram` builds `partner := (List.range
total).map (partnerIndexOf …)`), and equal structures have equal fields.  This DEMOTES the earlier
`ArcCupDiagramSameClassificationFold` route: the diagram leg does NOT need the through-the-head orbit's
leg-attachment classification — it rides the same soundness (arc invariance) as the two count legs.  ALL
THREE folded legs of the cup tails-cancel now rest on the ONE uniform premise `arcStructureOfSpineList
(bottomCount + 2) firstAtoms = … secondAtoms`.  What this marker does NOT claim: the fresh-seed arc
equality itself (delivered by the orbit's trace equivalence via arc invariance), nor the folded↔clean
transport down to the seed.  `= true`. -/
def fxMode_hasArcCupFoldedDiagramFreshArc : Bool := true

end FX1Poly.Polygraph
