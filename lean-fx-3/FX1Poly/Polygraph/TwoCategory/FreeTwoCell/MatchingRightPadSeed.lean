import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingRightPadSim

/-! # MatchingRightPadSeed — the canonical seeds are right-pad-simulated

`matchingOf (whiskerRight oneCell alpha)` runs `alpha`'s own spine (the action-invisibility of
`MatchingSpineActionCongruence`) from the canonical seed at the PADDED bottom boundary
`|F| + |oneCell|`, while `matchingOf alpha` runs the same spine from the canonical seed at `|F|`.
This file inhabits `MatchingRightPadSim` at that seed pair:

* `freshShiftAbove_beqCongr` — the shift is boolean-equality-reflecting (below-threshold ids are
  fixed, at-or-above ids translate rigidly, and the mixed case is `false` on both sides);
* `padIdentifiers` — the pad suffix `[threshold, …, threshold + delta - 1]` with its length and
  read characterizations;
* `paddedRangeSplit` — `List.range (bottomCount + pad)` IS the shift-image of
  `List.range bottomCount` followed by the pad suffix (pointwise reads);
* `canonicalMatchingSeed` + `matchingRightPadSim_initial` — the seed pair is pad-simulated, so
  the boundary-disciplined fold of `MatchingRightPadSim` carries the simulation through any
  shared spine.

The remaining `whiskerRightCongruent` steps are the padded-boundary view read-off and the field
assembly — the next bricks. -/

namespace FX1Poly.Polygraph

/-! ## The shift reflects boolean equality -/

private theorem natBeqSuccCongr (a b : Nat) : ((a + 1 == b + 1) = (a == b)) := by
  cases Nat.decEq a b with
  | isTrue areEqual =>
      rw [areEqual]
      exact (decide_eq_true rfl).trans (decide_eq_true rfl).symm
  | isFalse notEqual =>
      exact (decide_eq_false (fun succEq => notEqual (Nat.succ.inj succEq))).trans
        (decide_eq_false notEqual).symm

private theorem natBeqAddCongr (a b : Nat) : (delta : Nat) →
    ((a + delta == b + delta) = (a == b))
  | 0 => rfl
  | delta + 1 => (natBeqSuccCongr (a + delta) (b + delta)).trans (natBeqAddCongr a b delta)

/-- ★ **The fresh shift reflects boolean equality.**  Below-threshold identifiers are fixed,
at-or-above identifiers translate rigidly by `delta`, and a mixed pair is unequal both before
and after the shift (the below side stays strictly below the threshold, the other side stays
at or above it). -/
theorem freshShiftAbove_beqCongr (threshold delta a b : Nat) :
    (freshShiftAbove threshold delta a == freshShiftAbove threshold delta b) = (a == b) := by
  cases Nat.decLe threshold a with
  | isTrue aAtOrAbove =>
      rw [freshShiftAbove_ofLe threshold delta a aAtOrAbove]
      cases Nat.decLe threshold b with
      | isTrue bAtOrAbove =>
          rw [freshShiftAbove_ofLe threshold delta b bAtOrAbove]
          exact natBeqAddCongr a b delta
      | isFalse bNotAtOrAbove =>
          rw [freshShiftAbove_ofNotLe threshold delta b bNotAtOrAbove]
          have bStrictlyBelow : b < threshold := by
            cases Nat.lt_or_ge b threshold with
            | inl isBelow => exact isBelow
            | inr atOrAbove => exact absurd atOrAbove bNotAtOrAbove
          have bLtPlain : b < a := Nat.lt_of_lt_of_le bStrictlyBelow aAtOrAbove
          have bLtShifted : b < a + delta :=
            Nat.lt_of_lt_of_le bLtPlain (Nat.le_add_right a delta)
          have shiftedNe : (a + delta == b) = false :=
            decide_eq_false (fun mixedEq => Nat.lt_irrefl b (mixedEq ▸ bLtShifted))
          have plainNe : (a == b) = false :=
            decide_eq_false (fun mixedEq => Nat.lt_irrefl b (mixedEq ▸ bLtPlain))
          rw [shiftedNe, plainNe]
  | isFalse aNotAtOrAbove =>
      rw [freshShiftAbove_ofNotLe threshold delta a aNotAtOrAbove]
      cases Nat.decLe threshold b with
      | isTrue bAtOrAbove =>
          rw [freshShiftAbove_ofLe threshold delta b bAtOrAbove]
          have aStrictlyBelow : a < threshold := by
            cases Nat.lt_or_ge a threshold with
            | inl isBelow => exact isBelow
            | inr atOrAbove => exact absurd atOrAbove aNotAtOrAbove
          have aLtPlain : a < b := Nat.lt_of_lt_of_le aStrictlyBelow bAtOrAbove
          have aLtShifted : a < b + delta :=
            Nat.lt_of_lt_of_le aLtPlain (Nat.le_add_right b delta)
          have shiftedNe : (a == b + delta) = false :=
            decide_eq_false
              (fun mixedEq => Nat.lt_irrefl (b + delta) (mixedEq ▸ aLtShifted))
          have plainNe : (a == b) = false :=
            decide_eq_false (fun mixedEq => Nat.lt_irrefl b (mixedEq ▸ aLtPlain))
          rw [shiftedNe, plainNe]
      | isFalse bNotAtOrAbove =>
          rw [freshShiftAbove_ofNotLe threshold delta b bNotAtOrAbove]

/-! ## Range and append read plumbing (hand-rolled, propext-free) -/

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

private theorem natListAppendLength : (block : List Nat) → (wires : List Nat) →
    (block ++ wires).length = block.length + wires.length
  | [], wires => (Nat.zero_add wires.length).symm
  | _ :: blockRest, wires => by
      show (blockRest ++ wires).length + 1 = blockRest.length + 1 + wires.length
      rw [natListAppendLength blockRest wires,
        Nat.add_right_comm blockRest.length wires.length 1]

/-- Read PAST a block of known length: the append defers to the suffix.  The block length is
threaded as an equation so the caller never rewrites inside its own goal. -/
private theorem natListGetAt_append_atLength : (block : List Nat) → (wires : List Nat) →
    (blockLength offset : Nat) → block.length = blockLength →
    natListGetAt (block ++ wires) (blockLength + offset) = natListGetAt wires offset
  | [], wires, blockLength, offset, lengthEq => by
      rw [← lengthEq]
      show natListGetAt wires (0 + offset) = natListGetAt wires offset
      rw [Nat.zero_add]
  | head :: blockRest, wires, blockLength, offset, lengthEq => by
      rw [← lengthEq]
      show natListGetAt (head :: (blockRest ++ wires)) (blockRest.length + 1 + offset)
        = natListGetAt wires offset
      rw [Nat.add_right_comm blockRest.length 1 offset]
      exact natListGetAt_append_atLength blockRest wires blockRest.length offset rfl

/-! ## The pad suffix -/

/-- The pad suffix `[start, start + 1, …, start + count - 1]` — the identifiers the padded
canonical seed carries beyond the base boundary. -/
def padIdentifiers : Nat → Nat → List Nat
  | _, 0 => []
  | start, count + 1 => start :: padIdentifiers (start + 1) count

/-- The pad suffix has exactly `count` identifiers. -/
theorem padIdentifiers_length : (start count : Nat) →
    (padIdentifiers start count).length = count
  | _, 0 => rfl
  | start, count + 1 => congrArg (· + 1) (padIdentifiers_length (start + 1) count)

/-- Reading the pad suffix at an in-range offset yields `start + offset`. -/
theorem padIdentifiers_getAt : (start count offset : Nat) → offset < count →
    natListGetAt (padIdentifiers start count) offset = start + offset
  | _, 0, _, offsetLt => absurd offsetLt (Nat.not_succ_le_zero _)
  | _, _ + 1, 0, _ => rfl
  | start, count + 1, offset + 1, offsetLt => by
      have inner := padIdentifiers_getAt (start + 1) count offset
        (Nat.le_of_succ_le_succ offsetLt)
      rw [Nat.add_right_comm start 1 offset] at inner
      exact inner

/-! ## The padded range splits as shift-image plus pad suffix -/

/-- ★ **The padded canonical wire list IS the shift-image of the base wire list followed by
the pad suffix** — pointwise: below the boundary both sides read the identity (the shift fixes
below-threshold ids), at or past it the padded range keeps counting while the append defers to
the pad suffix. -/
theorem paddedRangeSplit (bottomCount pad : Nat) :
    List.range (bottomCount + pad)
      = (List.range bottomCount).map (freshShiftAbove bottomCount pad)
          ++ padIdentifiers bottomCount pad := by
  have mapRangeLength :
      ((List.range bottomCount).map (freshShiftAbove bottomCount pad)).length
        = bottomCount := by
    rw [mapLength, rangeLength]
  apply natListEqOfPointwiseGetAt
  · rw [rangeLength, natListAppendLength, mapRangeLength, padIdentifiers_length]
  · intro index indexInRange
    rw [rangeLength] at indexInRange
    cases Nat.lt_or_ge index bottomCount with
    | inl belowBottom =>
        rw [rangeGetAt_below (bottomCount + pad) index
            (Nat.lt_of_lt_of_le belowBottom (Nat.le_add_right bottomCount pad)),
          natListGetAt_append_inside _ (padIdentifiers bottomCount pad) index
            (by rw [mapRangeLength]; exact belowBottom),
          natListGetAt_map_inRange (freshShiftAbove bottomCount pad) (List.range bottomCount)
            index (by rw [rangeLength]; exact belowBottom),
          rangeGetAt_below bottomCount index belowBottom,
          freshShiftAbove_ofNotLe bottomCount pad index
            (fun atOrAbove =>
              Nat.lt_irrefl index (Nat.lt_of_lt_of_le belowBottom atOrAbove))]
    | inr atOrAboveBottom =>
        cases Nat.le.dest atOrAboveBottom with
        | intro offset offsetEq =>
            have sumBound : bottomCount + offset < bottomCount + pad := by
              rw [offsetEq]
              exact indexInRange
            have offsetLt : offset < pad := Nat.lt_of_add_lt_add_left sumBound
            rw [← offsetEq,
              rangeGetAt_below (bottomCount + pad) (bottomCount + offset) sumBound,
              natListGetAt_append_atLength
                ((List.range bottomCount).map (freshShiftAbove bottomCount pad))
                (padIdentifiers bottomCount pad) bottomCount offset mapRangeLength,
              padIdentifiers_getAt bottomCount pad offset offsetLt]

/-! ## The canonical seeds are pad-simulated -/

/-- The canonical matching seed at a bottom boundary: identity wires, no links, counter at the
boundary count, no loops — the state `matchingOfSpineList` starts from. -/
def canonicalMatchingSeed (bottomCount : Nat) : WireState :=
  { openWires := List.range bottomCount, links := [], nextFresh := bottomCount, loops := 0 }

/-- `matchingOfSpineList` IS the extract after processing from the canonical seed —
definitional read-off. -/
theorem matchingOfSpineList_ofCanonicalSeed {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} (bottomCount : Nat)
    (atoms : List (SpineAtom signature sourceMode targetMode)) :
    matchingOfSpineList bottomCount atoms
      = extractAfterProcessing bottomCount (canonicalMatchingSeed bottomCount) atoms := rfl

/-- ★ **The canonical seed pair is right-pad-simulated.**  Empty links make every root its own
node, so the component view is exactly the shift's boolean-equality reflection; the wire split
is `paddedRangeSplit`; counters, loops, forests, and the pad-zone invariants are definitional. -/
theorem matchingRightPadSim_initial (bottomCount pad : Nat) :
    MatchingRightPadSim bottomCount pad (padIdentifiers bottomCount pad)
      (canonicalMatchingSeed bottomCount) (canonicalMatchingSeed (bottomCount + pad)) :=
  { openMap := paddedRangeSplit bottomCount pad
    nfShift := rfl
    thresholdLe := Nat.le_refl bottomCount
    componentComm := fun a b => freshShiftAbove_beqCongr bottomCount pad a b
    loopsEq := rfl
    forestS := True.intro
    forestT := True.intro
    padRootsFixed := fun _ _ _ => rfl
    rootAvoidsPad := fun _ avoids => avoids }

/-! ## Honesty marker -/

/-- **Honesty marker — the right-pad simulation has its seed instance.**  The shift reflects
boolean equality (`freshShiftAbove_beqCongr`), the padded canonical wire list splits as
shift-image plus pad suffix (`paddedRangeSplit`), and the canonical seed pair at boundaries
`bottomCount` and `bottomCount + pad` inhabits `MatchingRightPadSim`
(`matchingRightPadSim_initial`) — so the boundary-disciplined fold carries the simulation
through any shared spine.  NOT yet shipped: the padded-boundary view read-off and the
`whiskerRightCongruent` assembly — the next MODE3-C bricks.  `= true`. -/
def fxMode_hasMatchingRightPadSeed : Bool := true

end FX1Poly.Polygraph
