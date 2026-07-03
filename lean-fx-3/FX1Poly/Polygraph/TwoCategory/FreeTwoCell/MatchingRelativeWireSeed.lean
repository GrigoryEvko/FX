import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingRelativeWireSim
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingRightPadSeed

/-! # MatchingRelativeWireSeed — the mid-state wire map + seed instance (MODE3-D brick D2)

The concrete `sigma` the vcompRight leg runs on: read the mid-state's open wires
positionally below their count, land in the mid-state's fresh block above it.  Defined by
structural recursion on the wire list — subtraction-free, so both read lemmas close by
definitional arms:

* `relativeWireMap_readsBelow` — below the wire count the map reads the list positionally;
* `relativeWireMap_shiftsAbove` — at `count + offset` the map yields `freshBase + offset`,
  which is exactly the `MatchingRelativeWireSim.freshCorr` shape;
* `matchingRelativeWireSim_initial` — every state is relative-wire-simulated from its own
  canonical seed (`openMap` is the pointwise range read-off, `freshCorr` is the shift lemma
  verbatim), plus the boundary-tracked form `matchingRelativeWireSim_initial_ofTracks` the
  vcompRight assembly will consume at the post-α mid-state.

The dynamics layer (`links` / `loops` partition join) is the next MODE3-D brick. -/

namespace FX1Poly.Polygraph

/-! ## Range read plumbing (private copies — the seed files' kits are file-private) -/

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

/-! ## The mid-state wire map -/

/-- The mid-state wire map: read the wire list positionally below its count, land in the
fresh block (offset from `freshBase`) at or above it.  Structural recursion on the wire
list — subtraction-free. -/
def relativeWireMap : List Nat → Nat → Nat → Nat
  | [], freshBase, identifier => freshBase + identifier
  | wire :: _, _, 0 => wire
  | _ :: rest, freshBase, identifier + 1 => relativeWireMap rest freshBase identifier

/-- Below the wire count the map reads the wire list positionally. -/
theorem relativeWireMap_readsBelow : (wires : List Nat) → (freshBase index : Nat) →
    index < wires.length →
    relativeWireMap wires freshBase index = natListGetAt wires index
  | [], _, index, indexBelow => absurd indexBelow (Nat.not_succ_le_zero index)
  | _ :: _, _, 0, _ => rfl
  | _ :: rest, freshBase, index + 1, indexBelow =>
      relativeWireMap_readsBelow rest freshBase index (Nat.le_of_succ_le_succ indexBelow)

/-- At `count + offset` the map lands in the fresh block at `freshBase + offset` — exactly
the `MatchingRelativeWireSim.freshCorr` shape at the canonical seed. -/
theorem relativeWireMap_shiftsAbove : (wires : List Nat) → (freshBase offset : Nat) →
    relativeWireMap wires freshBase (wires.length + offset) = freshBase + offset
  | [], freshBase, offset => by
      show freshBase + (0 + offset) = freshBase + offset
      rw [Nat.zero_add]
  | wire :: rest, freshBase, offset => by
      show relativeWireMap (wire :: rest) freshBase (rest.length + 1 + offset)
        = freshBase + offset
      rw [Nat.add_right_comm rest.length 1 offset]
      exact relativeWireMap_shiftsAbove rest freshBase offset

/-! ## The seed instance -/

/-- ★ **Every state is relative-wire-simulated from its own canonical seed** under its own
mid-state wire map: the canonical range reads back the state's wires positionally
(`openMap`), and the canonical counter maps into the state's fresh block offset-for-offset
(`freshCorr` is `relativeWireMap_shiftsAbove` verbatim). -/
theorem matchingRelativeWireSim_initial (midState : WireState) :
    MatchingRelativeWireSim (relativeWireMap midState.openWires midState.nextFresh)
      (canonicalMatchingSeed midState.openWires.length) midState := by
  have openMapProof : midState.openWires
      = (canonicalMatchingSeed midState.openWires.length).openWires.map
          (relativeWireMap midState.openWires midState.nextFresh) := by
    show midState.openWires
      = (List.range midState.openWires.length).map
          (relativeWireMap midState.openWires midState.nextFresh)
    apply natListEqOfPointwiseGetAt
    · rw [mapLength, rangeLength]
    · intro index indexInRange
      rw [natListGetAt_map_inRange
          (relativeWireMap midState.openWires midState.nextFresh)
          (List.range midState.openWires.length) index
          (by rw [rangeLength]; exact indexInRange),
        rangeGetAt_below midState.openWires.length index indexInRange,
        relativeWireMap_readsBelow midState.openWires midState.nextFresh index indexInRange]
  exact { openMap := openMapProof
          freshCorr := fun offset =>
            relativeWireMap_shiftsAbove midState.openWires midState.nextFresh offset }

/-- The seed instance at an abstract interface count — the boundary-tracked form the
vcompRight assembly consumes at the post-α mid-state. -/
theorem matchingRelativeWireSim_initial_ofTracks (midState : WireState)
    (interfaceCount : Nat) (tracks : midState.openWires.length = interfaceCount) :
    MatchingRelativeWireSim (relativeWireMap midState.openWires midState.nextFresh)
      (canonicalMatchingSeed interfaceCount) midState :=
  tracks ▸ matchingRelativeWireSim_initial midState

/-! ## Honesty marker -/

/-- **Honesty marker — the mid-state wire map + seed instance are SHIPPED (MODE3-D brick
D2).**  The concrete `sigma` (positional read below the count, fresh-block shift above it,
subtraction-free) with both read lemmas, and every state relative-wire-simulated from its
own canonical seed — including the boundary-tracked form.  NOT yet shipped: the DYNAMICS
layer — the `links` / `loops` partition-join invariant the vcompRight / Joyal–Street leg
turns on.  `= true`. -/
def fxMode_hasMatchingRelativeWireSeed : Bool := true

end FX1Poly.Polygraph
