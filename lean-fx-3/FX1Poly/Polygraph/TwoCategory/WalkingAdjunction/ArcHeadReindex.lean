import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPositionalShiftSim
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFreshShift

/-! # ArcHeadReindex — the concrete head reindexing at the peel's seed pair

The head cancellation compares the COMPOSITE run (the canonical seed at the head's source
boundary with the peeled head already fired) against the tail's FRESH run (the canonical seed
at the head's target boundary).  This brick pins the concrete `sigma` relating them: BELOW the
composite boundary's width an identifier reads off the composite's own post-head wire list; AT
or ABOVE it the identifier translates by the allocation delta.  Reading `sigma` off the wire
list (instead of a piecewise window formula) makes the seed `openMap` a single GENERIC
identity — any wire list is the reindex-image of the canonical range over its own length —
and the same builder serves the cup head (delta `1`) and the cap head (delta `3`).

Shipped: the builder, the above-width translation law, the generic range image, the two
boundary-width pins, and the two `ArcPositionalShiftSim` seed instantiations.

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

/-! ## The head reindexing builder -/

/-- **The head reindexing**: below the composite boundary's width the identifier reads off the
composite's post-head wire list; at or above it the identifier translates by the allocation
delta.  Because `sigma` is READ OFF the wire list, the seed `openMap` is a generic identity
(`arcHeadReindex_mapRange`) instead of a per-window piecewise computation. -/
def arcHeadReindex (compositeWires : List Nat) (freshDelta identifier : Nat) : Nat :=
  if identifier < compositeWires.length then natListGetAt compositeWires identifier
  else identifier + freshDelta

/-- Above the boundary width the reindexing is the plain translation — discharges the fold
kit's `sigmaShiftsAboveThreshold` hypothesis at `threshold := compositeWires.length`. -/
theorem arcHeadReindex_shiftsAboveLength (compositeWires : List Nat) (freshDelta : Nat)
    (identifier : Nat) (atLeast : compositeWires.length ≤ identifier) :
    arcHeadReindex compositeWires freshDelta identifier = identifier + freshDelta :=
  if_neg (fun below => Nat.lt_irrefl identifier (Nat.lt_of_lt_of_le below atLeast))

/-- ★ **The generic seed `openMap`**: ANY wire list is the reindex-image of the canonical
range over its own length — pointwise via the in-range getAt/map commutation and the range
read-off, glued by the pointwise-to-list bridge. -/
theorem arcHeadReindex_mapRange (compositeWires : List Nat) (freshDelta : Nat) :
    (List.range compositeWires.length).map (arcHeadReindex compositeWires freshDelta)
      = compositeWires := by
  apply natListEqOfPointwiseGetAt
  · rw [mapLength, rangeLength]
  · intro index indexBelow
    have belowLength : index < compositeWires.length := by
      rw [mapLength, rangeLength] at indexBelow
      exact indexBelow
    have rangeBound : index < (List.range compositeWires.length).length := by
      rw [rangeLength]
      exact belowLength
    rw [natListGetAt_map_inRange (arcHeadReindex compositeWires freshDelta)
        (List.range compositeWires.length) index rangeBound,
      rangeGetAt_below compositeWires.length index belowLength]
    exact if_pos belowLength

/-! ## The boundary-width pins at the two head shapes -/

/-- The post-cup boundary is two wider than the source boundary (unconditional — the splice
keeps every wire regardless of the window position). -/
theorem cupHeadOpenWires_length (bottomCount windowPosition : Nat) :
    (natListInsertAt (List.range bottomCount) windowPosition
      [bottomCount, bottomCount + 1]).length = bottomCount + 2 :=
  (natListInsertAt_length (List.range bottomCount) windowPosition
      [bottomCount, bottomCount + 1]).trans
    (congrArg (fun frontLength => frontLength + 2) (rangeLength bottomCount))

/-- The post-cap boundary is two narrower than the source boundary — stated additively
(`tailBoundary + 2 = bottomCount`), in range because the fire window fits the boundary. -/
theorem capHeadOpenWires_length (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount) :
    (natListRemoveTwoAt (List.range bottomCount) windowPosition).length = tailBoundary := by
  have removalShift := natListRemoveTwoAt_length (List.range bottomCount) windowPosition
    (by rw [rangeLength]; exact windowFits)
  exact natSumRightCancel 2
    (removalShift.trans ((rangeLength bottomCount).trans tailBoundaryFits.symm))

/-- The cup-head reindexing translates by `1` above the tail seed's boundary `bottomCount + 2`
— the fold kit's `sigmaShiftsAboveThreshold` at the cup seed. -/
theorem arcHeadReindex_cupSeedShifts (bottomCount windowPosition : Nat) :
    ∀ identifier, bottomCount + 2 ≤ identifier →
      arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1 identifier = identifier + 1 := by
  intro identifier atLeast
  exact arcHeadReindex_shiftsAboveLength
    (natListInsertAt (List.range bottomCount) windowPosition
      [bottomCount, bottomCount + 1]) 1 identifier
    (by rw [cupHeadOpenWires_length bottomCount windowPosition]; exact atLeast)

/-- The cap-head reindexing translates by `3` above the tail seed's boundary `tailBoundary` —
the fold kit's `sigmaShiftsAboveThreshold` at the cap seed. -/
theorem arcHeadReindex_capSeedShifts (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount) :
    ∀ identifier, tailBoundary ≤ identifier →
      arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3 identifier
        = identifier + 3 := by
  intro identifier atLeast
  exact arcHeadReindex_shiftsAboveLength
    (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3 identifier
    (by
      rw [capHeadOpenWires_length bottomCount windowPosition tailBoundary windowFits
        tailBoundaryFits]
      exact atLeast)

/-! ## The seed simulations at the two head shapes -/

/-- ★ **The cup-head seed simulation**: the composite run (canonical seed at `bottomCount`
with the peeled CUP fired at `windowPosition`) simulates the fresh tail run (canonical seed at
the cup's target boundary `bottomCount + 2`) under the cup-head reindexing — allocator one
ahead, the cup's event node `bottomCount + 2` as the head suffix. -/
theorem arcPositionalShiftSim_cupHeadSeed (bottomCount windowPosition : Nat) :
    ArcPositionalShiftSim
      (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1)
      1 (bottomCount + 2) [bottomCount + 2] []
      (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
      (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        windowPosition) := by
  refine
    { openMap := ?_
      nfShift := rfl
      nfFloor := Nat.le_refl (bottomCount + 2)
      cupEventsMap := rfl
      capEventsMap := rfl }
  show natListInsertAt (List.range bottomCount) windowPosition [bottomCount, bottomCount + 1]
      = (List.range (bottomCount + 2)).map
          (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
            [bottomCount, bottomCount + 1]) 1)
  rw [← cupHeadOpenWires_length bottomCount windowPosition]
  exact (arcHeadReindex_mapRange (natListInsertAt (List.range bottomCount) windowPosition
    [bottomCount, bottomCount + 1]) 1).symm

/-- ★ **The cap-head seed simulation**: the composite run (canonical seed at `bottomCount`
with the peeled CAP fired at a fitting `windowPosition`) simulates the fresh tail run
(canonical seed at the cap's target boundary `tailBoundary`, stated additively) under the
cap-head reindexing — allocator three ahead, the cap's event node `bottomCount` as the head
suffix. -/
theorem arcPositionalShiftSim_capHeadSeed (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount) :
    ArcPositionalShiftSim
      (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3)
      3 tailBoundary [] [bottomCount]
      (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
      (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        windowPosition) := by
  refine
    { openMap := ?_
      nfShift := congrArg (fun sourceBoundary => sourceBoundary + 1) tailBoundaryFits.symm
      nfFloor := Nat.le_refl tailBoundary
      cupEventsMap := rfl
      capEventsMap := rfl }
  show natListRemoveTwoAt (List.range bottomCount) windowPosition
      = (List.range tailBoundary).map
          (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3)
  rw [← capHeadOpenWires_length bottomCount windowPosition tailBoundary windowFits
    tailBoundaryFits]
  exact (arcHeadReindex_mapRange
    (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3).symm

/-! ## Honesty marker -/

/-- **Honesty marker — the concrete head reindexing at the peel's seed pair (peel campaign H,
seed rung, POSITIONAL leg).**  `arcHeadReindex` (read off the composite wire list, translate
above), the above-width law, the generic range image, the two boundary-width pins, the two
`sigmaShiftsAboveThreshold` seed discharges, and the two `ArcPositionalShiftSim` seed
instantiations (cup delta `1`, cap delta `3`).  What this marker does NOT claim: the seed
COMPONENT correspondence (`ArcComponentShiftCorr` at the head pair's links — the concrete
union-find computation), and the extract correspondence the cancellation consumes.  `= true`. -/
def fxMode_hasArcHeadReindexSeed : Bool := true

end FX1Poly.Polygraph
