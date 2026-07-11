import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcCrossingFaithfulStep
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFreshShift
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapRenameable

/-! # MODE-COMMUTE — the faithful crossing acts on the extract by a boundary-index TRANSPOSITION

`ArcCrossingFaithfulStep` (r7) shipped the corrected `2⇒2` crossing arm as an additive sibling: `stepCrossArc`
transposes the two live open wires at `position`, preserving width and leaving the union-find forest, `nextFresh`
and the cup/cap event lists untouched.  It witnessed the crossing OBSERVABLE (`crossing_observable_extract_ne`)
on different-component strands and INVISIBLE on same-component ports, but it did not name HOW the crossing acts on
`extractArc`.

This file lands the EQUIVARIANCE TRANSPORT: the crossing acts on the extract by the adjacent transposition
`transposeAdjacent (bottomCount + position)` of the boundary indices `bottomCount + position` and
`bottomCount + position + 1`.  Concretely, for the reachable window `position + 1 < openWires.length`:

  ★ **Per-index (the clean carrier, UNCONDITIONAL).**  Reading the crossed boundary at `index` equals reading the
    uncrossed boundary at the transposed index (`natListGetAt_boundaryNodes_stepCrossArc`).  Hence the per-port
    internal cup/cap counts are σ-EQUIVARIANT (`crossInternalEventCountAt_equivariant`) and the boundary
    same-component relation is σ-conjugate (`crossBoundarySameComponent_equivariant`), for EVERY state.

  ★ **Whole-list count-field swap (the headline, UNCONDITIONAL).**
    `(extractArc bc (stepCrossArc st p)).internalCupCounts = natListSwapTwoAt (extractArc bc st).internalCupCounts
    (bc + p)` (`internalCupCounts_stepCrossArc_eq_swap`, and the cap dual).  The crossing SWAPS the two count
    entries at the crossed boundary indices — exactly the observability the r7 probes witnessed, now proved
    general.  `cupCount` / `capCount` / `loops` are invariant (`rfl`).

## Where it JAMS — the partner field needs the perfect-matching regime (the r9 arm)

The `diagram.partner` field is σ-CONJUGATE (positions permuted by σ AND values remapped by σ) ONLY when every
boundary component holds ≤ 2 ports — i.e. the diagram is a genuine perfect matching (the shipped
`ArcPerfectMatchingTokens` invariant).  Off that regime the conjugation is FALSE, because `findPartnerScan`
returns the MIN-index match and min-index does not commute with an adjacent transposition once a component holds
> 2 ports.  This is a THEOREM here, not a hope: `crossing_triComponent_partner_ne_conjugate` REFUTES the partner
conjugation on a three-port component; `crossing_paired_partner_eq_conjugate` confirms it on a genuine matching.
So `fxMode_hasArcCrossingPartnerEquivariantTransport` stays `false` — the partner half is the r9 arm, threading
`ArcPerfectMatchingTokens` through the shipped Brauer involution machinery.

## What this file does NOT do (the pins stay false)

It does NOT wire the faithful crossing into `arcSwapCorePackage_of_adjunctionSwap` and it does NOT flip the
general-signature keystone.  `fxMode_hasArcPeelGeneralSignature` and the #2043 / WP-AMALG residual
`fxMode_hasArcGodementSamePartitionFreshProof` stay `false`; the shipped `stepArcAtom` / `extractArc` are never
edited.  This certificate is ADDITIVE.

Raw Lean 4 + Init; structural / fuel recursion, no `omega` / `simp`-AC / `WellFounded.fix`.  The transposition
`transposeAdjacent` is defined by joint structural recursion (no `==`, no `if`), so its equations are `rfl`-clean
and `propext`-free.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private plumbing (per-file copies, following the codebase pattern) -/

/-- Right cancellation for `≤` (core `Nat.le_of_add_le_add_right` is avoided for self-containment). -/
private theorem natLeOfAddLeAddRight : (cancelled : Nat) → {leftSum rightSum : Nat} →
    leftSum + cancelled ≤ rightSum + cancelled → leftSum ≤ rightSum
  | 0, _, _, sumsLe => sumsLe
  | cancelled + 1, _, _, sumsLe => natLeOfAddLeAddRight cancelled (Nat.le_of_succ_le_succ sumsLe)

/-- `<` implies `≠` (hand-rolled to avoid any name-drift on the core lemma). -/
private theorem natNeOfLt {first second : Nat} (isLess : first < second) : first ≠ second :=
  fun areEqual => Nat.lt_irrefl second (areEqual ▸ isLess)

/-- `List.range.loop count acc` has length `count + acc.length`. -/
private theorem rangeLoopLength : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLength count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1, Nat.add_right_comm count accumulated.length 1]

/-- `(List.range count).length = count`. -/
private theorem rangeLength (count : Nat) : (List.range count).length = count :=
  rangeLoopLength count []

/-- Reading `List.range.loop` past its produced block reads the accumulator. -/
private theorem rangeLoopGetAt_past : (count : Nat) → (accumulated : List Nat) → (offset : Nat) →
    natListGetAt (List.range.loop count accumulated) (offset + count) = natListGetAt accumulated offset
  | 0, _, _ => rfl
  | count + 1, accumulated, offset => by
      have inner := rangeLoopGetAt_past count (count :: accumulated) (offset + 1)
      rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
      exact inner

/-- Reading `List.range.loop` below its bound returns the index. -/
private theorem rangeLoopGetAt_below : (count : Nat) → (accumulated : List Nat) → (index : Nat) →
    index < count → natListGetAt (List.range.loop count accumulated) index = index
  | 0, _, _, indexBelow => absurd indexBelow (Nat.not_succ_le_zero _)
  | count + 1, accumulated, index, indexBelow => by
      cases Nat.lt_or_ge index count with
      | inl below => exact rangeLoopGetAt_below count (count :: accumulated) index below
      | inr atLeast =>
          have indexEq : index = count := Nat.le_antisymm (Nat.le_of_succ_le_succ indexBelow) atLeast
          have pastRead := rangeLoopGetAt_past count (count :: accumulated) 0
          rw [Nat.zero_add count] at pastRead
          rw [indexEq]
          exact pastRead

/-- Reading `List.range count` below `count` returns the index. -/
private theorem rangeGetAt_below (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  rangeLoopGetAt_below count [] index indexBelow

/-- `List.map` preserves length. -/
private theorem listMapLength {elementType resultType : Type} (mapFunction : elementType → resultType) :
    (entries : List elementType) → (entries.map mapFunction).length = entries.length
  | [] => rfl
  | _ :: rest => congrArg Nat.succ (listMapLength mapFunction rest)

/-- Reading a range-prefixed boundary below the prefix returns the index (assembled from the shipped
`natListGetAt_append_inside` and the range read-off, so no extra import). -/
private theorem natListGetAt_rangeAppendBelow (count : Nat) (wires : List Nat) (index : Nat)
    (indexBelow : index < count) :
    natListGetAt (List.range count ++ wires) index = index := by
  have inBlock : index < (List.range count).length := by rw [rangeLength]; exact indexBelow
  exact (natListGetAt_append_inside (List.range count) wires index inBlock).trans
    (rangeGetAt_below count index indexBelow)

/-! ## The adjacent transposition on boundary indices (no `==`, no `if` — structural)

`transposeAdjacent pivot target` swaps `pivot` and `pivot + 1`, fixing every other index.  Defined by joint
structural recursion so each equation is `rfl`-clean and `propext`-free. -/

/-- The adjacent transposition swapping `pivot` and `pivot + 1`. -/
def transposeAdjacent : Nat → Nat → Nat
  | 0, 0 => 1
  | 0, 1 => 0
  | 0, target + 2 => target + 2
  | _ + 1, 0 => 0
  | pivot + 1, target + 1 => transposeAdjacent pivot target + 1

/-- The transposition sends `pivot` to `pivot + 1`. -/
theorem transposeAdjacent_pivot : (pivot : Nat) → transposeAdjacent pivot pivot = pivot + 1
  | 0 => rfl
  | pivot + 1 => by
      show transposeAdjacent pivot pivot + 1 = pivot + 1 + 1
      rw [transposeAdjacent_pivot pivot]

/-- The transposition sends `pivot + 1` to `pivot`. -/
theorem transposeAdjacent_succ : (pivot : Nat) → transposeAdjacent pivot (pivot + 1) = pivot
  | 0 => rfl
  | pivot + 1 => by
      show transposeAdjacent pivot (pivot + 1) + 1 = pivot + 1
      rw [transposeAdjacent_succ pivot]

/-- The transposition fixes every index that is neither `pivot` nor `pivot + 1`. -/
theorem transposeAdjacent_other : (pivot target : Nat) →
    target ≠ pivot → target ≠ pivot + 1 → transposeAdjacent pivot target = target
  | 0, 0, notPivot, _ => absurd rfl notPivot
  | 0, 1, _, notSucc => absurd rfl notSucc
  | 0, _ + 2, _, _ => rfl
  | _ + 1, 0, _, _ => rfl
  | pivot + 1, target + 1, notPivot, notSucc => by
      show transposeAdjacent pivot target + 1 = target + 1
      rw [transposeAdjacent_other pivot target
        (fun areEqual => notPivot (congrArg (· + 1) areEqual))
        (fun areEqual => notSucc (congrArg (· + 1) areEqual))]

/-- The transposition's image is always one of `pivot + 1`, `pivot`, or the argument itself. -/
theorem transposeAdjacent_cases : (pivot target : Nat) →
    transposeAdjacent pivot target = pivot + 1 ∨ transposeAdjacent pivot target = pivot
      ∨ transposeAdjacent pivot target = target
  | 0, 0 => Or.inl rfl
  | 0, 1 => Or.inr (Or.inl rfl)
  | 0, _ + 2 => Or.inr (Or.inr rfl)
  | _ + 1, 0 => Or.inr (Or.inr rfl)
  | pivot + 1, target + 1 => by
      show transposeAdjacent pivot target + 1 = pivot + 1 + 1
        ∨ transposeAdjacent pivot target + 1 = pivot + 1
        ∨ transposeAdjacent pivot target + 1 = target + 1
      rcases transposeAdjacent_cases pivot target with atPivot | atPivotBase | atTarget
      · exact Or.inl (by rw [atPivot])
      · exact Or.inr (Or.inl (by rw [atPivotBase]))
      · exact Or.inr (Or.inr (by rw [atTarget]))

/-- The transposition preserves the bound: if the argument and `pivot + 1` are below `bound`, so is the image. -/
theorem transposeAdjacent_lt (pivot target bound : Nat)
    (targetBound : target < bound) (pivotBound : pivot + 1 < bound) :
    transposeAdjacent pivot target < bound := by
  rcases transposeAdjacent_cases pivot target with atPivot | atPivotBase | atTarget
  · rw [atPivot]; exact pivotBound
  · rw [atPivotBase]; exact Nat.lt_of_succ_lt pivotBound
  · rw [atTarget]; exact targetBound

/-- The transposition commutes with a left shift: transposing `offset + ·` at pivot `offset + pivot` is
`offset +` transposing at pivot `pivot`. -/
theorem transposeAdjacent_addLeft : (offset pivot target : Nat) →
    transposeAdjacent (offset + pivot) (offset + target) = offset + transposeAdjacent pivot target
  | 0, pivot, target => by
      rw [Nat.zero_add pivot, Nat.zero_add target, Nat.zero_add (transposeAdjacent pivot target)]
  | offset + 1, pivot, target => by
      rw [Nat.add_right_comm offset 1 pivot, Nat.add_right_comm offset 1 target]
      show transposeAdjacent (offset + pivot) (offset + target) + 1
        = offset + 1 + transposeAdjacent pivot target
      rw [transposeAdjacent_addLeft offset pivot target,
        Nat.add_right_comm offset (transposeAdjacent pivot target) 1]

/-! ## The swap preserves length, and reads at the transposed index (the ANCHOR) -/

/-- An in-window adjacent-transposition swap preserves the list length. -/
theorem natListSwapTwoAt_length (wires : List Nat) (position : Nat)
    (window : position + 1 < wires.length) :
    (natListSwapTwoAt wires position).length = wires.length := by
  show (natListInsertAt (natListRemoveTwoAt wires position) position
      [natListGetAt wires (position + 1), natListGetAt wires position]).length = wires.length
  rw [natListInsertAt_length]
  show (natListRemoveTwoAt wires position).length + 2 = wires.length
  exact natListRemoveTwoAt_length wires position window

/-- ★ **The bare anchor: reading the swapped list at `index` equals reading the original at the transposed
index.**  Four zones (below the window, at the two swapped positions, past the window) reuse the shipped
`natListInsertAt` / `natListRemoveTwoAt` window lemmas; the transposition value is read off `transposeAdjacent`'s
equational lemmas.  Window `position + 1 < wires.length`. -/
theorem natListGetAt_natListSwapTwoAt (wires : List Nat) (position index : Nat)
    (window : position + 1 < wires.length) :
    natListGetAt (natListSwapTwoAt wires position) index
      = natListGetAt wires (transposeAdjacent position index) := by
  have pairInRange : position + 2 ≤ wires.length := window
  have removeLen : (natListRemoveTwoAt wires position).length + 2 = wires.length :=
    natListRemoveTwoAt_length wires position pairInRange
  have positionLeRemove : position ≤ (natListRemoveTwoAt wires position).length := by
    have padded : position + 2 ≤ (natListRemoveTwoAt wires position).length + 2 := by
      rw [removeLen]; exact pairInRange
    exact natLeOfAddLeAddRight 2 padded
  show natListGetAt (natListInsertAt (natListRemoveTwoAt wires position) position
      [natListGetAt wires (position + 1), natListGetAt wires position]) index
    = natListGetAt wires (transposeAdjacent position index)
  rcases Nat.lt_or_ge index position with belowPosition | atLeastPosition
  · rw [natListGetAt_natListInsertAt_below (natListRemoveTwoAt wires position) position
        [natListGetAt wires (position + 1), natListGetAt wires position] index belowPosition
        (Nat.lt_of_lt_of_le belowPosition positionLeRemove),
      natListGetAt_natListRemoveTwoAt_below wires position index belowPosition,
      transposeAdjacent_other position index (natNeOfLt belowPosition)
        (natNeOfLt (Nat.lt_trans belowPosition (Nat.lt_succ_self position)))]
  · rcases Nat.lt_or_ge index (position + 1) with belowSucc | atLeastSucc
    · have indexEq : index = position := Nat.le_antisymm (Nat.le_of_lt_succ belowSucc) atLeastPosition
      rw [indexEq, transposeAdjacent_pivot position]
      exact natListGetAt_natListInsertAt_inside (natListRemoveTwoAt wires position) position
        [natListGetAt wires (position + 1), natListGetAt wires position] 0 (Nat.succ_pos 1) positionLeRemove
    · rcases Nat.lt_or_ge index (position + 2) with belowTwo | atLeastTwo
      · have indexEq : index = position + 1 :=
          Nat.le_antisymm (Nat.le_of_lt_succ belowTwo) atLeastSucc
        rw [indexEq, transposeAdjacent_succ position]
        exact natListGetAt_natListInsertAt_inside (natListRemoveTwoAt wires position) position
          [natListGetAt wires (position + 1), natListGetAt wires position] 1 (Nat.lt_succ_self 1) positionLeRemove
      · obtain ⟨offset, offsetEq⟩ := Nat.le.dest atLeastTwo
        have indexEq : index = position + offset + 2 := by
          rw [← offsetEq, Nat.add_right_comm position 2 offset]
        rw [indexEq]
        have posLt : position < position + offset + 2 := by
          have base : position + 0 < position + (offset + 2) :=
            Nat.add_lt_add_left (Nat.succ_pos (offset + 1)) position
          rw [Nat.add_zero, ← Nat.add_assoc] at base
          exact base
        have posSuccLt : position + 1 < position + offset + 2 := by
          have base : position + 1 < position + (offset + 2) :=
            Nat.add_lt_add_left (Nat.succ_lt_succ (Nat.succ_pos offset)) position
          rw [← Nat.add_assoc] at base
          exact base
        rw [transposeAdjacent_other position (position + offset + 2)
          (natNeOfLt posLt).symm (natNeOfLt posSuccLt).symm]
        exact (natListGetAt_natListInsertAt_pastBlock (natListRemoveTwoAt wires position) position
            [natListGetAt wires (position + 1), natListGetAt wires position] offset positionLeRemove).trans
          (natListGetAt_natListRemoveTwoAt_pastPair wires position offset pairInRange)

/-! ## The boundary-prefixed anchor -/

/-- Reading a range-prefixed boundary past the prefix reads the tail. -/
theorem natListGetAt_rangeAppend_pastRange (bottomCount : Nat) (wires : List Nat) (offset : Nat) :
    natListGetAt (List.range bottomCount ++ wires) (bottomCount + offset) = natListGetAt wires offset := by
  have base := natListGetAt_append_pastBlock (List.range bottomCount) wires offset
  rw [rangeLength] at base
  rw [Nat.add_comm bottomCount offset]
  exact base

/-- ★ **The boundary-prefixed anchor.**  With the range prefix of length `bottomCount`, reading the crossed
boundary at `index` equals reading the uncrossed boundary at `transposeAdjacent (bottomCount + position) index`:
below the prefix both read the index itself (the transposition fixes it), past the prefix the bare anchor and the
left-shift law (`transposeAdjacent_addLeft`) align. -/
theorem natListGetAt_boundaryNodes_stepCrossArc (bottomCount : Nat) (wires : List Nat)
    (position index : Nat) (window : position + 1 < wires.length) :
    natListGetAt (List.range bottomCount ++ natListSwapTwoAt wires position) index
      = natListGetAt (List.range bottomCount ++ wires)
          (transposeAdjacent (bottomCount + position) index) := by
  rcases Nat.lt_or_ge index bottomCount with belowBottom | atLeastBottom
  · rw [natListGetAt_rangeAppendBelow bottomCount (natListSwapTwoAt wires position) index belowBottom,
      transposeAdjacent_other (bottomCount + position) index
        (natNeOfLt (Nat.lt_of_lt_of_le belowBottom (Nat.le_add_right bottomCount position)))
        (natNeOfLt (Nat.lt_of_lt_of_le belowBottom
          (Nat.le_trans (Nat.le_add_right bottomCount position)
            (Nat.le_succ (bottomCount + position))))),
      natListGetAt_rangeAppendBelow bottomCount wires index belowBottom]
  · obtain ⟨innerIndex, innerEq⟩ := Nat.le.dest atLeastBottom
    subst innerEq
    rw [natListGetAt_rangeAppend_pastRange bottomCount (natListSwapTwoAt wires position) innerIndex,
      natListGetAt_natListSwapTwoAt wires position innerIndex window,
      transposeAdjacent_addLeft bottomCount position innerIndex,
      natListGetAt_rangeAppend_pastRange bottomCount wires (transposeAdjacent position innerIndex)]

/-! ## Per-index equivariance of the extract's connectivity reads (UNCONDITIONAL) -/

/-- ★ **The per-port internal event count is σ-equivariant.**  A crossing at `position` leaves `links` and the
event lists untouched, so the crossed extract's count at `index` equals the uncrossed extract's count at
`transposeAdjacent (bottomCount + position) index` — for EVERY state. -/
theorem crossInternalEventCountAt_equivariant (bottomCount position index : Nat)
    (state : ArcWireState) (eventNodes : List Nat)
    (window : position + 1 < state.openWires.length) :
    internalEventCountAt (stepCrossArc state position).links
        (boundaryNodesOf bottomCount (stepCrossArc state position)) eventNodes index
      = internalEventCountAt state.links (boundaryNodesOf bottomCount state) eventNodes
          (transposeAdjacent (bottomCount + position) index) := by
  show countEventsInRoot state.links
      (unionFindRootOf state.links
        (natListGetAt (List.range bottomCount ++ natListSwapTwoAt state.openWires position) index)) eventNodes
    = countEventsInRoot state.links
      (unionFindRootOf state.links
        (natListGetAt (List.range bottomCount ++ state.openWires)
          (transposeAdjacent (bottomCount + position) index))) eventNodes
  rw [natListGetAt_boundaryNodes_stepCrossArc bottomCount state.openWires position index window]

/-- ★ **The boundary same-component relation is σ-conjugate.**  A crossing at `position` conjugates the
same-component relation by the transposition on both indices — for EVERY state. -/
theorem crossBoundarySameComponent_equivariant (bottomCount position firstIndex secondIndex : Nat)
    (state : ArcWireState) (window : position + 1 < state.openWires.length) :
    boundarySameComponent bottomCount (stepCrossArc state position) firstIndex secondIndex
      = boundarySameComponent bottomCount state
          (transposeAdjacent (bottomCount + position) firstIndex)
          (transposeAdjacent (bottomCount + position) secondIndex) := by
  show (unionFindRootOf state.links
        (natListGetAt (List.range bottomCount ++ natListSwapTwoAt state.openWires position) firstIndex)
      == unionFindRootOf state.links
        (natListGetAt (List.range bottomCount ++ natListSwapTwoAt state.openWires position) secondIndex))
    = (unionFindRootOf state.links
        (natListGetAt (List.range bottomCount ++ state.openWires)
          (transposeAdjacent (bottomCount + position) firstIndex))
      == unionFindRootOf state.links
        (natListGetAt (List.range bottomCount ++ state.openWires)
          (transposeAdjacent (bottomCount + position) secondIndex)))
  rw [natListGetAt_boundaryNodes_stepCrossArc bottomCount state.openWires position firstIndex window,
    natListGetAt_boundaryNodes_stepCrossArc bottomCount state.openWires position secondIndex window]

/-! ## The whole-list count-field swap (the headline, UNCONDITIONAL) -/

/-- ★ **The crossing SWAPS the two internal cup-count entries.**  `(extractArc bc (stepCrossArc st p))` reads its
per-port internal cup counts as `natListSwapTwoAt` (at boundary pivot `bc + p`) of the uncrossed extract's — the
whole-list form of the per-index equivariance, matching the r7 observability probes.  Proved by list
extensionality (`natListEqOfPointwiseGetAt`) over the per-index `crossInternalEventCountAt_equivariant`. -/
theorem internalCupCounts_stepCrossArc_eq_swap (bottomCount position : Nat) (state : ArcWireState)
    (window : position + 1 < state.openWires.length) :
    (extractArc bottomCount (stepCrossArc state position)).internalCupCounts
      = natListSwapTwoAt (extractArc bottomCount state).internalCupCounts (bottomCount + position) := by
  have lenEq : (natListSwapTwoAt state.openWires position).length = state.openWires.length :=
    natListSwapTwoAt_length state.openWires position window
  have pivotBound : bottomCount + position + 1 < bottomCount + state.openWires.length := by
    have base := Nat.add_lt_add_left window bottomCount
    rw [← Nat.add_assoc] at base
    exact base
  have pivotBoundMapped : bottomCount + position + 1
      < ((List.range (bottomCount + state.openWires.length)).map
        (internalEventCountAt state.links (List.range bottomCount ++ state.openWires)
          state.cupEventNodes)).length := by
    rw [listMapLength, rangeLength]; exact pivotBound
  show (List.range (bottomCount + (natListSwapTwoAt state.openWires position).length)).map
      (internalEventCountAt state.links
        (List.range bottomCount ++ natListSwapTwoAt state.openWires position) state.cupEventNodes)
    = natListSwapTwoAt
        ((List.range (bottomCount + state.openWires.length)).map
          (internalEventCountAt state.links (List.range bottomCount ++ state.openWires) state.cupEventNodes))
        (bottomCount + position)
  rw [lenEq]
  refine natListEqOfPointwiseGetAt _ _ ?_ ?_
  · rw [natListSwapTwoAt_length
        ((List.range (bottomCount + state.openWires.length)).map
          (internalEventCountAt state.links (List.range bottomCount ++ state.openWires) state.cupEventNodes))
        (bottomCount + position) pivotBoundMapped,
      listMapLength, listMapLength]
  · intro index indexBound
    have indexLtTotal : index < bottomCount + state.openWires.length := by
      rw [listMapLength, rangeLength] at indexBound; exact indexBound
    have indexLtRange : index < (List.range (bottomCount + state.openWires.length)).length := by
      rw [rangeLength]; exact indexLtTotal
    have transLtTotal : transposeAdjacent (bottomCount + position) index
        < bottomCount + state.openWires.length :=
      transposeAdjacent_lt (bottomCount + position) index (bottomCount + state.openWires.length)
        indexLtTotal pivotBound
    have transLtRange : transposeAdjacent (bottomCount + position) index
        < (List.range (bottomCount + state.openWires.length)).length := by
      rw [rangeLength]; exact transLtTotal
    rw [natListGetAt_map_inRange
        (internalEventCountAt state.links
          (List.range bottomCount ++ natListSwapTwoAt state.openWires position) state.cupEventNodes)
        (List.range (bottomCount + state.openWires.length)) index indexLtRange,
      rangeGetAt_below (bottomCount + state.openWires.length) index indexLtTotal,
      natListGetAt_natListSwapTwoAt
        ((List.range (bottomCount + state.openWires.length)).map
          (internalEventCountAt state.links (List.range bottomCount ++ state.openWires) state.cupEventNodes))
        (bottomCount + position) index pivotBoundMapped,
      natListGetAt_map_inRange
        (internalEventCountAt state.links (List.range bottomCount ++ state.openWires) state.cupEventNodes)
        (List.range (bottomCount + state.openWires.length))
        (transposeAdjacent (bottomCount + position) index) transLtRange,
      rangeGetAt_below (bottomCount + state.openWires.length)
        (transposeAdjacent (bottomCount + position) index) transLtTotal]
    exact crossInternalEventCountAt_equivariant bottomCount position index state state.cupEventNodes window

/-- ★ **The crossing SWAPS the two internal cap-count entries** — the cap dual of
`internalCupCounts_stepCrossArc_eq_swap`. -/
theorem internalCapCounts_stepCrossArc_eq_swap (bottomCount position : Nat) (state : ArcWireState)
    (window : position + 1 < state.openWires.length) :
    (extractArc bottomCount (stepCrossArc state position)).internalCapCounts
      = natListSwapTwoAt (extractArc bottomCount state).internalCapCounts (bottomCount + position) := by
  have lenEq : (natListSwapTwoAt state.openWires position).length = state.openWires.length :=
    natListSwapTwoAt_length state.openWires position window
  have pivotBound : bottomCount + position + 1 < bottomCount + state.openWires.length := by
    have base := Nat.add_lt_add_left window bottomCount
    rw [← Nat.add_assoc] at base
    exact base
  have pivotBoundMapped : bottomCount + position + 1
      < ((List.range (bottomCount + state.openWires.length)).map
        (internalEventCountAt state.links (List.range bottomCount ++ state.openWires)
          state.capEventNodes)).length := by
    rw [listMapLength, rangeLength]; exact pivotBound
  show (List.range (bottomCount + (natListSwapTwoAt state.openWires position).length)).map
      (internalEventCountAt state.links
        (List.range bottomCount ++ natListSwapTwoAt state.openWires position) state.capEventNodes)
    = natListSwapTwoAt
        ((List.range (bottomCount + state.openWires.length)).map
          (internalEventCountAt state.links (List.range bottomCount ++ state.openWires) state.capEventNodes))
        (bottomCount + position)
  rw [lenEq]
  refine natListEqOfPointwiseGetAt _ _ ?_ ?_
  · rw [natListSwapTwoAt_length
        ((List.range (bottomCount + state.openWires.length)).map
          (internalEventCountAt state.links (List.range bottomCount ++ state.openWires) state.capEventNodes))
        (bottomCount + position) pivotBoundMapped,
      listMapLength, listMapLength]
  · intro index indexBound
    have indexLtTotal : index < bottomCount + state.openWires.length := by
      rw [listMapLength, rangeLength] at indexBound; exact indexBound
    have indexLtRange : index < (List.range (bottomCount + state.openWires.length)).length := by
      rw [rangeLength]; exact indexLtTotal
    have transLtTotal : transposeAdjacent (bottomCount + position) index
        < bottomCount + state.openWires.length :=
      transposeAdjacent_lt (bottomCount + position) index (bottomCount + state.openWires.length)
        indexLtTotal pivotBound
    have transLtRange : transposeAdjacent (bottomCount + position) index
        < (List.range (bottomCount + state.openWires.length)).length := by
      rw [rangeLength]; exact transLtTotal
    rw [natListGetAt_map_inRange
        (internalEventCountAt state.links
          (List.range bottomCount ++ natListSwapTwoAt state.openWires position) state.capEventNodes)
        (List.range (bottomCount + state.openWires.length)) index indexLtRange,
      rangeGetAt_below (bottomCount + state.openWires.length) index indexLtTotal,
      natListGetAt_natListSwapTwoAt
        ((List.range (bottomCount + state.openWires.length)).map
          (internalEventCountAt state.links (List.range bottomCount ++ state.openWires) state.capEventNodes))
        (bottomCount + position) index pivotBoundMapped,
      natListGetAt_map_inRange
        (internalEventCountAt state.links (List.range bottomCount ++ state.openWires) state.capEventNodes)
        (List.range (bottomCount + state.openWires.length))
        (transposeAdjacent (bottomCount + position) index) transLtRange,
      rangeGetAt_below (bottomCount + state.openWires.length)
        (transposeAdjacent (bottomCount + position) index) transLtTotal]
    exact crossInternalEventCountAt_equivariant bottomCount position index state state.capEventNodes window

/-- The crossing leaves the cup total invariant (the event lists are untouched). -/
theorem cupCount_stepCrossArc_unchanged (bottomCount position : Nat) (state : ArcWireState) :
    (extractArc bottomCount (stepCrossArc state position)).cupCount
      = (extractArc bottomCount state).cupCount := rfl

/-- The crossing leaves the cap total invariant. -/
theorem capCount_stepCrossArc_unchanged (bottomCount position : Nat) (state : ArcWireState) :
    (extractArc bottomCount (stepCrossArc state position)).capCount
      = (extractArc bottomCount state).capCount := rfl

/-- The crossing leaves the loop count invariant. -/
theorem loops_stepCrossArc_unchanged (bottomCount position : Nat) (state : ArcWireState) :
    (extractArc bottomCount (stepCrossArc state position)).diagram.loops
      = (extractArc bottomCount state).diagram.loops := rfl

/-! ## The partner conjugation — the regime-gated arm (Probe fixtures on the r7 hostiles)

`conjugatePartner` is the σ-conjugation the partner field WOULD follow: permute positions by the transposition
AND remap values by it.  It holds only in the perfect-matching regime (each component ≤ 2 ports). -/

/-- The σ-conjugation of a partner list at boundary pivot `pivot`: swap the two entries then remap every value by
the same transposition. -/
def conjugatePartner (partner : List Nat) (pivot : Nat) : List Nat :=
  (natListSwapTwoAt partner pivot).map (transposeAdjacent pivot)

/-- ★ **Probe A (count swap, PROVEN general — witnessed on the different-component hostile).**  On
`crossingObservableState` the crossing at position `0` swaps the internal cup counts `[1,0,0,0] ↦ [0,1,0,0]`,
exactly `natListSwapTwoAt _ 0`.  A concrete instance of `internalCupCounts_stepCrossArc_eq_swap`. -/
theorem crossing_observable_internalCupCounts_isSwap :
    (extractArc 0 (stepCrossArc crossingObservableState 0)).internalCupCounts
      = natListSwapTwoAt (extractArc 0 crossingObservableState).internalCupCounts 0 := by decide

/-- ★ **Probe D (count swap at another position).**  At position `1` the swap is a no-op on the count vector
(`[1,0,0,0] ↦ [1,0,0,0]`), still exactly `natListSwapTwoAt _ 1`. -/
theorem crossing_observable_internalCupCounts_isSwap_atOne :
    (extractArc 0 (stepCrossArc crossingObservableState 1)).internalCupCounts
      = natListSwapTwoAt (extractArc 0 crossingObservableState).internalCupCounts 1 := by decide

/-- A genuine PERFECT MATCHING fixture: bottom ports `{0,1}`, top wires `[10,11,12,13]` paired to distinct
components (`10~0`, `11~1`, `12`, `13` each own a component).  Every boundary component holds ≤ 2 ports. -/
def crossingPairedState : ArcWireState :=
  { openWires := [10, 11, 12, 13],
    links := [(10, 0), (11, 1), (12, 100), (13, 101)],
    nextFresh := 200,
    loops := 0,
    cupEventNodes := [],
    capEventNodes := [] }

/-- ★ **Probe B (partner conjugation HOLDS in the matching regime).**  On the perfect matching, the crossing at
position `1` (boundary pivot `bottomCount + position = 3`) conjugates the partner list exactly:
`partner = [2,3,0,1,4,5] ↦ [2,4,0,3,1,5] = conjugatePartner _ 3`.  This is the regime where the r9 partner arm
lands. -/
theorem crossing_paired_partner_eq_conjugate :
    (extractArc 2 (stepCrossArc crossingPairedState 1)).diagram.partner
      = conjugatePartner (extractArc 2 crossingPairedState).diagram.partner 3 := by decide

/-- The HOSTILE: three top ports `40 ~ 41 ~ 42` share ONE component (`43` is alone) — a non-perfect-matching
diagram, unreachable by cup/cap folding (it violates `ArcPerfectMatchingTokens`). -/
def crossingTriComponentState : ArcWireState :=
  { openWires := [40, 41, 42, 43],
    links := [(41, 40), (42, 40)],
    nextFresh := 50,
    loops := 0,
    cupEventNodes := [],
    capEventNodes := [] }

/-- ★ **THE JAMMING ARM, witnessed — the partner conjugation FAILS off the perfect-matching regime.**  On the
three-port component, the crossing leaves the partner list `[1,0,0,3]` unchanged, while the σ-conjugation would
give `[1,0,1,3]`: `findPartnerScan`'s MIN-index choice does not commute with the transposition once a component
holds > 2 ports.  So the partner half of the transport is CONDITIONED on `ArcPerfectMatchingTokens` — the r9
arm — and cannot be stated `∀ state`. -/
theorem crossing_triComponent_partner_ne_conjugate :
    (extractArc 0 (stepCrossArc crossingTriComponentState 0)).diagram.partner
      ≠ conjugatePartner (extractArc 0 crossingTriComponentState).diagram.partner 0 := by decide

/-! ## Honesty markers -/

/-- **Honesty marker — the COUNT-FIELD equivariance transport is PROVED, unconditionally.**  The faithful
crossing acts on the extract's per-port internal cup/cap counts by the boundary-index transposition
`transposeAdjacent (bottomCount + position)`: per-index (`crossInternalEventCountAt_equivariant`), as the
same-component conjugation (`crossBoundarySameComponent_equivariant`), and as the whole-list swap
(`internalCupCounts_stepCrossArc_eq_swap` / `internalCapCounts_stepCrossArc_eq_swap`, witnessed by
`crossing_observable_internalCupCounts_isSwap`).  The cup/cap totals and loop count are invariant.  This holds for
EVERY state — no matching hypothesis.  `= true`. -/
def fxMode_hasArcCrossingCountEquivariantTransport : Bool := true

/-- **Honesty marker — the PARTNER equivariance transport is REGIME-GATED (the r9 arm), not general.**  The
`diagram.partner` field σ-conjugates only when every boundary component holds ≤ 2 ports (the shipped
`ArcPerfectMatchingTokens` invariant): `crossing_paired_partner_eq_conjugate` confirms it on a genuine matching,
but `crossing_triComponent_partner_ne_conjugate` REFUTES it on a three-port component (min-index of
`findPartnerScan` does not commute with an adjacent transposition there).  So this cannot be flipped `true` for a
general state; landing it needs threading `ArcPerfectMatchingTokens` through the shipped Brauer involution
machinery — the next round.  `= false`. -/
def fxMode_hasArcCrossingPartnerEquivariantTransport : Bool := false

/-- **Honesty pin — the faithful crossing engine is untouched.**  This file only reads `stepCrossArc` / `extractArc`;
`fxMode_hasArcCrossingFaithfulStep` stays `true`.  `rfl`. -/
theorem arcCrossingEquivariant_faithfulStep_stays_true :
    fxMode_hasArcCrossingFaithfulStep = true := rfl

/-- **Honesty pin — the general-signature peel stays the open keystone.**  The equivariance transport supplies the
count-field half a general-signature peel needs, but wiring the faithful crossing into
`arcSwapCorePackage_of_adjunctionSwap` (plus the partner arm above) is the next round;
`fxMode_hasArcPeelGeneralSignature` stays `false`.  `rfl`. -/
theorem arcCrossingEquivariant_generalSignature_stays_false :
    fxMode_hasArcPeelGeneralSignature = false := rfl

/-- **Honesty pin — the #2043 / WP-AMALG fresh-partition keystone is untouched.**
`fxMode_hasArcGodementSamePartitionFreshProof` stays `false`.  `rfl`. -/
theorem arcCrossingEquivariant_samePartitionFreshProof_stays_false :
    fxMode_hasArcGodementSamePartitionFreshProof = false := rfl

end FX1Poly.Polygraph
