import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusFold
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFreshShift

/-! # ArcCensusIndexForm — the boundary census in matching-index form (peel campaign H, cup rung 2d-v opener)

The census speaks END TOKENS; the partner-scan machinery speaks BOUNDARY INDICES into
`List.range seedBoundary ++ openWires` (the `extractDiagram` boundary list).  This brick
translates: three pairwise-distinct in-range boundary indices whose reads are pairwise
same-component contradict the census — each index names a token (a bottom port below the seed
boundary, an open slot at or past it), the token's node IS the boundary read, and distinct
indices name distinct tokens.  This is the two-endpoint uniqueness the fused-component partner
rewiring dispatches on: a boundary index's same-component partner index is unique.

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

/-! ## Indices name tokens -/

/-- Every in-range boundary index names an end token whose node is exactly the boundary read:
a bottom port when the index is below the seed boundary, an open slot at its offset otherwise.
The disjunction records the shape for the injectivity recovery. -/
private theorem arcEndTokenAtIndex (seedBoundary : Nat) (state : ArcWireState)
    (boundary : List Nat)
    (bottomReads : ∀ portIndex : Nat, portIndex < seedBoundary →
      natListGetAt boundary portIndex = portIndex)
    (slotReads : ∀ slotOffset : Nat, slotOffset < state.openWires.length →
      natListGetAt boundary (seedBoundary + slotOffset)
        = natListGetAt state.openWires slotOffset)
    (index : Nat) (inRange : index < seedBoundary + state.openWires.length) :
    ∃ token : ArcEndToken,
      isValidArcEndToken seedBoundary state token
        ∧ arcEndTokenNode state token = natListGetAt boundary index
        ∧ ((index < seedBoundary ∧ token = ArcEndToken.bottomPort index)
            ∨ ∃ slotOffset : Nat, seedBoundary + slotOffset = index
                ∧ token = ArcEndToken.openSlot slotOffset) := by
  cases Nat.lt_or_ge index seedBoundary with
  | inl belowBoundary =>
      refine ⟨ArcEndToken.bottomPort index, belowBoundary, ?_,
        Or.inl ⟨belowBoundary, rfl⟩⟩
      show index = natListGetAt boundary index
      exact (bottomReads index belowBoundary).symm
  | inr boundaryLeIndex =>
      obtain ⟨slotOffset, offsetSpec⟩ := Nat.le.dest boundaryLeIndex
      have slotBelowLength : slotOffset < state.openWires.length := by
        have indexSplit : seedBoundary + slotOffset
            < seedBoundary + state.openWires.length := by
          rw [offsetSpec]
          exact inRange
        exact Nat.lt_of_add_lt_add_left indexSplit
      refine ⟨ArcEndToken.openSlot slotOffset, slotBelowLength, ?_,
        Or.inr ⟨slotOffset, offsetSpec, rfl⟩⟩
      show natListGetAt state.openWires slotOffset = natListGetAt boundary index
      rw [← offsetSpec]
      exact (slotReads slotOffset slotBelowLength).symm

/-- Distinct indices name distinct tokens: bottom ports carry their index, open slots carry
their offset, and the constructors never collide. -/
private theorem arcIndexOfTokenRecovery (seedBoundary : Nat) (indexOne indexTwo : Nat)
    (tokenOne tokenTwo : ArcEndToken)
    (shapeOne : (indexOne < seedBoundary ∧ tokenOne = ArcEndToken.bottomPort indexOne)
        ∨ ∃ slotOffset : Nat, seedBoundary + slotOffset = indexOne
            ∧ tokenOne = ArcEndToken.openSlot slotOffset)
    (shapeTwo : (indexTwo < seedBoundary ∧ tokenTwo = ArcEndToken.bottomPort indexTwo)
        ∨ ∃ slotOffset : Nat, seedBoundary + slotOffset = indexTwo
            ∧ tokenTwo = ArcEndToken.openSlot slotOffset)
    (tokensEqual : tokenOne = tokenTwo) : indexOne = indexTwo := by
  cases shapeOne with
  | inl bottomOne =>
      cases shapeTwo with
      | inl bottomTwo =>
          rw [bottomOne.2, bottomTwo.2] at tokensEqual
          injection tokensEqual with indicesEqual
      | inr slotTwo =>
          obtain ⟨offsetTwo, _offsetTwoSpec, tokenTwoShape⟩ := slotTwo
          rw [bottomOne.2, tokenTwoShape] at tokensEqual
          exact ArcEndToken.noConfusion tokensEqual
  | inr slotOne =>
      obtain ⟨offsetOne, offsetOneSpec, tokenOneShape⟩ := slotOne
      cases shapeTwo with
      | inl bottomTwo =>
          rw [tokenOneShape, bottomTwo.2] at tokensEqual
          exact ArcEndToken.noConfusion tokensEqual
      | inr slotTwo =>
          obtain ⟨offsetTwo, offsetTwoSpec, tokenTwoShape⟩ := slotTwo
          rw [tokenOneShape, tokenTwoShape] at tokensEqual
          injection tokensEqual with offsetsEqual
          rw [← offsetOneSpec, ← offsetTwoSpec, offsetsEqual]

/-! ## The census in index form -/

/-- ★ **The census in matching-index form.**  Over any boundary list reading bottom ports below
the seed boundary and open wires at or past it, three pairwise-distinct in-range indices with
pairwise same-component reads are impossible: each index names a token whose node is its read,
distinct indices name distinct tokens, and three same-component tokens violate the census. -/
theorem arcBoundaryCensus_indexForm (seedBoundary : Nat) (state : ArcWireState)
    (census : ArcBoundaryCensus seedBoundary state)
    (boundary : List Nat)
    (bottomReads : ∀ portIndex : Nat, portIndex < seedBoundary →
      natListGetAt boundary portIndex = portIndex)
    (slotReads : ∀ slotOffset : Nat, slotOffset < state.openWires.length →
      natListGetAt boundary (seedBoundary + slotOffset)
        = natListGetAt state.openWires slotOffset)
    (indexOne indexTwo indexThree : Nat)
    (oneInRange : indexOne < seedBoundary + state.openWires.length)
    (twoInRange : indexTwo < seedBoundary + state.openWires.length)
    (threeInRange : indexThree < seedBoundary + state.openWires.length)
    (oneNeTwo : indexOne ≠ indexTwo) (oneNeThree : indexOne ≠ indexThree)
    (twoNeThree : indexTwo ≠ indexThree)
    (sameOneTwo : isSameComponent state.links (natListGetAt boundary indexOne)
      (natListGetAt boundary indexTwo) = true)
    (sameOneThree : isSameComponent state.links (natListGetAt boundary indexOne)
      (natListGetAt boundary indexThree) = true) : False := by
  obtain ⟨tokenOne, validOne, nodeOne, shapeOne⟩ :=
    arcEndTokenAtIndex seedBoundary state boundary bottomReads slotReads indexOne oneInRange
  obtain ⟨tokenTwo, validTwo, nodeTwo, shapeTwo⟩ :=
    arcEndTokenAtIndex seedBoundary state boundary bottomReads slotReads indexTwo twoInRange
  obtain ⟨tokenThree, validThree, nodeThree, shapeThree⟩ :=
    arcEndTokenAtIndex seedBoundary state boundary bottomReads slotReads indexThree threeInRange
  have sameTokensOneTwo : isSameComponent state.links (arcEndTokenNode state tokenOne)
      (arcEndTokenNode state tokenTwo) = true := by
    rw [nodeOne, nodeTwo]
    exact sameOneTwo
  have sameTokensOneThree : isSameComponent state.links (arcEndTokenNode state tokenOne)
      (arcEndTokenNode state tokenThree) = true := by
    rw [nodeOne, nodeThree]
    exact sameOneThree
  exact census tokenOne tokenTwo tokenThree validOne validTwo validThree
    (fun tokensEqual => oneNeTwo (arcIndexOfTokenRecovery seedBoundary indexOne indexTwo
      tokenOne tokenTwo shapeOne shapeTwo tokensEqual))
    (fun tokensEqual => oneNeThree (arcIndexOfTokenRecovery seedBoundary indexOne indexThree
      tokenOne tokenThree shapeOne shapeThree tokensEqual))
    (fun tokensEqual => twoNeThree (arcIndexOfTokenRecovery seedBoundary indexTwo indexThree
      tokenTwo tokenThree shapeTwo shapeThree tokensEqual))
    sameTokensOneTwo sameTokensOneThree

/-- ★ **The census over the canonical extraction boundary** `List.range seedBoundary ++
openWires` — the exact list `extractDiagram` and the partner scans read.  The two read
hypotheses of the index form are discharged by the append/range read lemmas. -/
theorem arcBoundaryCensus_boundaryNodes (seedBoundary : Nat) (state : ArcWireState)
    (census : ArcBoundaryCensus seedBoundary state)
    (indexOne indexTwo indexThree : Nat)
    (oneInRange : indexOne < seedBoundary + state.openWires.length)
    (twoInRange : indexTwo < seedBoundary + state.openWires.length)
    (threeInRange : indexThree < seedBoundary + state.openWires.length)
    (oneNeTwo : indexOne ≠ indexTwo) (oneNeThree : indexOne ≠ indexThree)
    (twoNeThree : indexTwo ≠ indexThree)
    (sameOneTwo : isSameComponent state.links
      (natListGetAt (List.range seedBoundary ++ state.openWires) indexOne)
      (natListGetAt (List.range seedBoundary ++ state.openWires) indexTwo) = true)
    (sameOneThree : isSameComponent state.links
      (natListGetAt (List.range seedBoundary ++ state.openWires) indexOne)
      (natListGetAt (List.range seedBoundary ++ state.openWires) indexThree) = true) :
    False := by
  have bottomReads : ∀ portIndex : Nat, portIndex < seedBoundary →
      natListGetAt (List.range seedBoundary ++ state.openWires) portIndex = portIndex := by
    intro portIndex portBelow
    have blockBound : portIndex < (List.range seedBoundary).length := by
      rw [rangeLength seedBoundary]
      exact portBelow
    exact (natListGetAt_append_inside (List.range seedBoundary) state.openWires portIndex
      blockBound).trans (rangeGetAt_below seedBoundary portIndex portBelow)
  have slotReads : ∀ slotOffset : Nat, slotOffset < state.openWires.length →
      natListGetAt (List.range seedBoundary ++ state.openWires) (seedBoundary + slotOffset)
        = natListGetAt state.openWires slotOffset := by
    intro slotOffset _slotBelow
    have pastRead := natListGetAt_append_pastBlock (List.range seedBoundary) state.openWires
      slotOffset
    rw [rangeLength seedBoundary] at pastRead
    rw [Nat.add_comm seedBoundary slotOffset]
    exact pastRead
  exact arcBoundaryCensus_indexForm seedBoundary state census
    (List.range seedBoundary ++ state.openWires) bottomReads slotReads
    indexOne indexTwo indexThree oneInRange twoInRange threeInRange
    oneNeTwo oneNeThree twoNeThree sameOneTwo sameOneThree

/-- **Honesty marker — the census INDEX FORM is SHIPPED (peel campaign H, cup rung 2d-v
opener).**  Three pairwise-distinct in-range boundary indices with pairwise same-component
reads are impossible, both over an abstract boundary list with port/slot read hypotheses
(`arcBoundaryCensus_indexForm`) and over the canonical extraction boundary
`List.range seedBoundary ++ openWires` (`arcBoundaryCensus_boundaryNodes`).  What this marker
does NOT claim: the fused-component partner rewiring itself (the punctured joined scan finding
the other leg attachment) and the cup-cancellation endgame.  `= true`. -/
def fxMode_hasArcCensusIndexForm : Bool := true

end FX1Poly.Polygraph
