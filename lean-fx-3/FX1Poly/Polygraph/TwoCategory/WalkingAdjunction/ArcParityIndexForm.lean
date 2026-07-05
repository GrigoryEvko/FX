import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcEndTokenParity
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingPartnerScan
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFreshShift
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWindowSuffix
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.BlockRotation

/-! # ArcParityIndexForm — the parity invariant in matching-index form (peel campaign H, parity rung P-5 opener)

The parity invariant speaks END TOKENS; the partner-scan machinery speaks BOUNDARY INDICES
into `List.range seedBoundary ++ openWires`.  This brick translates: every in-range boundary
index carries a RUN-INDEPENDENT parity class (`arcBoundaryIndexClass` — a function of the
index and the seed boundary alone, no state argument), a found partner sits at the OPPOSITE
class of its probe (`arcPartnerFound_classOpposite` — scan soundness gives the same-component
witness, the invariant flips the class), and therefore the cross-run LEG SWAP is impossible
(`arcPartnerLegSwap_impossible`): no probe index can partner to a window leg in one parity
state and to the ADJACENT leg in another, because adjacent bottom ports carry opposite
classes while the probe's own class is the same in both runs.

This is the kill the cup partner cancel was waiting for: the composite partner transport's
two fused branches cover for each other exactly when the fresh partner at the shifted probe
jumps between the two window legs across the runs — the one discrepancy the transported
dispatch equality cannot see, and the one this refutation excludes.

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

/-! ## The canonical boundary reads -/

/-- Below the seed boundary, the canonical extraction boundary reads the index itself. -/
private theorem canonicalBottomReads (seedBoundary : Nat) (wires : List Nat)
    (portIndex : Nat) (portBelow : portIndex < seedBoundary) :
    natListGetAt (List.range seedBoundary ++ wires) portIndex = portIndex := by
  have blockBound : portIndex < (List.range seedBoundary).length := by
    rw [rangeLength seedBoundary]
    exact portBelow
  exact (natListGetAt_append_inside (List.range seedBoundary) wires portIndex
    blockBound).trans (rangeGetAt_below seedBoundary portIndex portBelow)

/-- At or past the seed boundary, the canonical extraction boundary reads the open wire at
the offset. -/
private theorem canonicalSlotReads (seedBoundary : Nat) (wires : List Nat)
    (slotOffset : Nat) (_slotBelow : slotOffset < wires.length) :
    natListGetAt (List.range seedBoundary ++ wires) (seedBoundary + slotOffset)
      = natListGetAt wires slotOffset := by
  have pastRead := natListGetAt_append_pastBlock (List.range seedBoundary) wires slotOffset
  rw [rangeLength seedBoundary] at pastRead
  rw [Nat.add_comm seedBoundary slotOffset]
  exact pastRead

/-! ## Indices name tokens (per-file copy, following the census index-form mold) -/

/-- Every in-range boundary index names an end token whose node is exactly the boundary
read: a bottom port when the index is below the seed boundary, an open slot at its offset
otherwise.  The disjunction records the shape for the class and injectivity recoveries. -/
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

/-! ## The run-independent index class -/

/-- **The parity class of a boundary index** — a function of the index and the seed
boundary ALONE, with no state argument.  Below the seed boundary the index is a bottom
port (class = its position parity); at or past it the index is an open slot (class = the
FLIP of its offset parity).  Run-independence is what makes the cross-run leg-swap
refutable: the same index carries the same class in every run. -/
def arcBoundaryIndexClass (sourceMode : AdjunctionMode) (seedBoundary index : Nat) :
    AdjunctionMode :=
  if index < seedBoundary then adjunctionModeAtDistance sourceMode index
  else adjunctionOppositeMode (adjunctionModeAtDistance sourceMode (index - seedBoundary))

/-- The two adjunction modes are distinct: the opposite is never a fixed point. -/
private theorem oppositeModeNeSelf (mode : AdjunctionMode) :
    adjunctionOppositeMode mode ≠ mode := by
  cases mode with
  | base => exact fun tipEqBase => AdjunctionMode.noConfusion tipEqBase
  | tip => exact fun baseEqTip => AdjunctionMode.noConfusion baseEqTip

/-- The token named by an in-range index carries exactly the index class: a bottom port's
class is the position parity (the below-boundary branch), an open slot's class is the
flipped offset parity (the at-or-past branch, the offset recovered by subtraction). -/
private theorem arcEndTokenClass_ofIndexShape (sourceMode : AdjunctionMode)
    (seedBoundary index : Nat) (token : ArcEndToken)
    (shape : (index < seedBoundary ∧ token = ArcEndToken.bottomPort index)
        ∨ ∃ slotOffset : Nat, seedBoundary + slotOffset = index
            ∧ token = ArcEndToken.openSlot slotOffset) :
    arcEndTokenClass sourceMode token
      = arcBoundaryIndexClass sourceMode seedBoundary index := by
  cases shape with
  | inl bottomShape =>
      obtain ⟨indexBelow, tokenShape⟩ := bottomShape
      rw [tokenShape]
      show adjunctionModeAtDistance sourceMode index
        = if index < seedBoundary then adjunctionModeAtDistance sourceMode index
          else adjunctionOppositeMode
            (adjunctionModeAtDistance sourceMode (index - seedBoundary))
      exact (if_pos indexBelow).symm
  | inr slotShape =>
      obtain ⟨slotOffset, offsetSpec, tokenShape⟩ := slotShape
      rw [tokenShape]
      have boundaryLeIndex : seedBoundary ≤ index := Nat.le.intro offsetSpec
      have notBelow : ¬ index < seedBoundary := fun below =>
        Nat.lt_irrefl seedBoundary (Nat.lt_of_le_of_lt boundaryLeIndex below)
      have offsetRecovered : index - seedBoundary = slotOffset := by
        rw [← offsetSpec, Nat.add_comm seedBoundary slotOffset]
        exact addSubCancelRight slotOffset seedBoundary
      show adjunctionOppositeMode (adjunctionModeAtDistance sourceMode slotOffset)
        = if index < seedBoundary then adjunctionModeAtDistance sourceMode index
          else adjunctionOppositeMode
            (adjunctionModeAtDistance sourceMode (index - seedBoundary))
      rw [if_neg notBelow, offsetRecovered]

/-! ## A found partner sits at the opposite class -/

/-- ★ **A found partner sits at the OPPOSITE index class of its probe.**  Scan soundness
(`findPartnerScan_root_ofFound`) turns the found partner into a same-component witness
between the probe's and the target's boundary reads; the two indices name distinct valid
tokens whose classes are the index classes; the parity invariant flips the class. -/
theorem arcPartnerFound_classOpposite (sourceMode : AdjunctionMode) (seedBoundary : Nat)
    (state : ArcWireState)
    (parity : ArcEndTokenParity sourceMode seedBoundary state)
    (probeIndex targetIndex : Nat)
    (probeInRange : probeIndex < seedBoundary + state.openWires.length)
    (targetInRange : targetIndex < seedBoundary + state.openWires.length)
    (targetNeProbe : targetIndex ≠ probeIndex)
    (partnerFound : partnerIndexOf state.links (List.range seedBoundary ++ state.openWires)
        (seedBoundary + state.openWires.length) probeIndex = targetIndex) :
    arcBoundaryIndexClass sourceMode seedBoundary probeIndex
      = adjunctionOppositeMode (arcBoundaryIndexClass sourceMode seedBoundary targetIndex)
    := by
  have scanForm : findPartnerScan state.links (List.range seedBoundary ++ state.openWires)
      (unionFindRootOf state.links
        (natListGetAt (List.range seedBoundary ++ state.openWires) probeIndex))
      probeIndex (List.range (seedBoundary + state.openWires.length)) = targetIndex :=
    partnerFound
  have resultNeExclude : findPartnerScan state.links
      (List.range seedBoundary ++ state.openWires)
      (unionFindRootOf state.links
        (natListGetAt (List.range seedBoundary ++ state.openWires) probeIndex))
      probeIndex (List.range (seedBoundary + state.openWires.length)) ≠ probeIndex :=
    fun resultEqExclude => targetNeProbe (scanForm.symm.trans resultEqExclude)
  have rootFact := findPartnerScan_root_ofFound state.links
    (List.range seedBoundary ++ state.openWires)
    (unionFindRootOf state.links
      (natListGetAt (List.range seedBoundary ++ state.openWires) probeIndex))
    probeIndex (List.range (seedBoundary + state.openWires.length)) resultNeExclude
  rw [scanForm] at rootFact
  have sameReads : isSameComponent state.links
      (natListGetAt (List.range seedBoundary ++ state.openWires) probeIndex)
      (natListGetAt (List.range seedBoundary ++ state.openWires) targetIndex) = true :=
    decide_eq_true rootFact.symm
  obtain ⟨probeToken, probeValid, probeNode, probeShape⟩ :=
    arcEndTokenAtIndex seedBoundary state (List.range seedBoundary ++ state.openWires)
      (canonicalBottomReads seedBoundary state.openWires)
      (canonicalSlotReads seedBoundary state.openWires) probeIndex probeInRange
  obtain ⟨targetToken, targetValid, targetNode, targetShape⟩ :=
    arcEndTokenAtIndex seedBoundary state (List.range seedBoundary ++ state.openWires)
      (canonicalBottomReads seedBoundary state.openWires)
      (canonicalSlotReads seedBoundary state.openWires) targetIndex targetInRange
  have tokensDistinct : probeToken ≠ targetToken := fun tokensEqual =>
    targetNeProbe (arcIndexOfTokenRecovery seedBoundary probeIndex targetIndex
      probeToken targetToken probeShape targetShape tokensEqual).symm
  have sameTokens : isSameComponent state.links (arcEndTokenNode state probeToken)
      (arcEndTokenNode state targetToken) = true := by
    rw [probeNode, targetNode]
    exact sameReads
  have classesOpposite := parity probeToken targetToken probeValid targetValid
    tokensDistinct sameTokens
  rw [arcEndTokenClass_ofIndexShape sourceMode seedBoundary probeIndex probeToken
      probeShape,
    arcEndTokenClass_ofIndexShape sourceMode seedBoundary targetIndex targetToken
      targetShape] at classesOpposite
  exact classesOpposite

/-! ## The cross-run leg-swap refutation -/

/-- ★ **The cross-run LEG SWAP is impossible.**  No probe index can partner to a window
leg in one parity state and to the ADJACENT leg in another: the probe's index class is
run-independent, each found partner flips it, and the two adjacent bottom ports carry
opposite classes — so the swap would force a mode to equal its own opposite.  This is the
one discrepancy the transported composite partner dispatch cannot see, and the parity kill
that pins the fresh partner data at the cup's window legs. -/
theorem arcPartnerLegSwap_impossible (sourceMode : AdjunctionMode) (seedBoundary : Nat)
    (stateOne stateTwo : ArcWireState)
    (parityOne : ArcEndTokenParity sourceMode seedBoundary stateOne)
    (parityTwo : ArcEndTokenParity sourceMode seedBoundary stateTwo)
    (windowPosition probeIndex : Nat)
    (windowSuccBelow : windowPosition + 1 < seedBoundary)
    (probeNeLeft : windowPosition ≠ probeIndex)
    (probeNeRight : windowPosition + 1 ≠ probeIndex)
    (probeInRangeOne : probeIndex < seedBoundary + stateOne.openWires.length)
    (probeInRangeTwo : probeIndex < seedBoundary + stateTwo.openWires.length)
    (partnerOneAtLeft : partnerIndexOf stateOne.links
        (List.range seedBoundary ++ stateOne.openWires)
        (seedBoundary + stateOne.openWires.length) probeIndex = windowPosition)
    (partnerTwoAtRight : partnerIndexOf stateTwo.links
        (List.range seedBoundary ++ stateTwo.openWires)
        (seedBoundary + stateTwo.openWires.length) probeIndex = windowPosition + 1) :
    False := by
  have windowBelow : windowPosition < seedBoundary :=
    Nat.lt_of_le_of_lt (Nat.le_succ windowPosition) windowSuccBelow
  have leftInRange : windowPosition < seedBoundary + stateOne.openWires.length :=
    Nat.lt_of_lt_of_le windowBelow
      (Nat.le_add_right seedBoundary stateOne.openWires.length)
  have rightInRange : windowPosition + 1 < seedBoundary + stateTwo.openWires.length :=
    Nat.lt_of_lt_of_le windowSuccBelow
      (Nat.le_add_right seedBoundary stateTwo.openWires.length)
  have probeClassOne := arcPartnerFound_classOpposite sourceMode seedBoundary stateOne
    parityOne probeIndex windowPosition probeInRangeOne leftInRange probeNeLeft
    partnerOneAtLeft
  have probeClassTwo := arcPartnerFound_classOpposite sourceMode seedBoundary stateTwo
    parityTwo probeIndex (windowPosition + 1) probeInRangeTwo rightInRange probeNeRight
    partnerTwoAtRight
  have oppositesEqual : adjunctionOppositeMode
      (arcBoundaryIndexClass sourceMode seedBoundary windowPosition)
      = adjunctionOppositeMode
        (arcBoundaryIndexClass sourceMode seedBoundary (windowPosition + 1)) :=
    probeClassOne.symm.trans probeClassTwo
  have classesEqual : arcBoundaryIndexClass sourceMode seedBoundary windowPosition
      = arcBoundaryIndexClass sourceMode seedBoundary (windowPosition + 1) := by
    have doubled := congrArg adjunctionOppositeMode oppositesEqual
    rw [adjunctionOppositeMode_isInvolutive
        (arcBoundaryIndexClass sourceMode seedBoundary windowPosition),
      adjunctionOppositeMode_isInvolutive
        (arcBoundaryIndexClass sourceMode seedBoundary (windowPosition + 1))] at doubled
    exact doubled
  have leftUnfold : arcBoundaryIndexClass sourceMode seedBoundary windowPosition
      = adjunctionModeAtDistance sourceMode windowPosition := by
    show (if windowPosition < seedBoundary
        then adjunctionModeAtDistance sourceMode windowPosition
        else adjunctionOppositeMode
          (adjunctionModeAtDistance sourceMode (windowPosition - seedBoundary)))
      = adjunctionModeAtDistance sourceMode windowPosition
    rw [if_pos windowBelow]
  have rightUnfold : arcBoundaryIndexClass sourceMode seedBoundary (windowPosition + 1)
      = adjunctionModeAtDistance sourceMode (windowPosition + 1) := by
    show (if windowPosition + 1 < seedBoundary
        then adjunctionModeAtDistance sourceMode (windowPosition + 1)
        else adjunctionOppositeMode
          (adjunctionModeAtDistance sourceMode (windowPosition + 1 - seedBoundary)))
      = adjunctionModeAtDistance sourceMode (windowPosition + 1)
    rw [if_pos windowSuccBelow]
  have fixedPoint : adjunctionModeAtDistance sourceMode windowPosition
      = adjunctionOppositeMode (adjunctionModeAtDistance sourceMode windowPosition) :=
    leftUnfold.symm.trans (classesEqual.trans rightUnfold)
  exact oppositeModeNeSelf (adjunctionModeAtDistance sourceMode windowPosition)
    fixedPoint.symm

/-! ## Honesty marker -/

/-- **Honesty marker — the parity INDEX FORM is SHIPPED (peel campaign H, parity rung P-5
opener).**  The run-independent boundary index class (`arcBoundaryIndexClass` — no state
argument), the found-partner class flip (`arcPartnerFound_classOpposite`), and the
cross-run leg-swap refutation (`arcPartnerLegSwap_impossible`): no probe can partner to a
window leg in one parity state and to the adjacent leg in another.  What this marker does
NOT claim: the fresh partner cancel assembled over the composite dispatch equality (the
leg-swap kill instantiated at the two folded runs) and the orbit-realignment endgame.
`= true`. -/
def fxMode_hasArcParityIndexForm : Bool := true

end FX1Poly.Polygraph
