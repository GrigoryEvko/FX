import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingCanonicalPairs

/-! # MatchingCompositeView — the composite boundary view agreement (MODE3-D, VIEW leg close)

The interface-gluing VIEW leg, closed at the event-list level: two second-half traces whose
CANONICAL runs extract identically act identically — as seen from the COMPOSITE boundary —
on any fresh-disjoint forest of mid-state links.

* `interfaceCorresponds_ofCompositeBoundaryPosition` — every composite boundary position's
  reads correspond: bottom ports (below the fresh base by the boundary monotonicity bound)
  self-correspond, top positions read rename images of the two canonical top wires, which
  pair positionally;
* ★ `compositeBoundaryView_agrees_ofExtractEq` — the Bool-level agreement: extract equality
  reconstructs the connectivity-view simulation in BOTH orientations, each direction of the
  fully discharged composite transfer runs at the corresponding boundary reads, and the two
  implications glue.

This is the "composite component view determined by (mid-state links, canonical extract)"
statement with no runs in it: the remaining SAT-D5 work is pure premise unpacking — rewriting
the composite runs' links and wires into these list forms through the D4a read-offs.  Raw
Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private plumbing -/

private theorem boolEqOfImpliesBoth : (leftBool rightBool : Bool) →
    (leftBool = true → rightBool = true) → (rightBool = true → leftBool = true) →
    leftBool = rightBool
  | true, _, forward, _ => (forward rfl).symm
  | false, true, _, backward => backward rfl
  | false, false, _, _ => rfl

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

/-- Reading the composite boundary list below the base count reads the port itself. -/
private theorem compositeBoundaryRead_ofPort (baseCount : Nat) (topWires : List Nat)
    (port : Nat) (portBelow : port < baseCount) :
    natListGetAt (List.range baseCount ++ topWires) port = port := by
  have portBelowRange : port < (List.range baseCount).length := by
    rw [rangeLength baseCount]
    exact portBelow
  rw [natListGetAt_append_inside (List.range baseCount) topWires port portBelowRange]
  exact rangeGetAt_below baseCount port portBelow

/-- Reading the composite boundary list at a top position reads the rename image of the
canonical top wire at that offset. -/
private theorem compositeBoundaryRead_ofTop (sigma : Nat → Nat) (baseCount : Nat)
    (canonicalWires : List Nat) (offset : Nat) (offsetBelow : offset < canonicalWires.length) :
    natListGetAt (List.range baseCount ++ canonicalWires.map sigma) (offset + baseCount)
      = sigma (natListGetAt canonicalWires offset) := by
  have pastRead := natListGetAt_append_pastBlock (List.range baseCount)
    (canonicalWires.map sigma) offset
  rw [rangeLength baseCount] at pastRead
  rw [pastRead]
  exact natListGetAt_map_inRange sigma canonicalWires offset offsetBelow

/-! ## The composite boundary correspondence -/

/-- **Every composite boundary position's reads correspond**: a bottom port reads itself in
both composites and sits below the fresh base; a top position reads the rename images of the
two canonical top wires, which pair positionally. -/
theorem interfaceCorresponds_ofCompositeBoundaryPosition (wires : List Nat) (freshBase : Nat)
    (midCount baseCount : Nat) (baseBelow : baseCount ≤ freshBase)
    (stateFirst stateSecond : WireState)
    (lengthsAgree : stateFirst.openWires.length = stateSecond.openWires.length)
    (position : Nat)
    (positionInRange : position < baseCount + stateFirst.openWires.length) :
    InterfaceCorresponds (relativeWireMap wires freshBase) freshBase
      (CanonicalBoundaryPair midCount stateFirst stateSecond)
      (natListGetAt (List.range baseCount
        ++ stateFirst.openWires.map (relativeWireMap wires freshBase)) position)
      (natListGetAt (List.range baseCount
        ++ stateSecond.openWires.map (relativeWireMap wires freshBase)) position) := by
  cases Nat.lt_or_ge position baseCount with
  | inl positionIsPort =>
      rw [compositeBoundaryRead_ofPort baseCount
          (stateFirst.openWires.map (relativeWireMap wires freshBase)) position positionIsPort,
        compositeBoundaryRead_ofPort baseCount
          (stateSecond.openWires.map (relativeWireMap wires freshBase)) position positionIsPort]
      exact interfaceCorresponds_ofBelowBase (relativeWireMap wires freshBase) freshBase
        (CanonicalBoundaryPair midCount stateFirst stateSecond) position
        (Nat.lt_of_lt_of_le positionIsPort baseBelow)
  | inr positionIsTop =>
      obtain ⟨offset, offsetEq⟩ := Nat.le.dest positionIsTop
      have offsetBelowFirst : offset < stateFirst.openWires.length := by
        rw [← offsetEq] at positionInRange
        exact Nat.lt_of_add_lt_add_left positionInRange
      have offsetBelowSecond : offset < stateSecond.openWires.length := by
        rw [← lengthsAgree]
        exact offsetBelowFirst
      rw [← offsetEq, Nat.add_comm baseCount offset,
        compositeBoundaryRead_ofTop (relativeWireMap wires freshBase) baseCount
          stateFirst.openWires offset offsetBelowFirst,
        compositeBoundaryRead_ofTop (relativeWireMap wires freshBase) baseCount
          stateSecond.openWires offset offsetBelowSecond]
      exact interfaceCorresponds_ofCanonicalPair (relativeWireMap wires freshBase) freshBase
        (CanonicalBoundaryPair midCount stateFirst stateSecond)
        (natListGetAt stateFirst.openWires offset)
        (natListGetAt stateSecond.openWires offset)
        (canonicalBoundaryPair_ofTopPosition midCount stateFirst stateSecond offset
          offsetBelowFirst)

/-! ## The VIEW leg, closed at the event-list level -/

/-- ★ **The composite boundary view agreement** — equal canonical extracts force the two
renamed traces' composite folds to agree at every pair of in-range composite boundary reads:
extract equality reconstructs the view simulation in both orientations, and each direction
of the fully discharged composite transfer runs at the corresponding reads. -/
theorem compositeBoundaryView_agrees_ofExtractEq (wires : List Nat) (freshBase : Nat)
    (discipline : RelativeWireZoneDiscipline wires freshBase)
    (midCount : Nat) (midTracks : wires.length = midCount)
    (baseCount : Nat) (baseBelow : baseCount ≤ freshBase)
    (stateA stateB : WireState) (eventsA eventsB midLinks : List (Nat × Nat))
    (linksA : stateA.links = applyJoinEvents eventsA [])
    (linksB : stateB.links = applyJoinEvents eventsB [])
    (extractsEqual : extractDiagram midCount stateA = extractDiagram midCount stateB)
    (forest : isUnionFindForest midLinks)
    (baseBounded : ∀ leftNode rightNode : Nat, (leftNode, rightNode) ∈ midLinks →
      leftNode < freshBase ∧ rightNode < freshBase)
    (positionOne positionTwo : Nat)
    (oneInRange : positionOne < baseCount + stateA.openWires.length)
    (twoInRange : positionTwo < baseCount + stateA.openWires.length) :
    isSameComponent
        (applyJoinEvents (eventsA.map (fun event =>
          (relativeWireMap wires freshBase event.1, relativeWireMap wires freshBase event.2)))
          midLinks)
        (natListGetAt (List.range baseCount
          ++ stateA.openWires.map (relativeWireMap wires freshBase)) positionOne)
        (natListGetAt (List.range baseCount
          ++ stateA.openWires.map (relativeWireMap wires freshBase)) positionTwo)
      = isSameComponent
        (applyJoinEvents (eventsB.map (fun event =>
          (relativeWireMap wires freshBase event.1, relativeWireMap wires freshBase event.2)))
          midLinks)
        (natListGetAt (List.range baseCount
          ++ stateB.openWires.map (relativeWireMap wires freshBase)) positionOne)
        (natListGetAt (List.range baseCount
          ++ stateB.openWires.map (relativeWireMap wires freshBase)) positionTwo) := by
  have viewSimForward : MatchingConnectivityViewSim midCount stateA stateB :=
    matchingConnectivityViewSim_ofExtractEq midCount stateA stateB extractsEqual
  have viewSimBackward : MatchingConnectivityViewSim midCount stateB stateA :=
    matchingConnectivityViewSim_ofExtractEq midCount stateB stateA extractsEqual.symm
  have oneInRangeB : positionOne < baseCount + stateB.openWires.length := by
    rw [← viewSimForward.lengthEq]
    exact oneInRange
  have twoInRangeB : positionTwo < baseCount + stateB.openWires.length := by
    rw [← viewSimForward.lengthEq]
    exact twoInRange
  exact boolEqOfImpliesBoth _ _
    (fun foldConnectedA =>
      compositeConnectivity_transfersAcrossInterface wires freshBase discipline
        midCount midTracks stateA stateB eventsA eventsB midLinks linksA linksB
        viewSimForward forest baseBounded _ _ _ _
        (interfaceCorresponds_ofCompositeBoundaryPosition wires freshBase midCount baseCount
          baseBelow stateA stateB viewSimForward.lengthEq positionOne oneInRange)
        (interfaceCorresponds_ofCompositeBoundaryPosition wires freshBase midCount baseCount
          baseBelow stateA stateB viewSimForward.lengthEq positionTwo twoInRange)
        foldConnectedA)
    (fun foldConnectedB =>
      compositeConnectivity_transfersAcrossInterface wires freshBase discipline
        midCount midTracks stateB stateA eventsB eventsA midLinks linksB linksA
        viewSimBackward forest baseBounded _ _ _ _
        (interfaceCorresponds_ofCompositeBoundaryPosition wires freshBase midCount baseCount
          baseBelow stateB stateA viewSimBackward.lengthEq positionOne oneInRangeB)
        (interfaceCorresponds_ofCompositeBoundaryPosition wires freshBase midCount baseCount
          baseBelow stateB stateA viewSimBackward.lengthEq positionTwo twoInRangeB)
        foldConnectedB)

/-! ## Honesty marker -/

/-- **Honesty marker — the interface-gluing VIEW leg is CLOSED at the event-list level.**
Two second-half traces with extract-equal canonical runs act identically — as read from any
pair of in-range composite boundary positions — on any fresh-disjoint forest of mid-state
links (`compositeBoundaryView_agrees_ofExtractEq`), through the eight-brick engine stack:
path characterization, interface transfer, fold-support rigidity, fold-rename equivariance,
the segment discharge, the positional canonical pairing, and the composite boundary
correspondence.  NOT yet shipped: the LOOP leg (equal loop increments over the mid links)
and the SAT-D5 run-level premise unpacking (rewriting the composite runs' links and wires
into these list forms through the D4a read-offs).  `= true`. -/
def fxMode_hasCompositeBoundaryViewAgreement : Bool := true

end FX1Poly.Polygraph
