import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingInterfaceSegment
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingPartnerReconstruction
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWindowSuffix
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingRelativeZone

/-! # MatchingCanonicalPairs — the positional boundary pairing instantiates the discharge (MODE3-D)

The segment-transfer discharge runs on an abstract `CanonicalPair`; this file builds the
concrete one — two canonical runs' boundary nodes paired POSITIONALLY — and discharges every
remaining hypothesis from the shipped extract↔view machinery:

* `CanonicalBoundaryPair` — nodes read at the same in-range boundary position of the two
  canonical states (`matchingBoundaryNodes` = bottom ports then top wires);
* `canonicalBoundaryPair_ofBottomPort` / `_ofTopPosition` — the two position families, read
  through the range/append kits (a bottom port IS its own boundary node in both states);
* `canonicalBoundaryPair_selfOfPortImage` — the zone discipline pins any below-base
  `relativeWireMap` image to a port index, which self-pairs — `portPairsSelf` discharged;
* `canonicalTransfers_ofViewSim` — the connectivity-view simulation (what extract equality
  reconstructs) IS the canonical transfer at positionally paired nodes: the view read at the
  two positions is definitionally the empty-base fold connectivity at the paired nodes once
  the links read-offs rewrite;
* ★ `compositeConnectivity_transfersAcrossInterface` — the fully discharged composite
  transfer: zone discipline + boundary tracking + links read-offs + view sim in, one-directional
  composite connectivity transfer out.

Remaining for the VIEW close: the composite-boundary `Corresponds` instances (bottom ports
below the fresh base, top wires as rename images of top positions) and the two-directional
Bool view equality.  Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the
audit twin. -/

set_option autoImplicit false

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

/-! ## The positional boundary pairing -/

/-- **The canonical boundary pairing**: two nodes read at the SAME in-range boundary position
of the two canonical states — the concrete `CanonicalPair` the segment-transfer discharge
consumes. -/
def CanonicalBoundaryPair (bottomCount : Nat) (stateA stateB : WireState)
    (nodeA nodeB : Nat) : Prop :=
  ∃ position : Nat, position < bottomCount + stateA.openWires.length
    ∧ natListGetAt (matchingBoundaryNodes bottomCount stateA) position = nodeA
    ∧ natListGetAt (matchingBoundaryNodes bottomCount stateB) position = nodeB

/-- A bottom port pairs with ITSELF: position `port` reads the range prefix in both states. -/
theorem canonicalBoundaryPair_ofBottomPort (bottomCount : Nat) (stateA stateB : WireState)
    (port : Nat) (portBelow : port < bottomCount) :
    CanonicalBoundaryPair bottomCount stateA stateB port port := by
  have portBelowRange : port < (List.range bottomCount).length := by
    rw [rangeLength bottomCount]
    exact portBelow
  have readA : natListGetAt (matchingBoundaryNodes bottomCount stateA) port = port := by
    show natListGetAt (List.range bottomCount ++ stateA.openWires) port = port
    rw [natListGetAt_append_inside (List.range bottomCount) stateA.openWires port
      portBelowRange]
    exact rangeGetAt_below bottomCount port portBelow
  have readB : natListGetAt (matchingBoundaryNodes bottomCount stateB) port = port := by
    show natListGetAt (List.range bottomCount ++ stateB.openWires) port = port
    rw [natListGetAt_append_inside (List.range bottomCount) stateB.openWires port
      portBelowRange]
    exact rangeGetAt_below bottomCount port portBelow
  exact ⟨port, Nat.lt_of_lt_of_le portBelow (Nat.le_add_right bottomCount
    stateA.openWires.length), readA, readB⟩

/-- The two top wires at one position pair: position `topOffset + bottomCount` reads past the
range prefix into the open-wire suffix in both states. -/
theorem canonicalBoundaryPair_ofTopPosition (bottomCount : Nat) (stateA stateB : WireState)
    (topOffset : Nat) (offsetInRange : topOffset < stateA.openWires.length) :
    CanonicalBoundaryPair bottomCount stateA stateB
      (natListGetAt stateA.openWires topOffset)
      (natListGetAt stateB.openWires topOffset) := by
  have readA : natListGetAt (matchingBoundaryNodes bottomCount stateA)
      (topOffset + bottomCount) = natListGetAt stateA.openWires topOffset := by
    have pastRead := natListGetAt_append_pastBlock (List.range bottomCount)
      stateA.openWires topOffset
    rw [rangeLength bottomCount] at pastRead
    exact pastRead
  have readB : natListGetAt (matchingBoundaryNodes bottomCount stateB)
      (topOffset + bottomCount) = natListGetAt stateB.openWires topOffset := by
    have pastRead := natListGetAt_append_pastBlock (List.range bottomCount)
      stateB.openWires topOffset
    rw [rangeLength bottomCount] at pastRead
    exact pastRead
  have positionBound : topOffset + bottomCount < bottomCount + stateA.openWires.length := by
    rw [Nat.add_comm topOffset bottomCount]
    exact Nat.add_lt_add_left offsetInRange bottomCount
  exact ⟨topOffset + bottomCount, positionBound, readA, readB⟩

/-- **The zone discipline discharges `portPairsSelf`**: a below-base `relativeWireMap` image
forces its preimage into the port zone (else the image sits at or above the base), and with
the wire count tracking the canonical bottom boundary the port index self-pairs. -/
theorem canonicalBoundaryPair_selfOfPortImage (wires : List Nat) (freshBase : Nat)
    (discipline : RelativeWireZoneDiscipline wires freshBase)
    (bottomCount : Nat) (midTracks : wires.length = bottomCount)
    (stateA stateB : WireState) (preimage : Nat)
    (imageBelow : relativeWireMap wires freshBase preimage < freshBase) :
    CanonicalBoundaryPair bottomCount stateA stateB preimage preimage := by
  cases Nat.lt_or_ge preimage wires.length with
  | inl preimageInPortZone =>
      rw [midTracks] at preimageInPortZone
      exact canonicalBoundaryPair_ofBottomPort bottomCount stateA stateB preimage
        preimageInPortZone
  | inr preimageInFreshZone =>
      exact absurd
        (Nat.lt_of_le_of_lt (discipline.freshImageAtOrAbove preimage preimageInFreshZone)
          imageBelow)
        (Nat.lt_irrefl freshBase)

/-! ## The canonical transfer from the connectivity-view simulation -/

/-- **The view simulation IS the canonical transfer at positionally paired nodes**: the
matching same-component read at the two positions is definitionally the empty-base fold
connectivity at the paired nodes once the boundary reads and links read-offs rewrite. -/
theorem canonicalTransfers_ofViewSim (bottomCount : Nat) (stateA stateB : WireState)
    (eventsA eventsB : List (Nat × Nat))
    (linksA : stateA.links = applyJoinEvents eventsA [])
    (linksB : stateB.links = applyJoinEvents eventsB [])
    (viewSim : MatchingConnectivityViewSim bottomCount stateA stateB)
    (pivotCanonicalA pivotCanonicalB probeCanonicalA probeCanonicalB : Nat)
    (pivotPair : CanonicalBoundaryPair bottomCount stateA stateB
      pivotCanonicalA pivotCanonicalB)
    (probePair : CanonicalBoundaryPair bottomCount stateA stateB
      probeCanonicalA probeCanonicalB)
    (connectedA : isSameComponent (applyJoinEvents eventsA [])
      pivotCanonicalA probeCanonicalA = true) :
    isSameComponent (applyJoinEvents eventsB [])
      pivotCanonicalB probeCanonicalB = true := by
  obtain ⟨pivotPosition, pivotBound, pivotReadA, pivotReadB⟩ := pivotPair
  obtain ⟨probePosition, probeBound, probeReadA, probeReadB⟩ := probePair
  have pivotBoundB : pivotPosition < bottomCount + stateB.openWires.length := by
    rw [← viewSim.lengthEq]
    exact pivotBound
  have probeBoundB : probePosition < bottomCount + stateB.openWires.length := by
    rw [← viewSim.lengthEq]
    exact probeBound
  have viewShaped : isSameComponent stateA.links
        (natListGetAt (matchingBoundaryNodes bottomCount stateA) pivotPosition)
        (natListGetAt (matchingBoundaryNodes bottomCount stateA) probePosition)
      = isSameComponent stateB.links
        (natListGetAt (matchingBoundaryNodes bottomCount stateB) pivotPosition)
        (natListGetAt (matchingBoundaryNodes bottomCount stateB) probePosition) :=
    viewSim.viewAgrees pivotPosition probePosition pivotBoundB probeBoundB
  rw [pivotReadA, probeReadA, pivotReadB, probeReadB, linksA, linksB] at viewShaped
  rw [← viewShaped]
  exact connectedA

/-! ## The fully discharged composite transfer -/

/-- ★ **The composite transfer, fully discharged**: with the mid-state zone discipline, the
wire count tracking the canonical bottom boundary, the two canonical links read-offs, and
the connectivity-view simulation (what extract equality reconstructs), composite connectivity
of the first renamed trace over the mid links transfers to the second at
`InterfaceCorresponds`-related probes. -/
theorem compositeConnectivity_transfersAcrossInterface (wires : List Nat) (freshBase : Nat)
    (discipline : RelativeWireZoneDiscipline wires freshBase)
    (bottomCount : Nat) (midTracks : wires.length = bottomCount)
    (stateA stateB : WireState) (eventsA eventsB midLinks : List (Nat × Nat))
    (linksA : stateA.links = applyJoinEvents eventsA [])
    (linksB : stateB.links = applyJoinEvents eventsB [])
    (viewSim : MatchingConnectivityViewSim bottomCount stateA stateB)
    (forest : isUnionFindForest midLinks)
    (baseBounded : ∀ leftNode rightNode : Nat, (leftNode, rightNode) ∈ midLinks →
      leftNode < freshBase ∧ rightNode < freshBase)
    (startNode lastNode startImage lastImage : Nat)
    (startCorresponds : InterfaceCorresponds (relativeWireMap wires freshBase) freshBase
      (CanonicalBoundaryPair bottomCount stateA stateB) startNode startImage)
    (lastCorresponds : InterfaceCorresponds (relativeWireMap wires freshBase) freshBase
      (CanonicalBoundaryPair bottomCount stateA stateB) lastNode lastImage)
    (foldConnected : isSameComponent
      (applyJoinEvents (eventsA.map (fun event =>
        (relativeWireMap wires freshBase event.1, relativeWireMap wires freshBase event.2)))
        midLinks)
      startNode lastNode = true) :
    isSameComponent
      (applyJoinEvents (eventsB.map (fun event =>
        (relativeWireMap wires freshBase event.1, relativeWireMap wires freshBase event.2)))
        midLinks)
      startImage lastImage = true :=
  isSameComponent_applyJoinEvents_transferAcrossInterface_ofCanonicalPairs
    (relativeWireMap wires freshBase) discipline.isInjective freshBase
    (CanonicalBoundaryPair bottomCount stateA stateB) eventsA eventsB midLinks
    forest baseBounded
    (canonicalBoundaryPair_selfOfPortImage wires freshBase discipline bottomCount midTracks
      stateA stateB)
    (canonicalTransfers_ofViewSim bottomCount stateA stateB eventsA eventsB linksA linksB
      viewSim)
    startNode lastNode startImage lastImage startCorresponds lastCorresponds foldConnected

/-! ## Honesty marker -/

/-- **Honesty marker — the positional canonical boundary pairing is SHIPPED and discharges
the whole transfer stack.**  `CanonicalBoundaryPair` (same in-range boundary position, both
states), the two position families (bottom ports self-pair, top wires pair positionally),
the zone-discipline `portPairsSelf` discharge, the view-simulation canonical transfer, and
the fully discharged one-directional composite transfer
(`compositeConnectivity_transfersAcrossInterface`).  NOT yet shipped: the VIEW close — the
composite-boundary `Corresponds` instances (composite bottom ports below the fresh base,
composite top wires as rename images of top positions via the openWires read-off) and the
two-directional Bool view equality; and the LOOP leg.  `= true`. -/
def fxMode_hasCanonicalBoundaryPairing : Bool := true

end FX1Poly.Polygraph
