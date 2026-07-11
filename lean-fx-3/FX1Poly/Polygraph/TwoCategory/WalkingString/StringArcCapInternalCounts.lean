import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapInternalCounts
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcCapBoundaryReads
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcCapScanAssembly
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcCapSeedClosure
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcCapWindowCounts
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcEventCountTransport

/-! # WalkingString/StringArcCapInternalCounts — the composite internal-count lists are the spliced
fresh lists, ported (FC-3 r20, THE CLONE CAMPAIGN — Branch A)

Phantom-signature two-token clone of the walking-adjunction `ArcCapInternalCounts`, re-plumbed onto the
FOUR-generator adjoint-triple seed.  The composite extract's per-port internal cap/cup count lists
equal the fresh extract's lists with the consumed strand's two values spliced in at the window: count
VALUES are boundary-invariant (no reindexing), below/past-window entries ride the on-the-nose
event-count transports at shifted boundary reads (the string transports
`stringArcCapHeadFolded_capEventCount_ofChained` / `stringArcCapHeadFolded_cupEventCountAtImage`), and
the two window ports read the consumed strand (the string window counts
`stringArcCapHeadFolded_windowStrand{Cap,Cup}Count` at the same root
`stringArcCapHeadFolded_windowRightRootEq`).  The private spliced-list assembly kit
(`internalCountListCorr_ofPointwise` and its helpers) is graph-neutral and re-declared verbatim; the
signature is a pure phantom, so ONLY the `SpineAtom`-quantified statements clone.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private plumbing (per-file copies, following the codebase pattern) -/

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

private theorem rangeLength (count : Nat) : (List.range count).length = count :=
  rangeLoopLength count []

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

/-- Hand-rolled append associativity (the core lemma leaks `propext`). -/
private theorem appendAssoc : (front middle back : List Nat) →
    (front ++ middle) ++ back = front ++ (middle ++ back)
  | [], _, _ => rfl
  | headWire :: frontRest, middle, back =>
      congrArg (fun joined => headWire :: joined) (appendAssoc frontRest middle back)

/-- Inserting a block exactly at the front segment's length splices it between the
segments. -/
private theorem natListInsertAt_splitsAtLength : (front : List Nat) → (position : Nat) →
    (back block : List Nat) → front.length = position →
    natListInsertAt (front ++ back) position block = front ++ (block ++ back)
  | [], position, back, block, lengthEq => by
      cases lengthEq
      cases back with
      | nil => exact rfl
      | cons headWire restWires => exact rfl
  | headWire :: frontRest, position, back, block, lengthEq => by
      cases lengthEq
      show headWire :: natListInsertAt (frontRest ++ back) frontRest.length block
        = headWire :: (frontRest ++ (block ++ back))
      exact congrArg (fun spliced => headWire :: spliced)
        (natListInsertAt_splitsAtLength frontRest frontRest.length back block rfl)

/-- Two maps agree on a list when they agree pointwise on its members (structural — no
`funext`). -/
private theorem listMapCongrOnMembers (compositeCount freshCount : Nat → Nat) :
    (candidates : List Nat) →
    (∀ candidate, candidate ∈ candidates → compositeCount candidate = freshCount candidate) →
    candidates.map compositeCount = candidates.map freshCount
  | [], _ => rfl
  | headCandidate :: rest, pointwise => by
      show compositeCount headCandidate :: rest.map compositeCount
        = freshCount headCandidate :: rest.map freshCount
      rw [pointwise headCandidate (List.Mem.head rest),
        listMapCongrOnMembers compositeCount freshCount rest
          (fun laterCandidate laterMem =>
            pointwise laterCandidate (List.Mem.tail headCandidate laterMem))]

/-- The past-window variant: composite counts at `windowPosition + 2 + offset` agree with
fresh counts at `windowPosition + offset` — both offset spellings baked into the statement
so no fused-lambda rewriting is ever needed. -/
private theorem listMapPastWindowCongr
    (compositeCount freshCount : Nat → Nat) (windowPosition : Nat) :
    (offsets : List Nat) →
    (∀ offset, offset ∈ offsets →
      compositeCount (windowPosition + 2 + offset) = freshCount (windowPosition + offset)) →
    (offsets.map (fun offset => windowPosition + 2 + offset)).map compositeCount
      = (offsets.map (fun offset => windowPosition + offset)).map freshCount
  | [], _ => rfl
  | headOffset :: rest, pointwise => by
      show compositeCount (windowPosition + 2 + headOffset)
          :: (rest.map (fun offset => windowPosition + 2 + offset)).map compositeCount
        = freshCount (windowPosition + headOffset)
          :: (rest.map (fun offset => windowPosition + offset)).map freshCount
      rw [pointwise headOffset (List.Mem.head rest),
        listMapPastWindowCongr compositeCount freshCount windowPosition rest
          (fun laterOffset laterMem =>
            pointwise laterOffset (List.Mem.tail headOffset laterMem))]

/-- **The generic spliced-list assembly for boundary-invariant values**: a composite count
map over the interleaved range equals the fresh count map over the plain range with the
window value pair spliced in, granted the three zone facts — below-window pointwise
agreement, past-window pointwise agreement at shifted indices, and the two window
values. -/
private theorem internalCountListCorr_ofPointwise
    (compositeCount freshCount : Nat → Nat) (windowPosition tailCount windowValue : Nat)
    (pointwiseBelow : ∀ candidate, candidate ∈ List.range windowPosition →
      compositeCount candidate = freshCount candidate)
    (pointwisePast : ∀ offset, offset ∈ List.range tailCount →
      compositeCount (windowPosition + 2 + offset) = freshCount (windowPosition + offset))
    (windowLeft : compositeCount windowPosition = windowValue)
    (windowRight : compositeCount (windowPosition + 1) = windowValue) :
    (List.range ((windowPosition + 2) + tailCount)).map compositeCount
      = natListInsertAt ((List.range (windowPosition + tailCount)).map freshCount)
          windowPosition [windowValue, windowValue] := by
  have belowSegEq : (List.range windowPosition).map compositeCount
      = (List.range windowPosition).map freshCount :=
    listMapCongrOnMembers compositeCount freshCount (List.range windowPosition)
      pointwiseBelow
  have pastSegEq := listMapPastWindowCongr compositeCount freshCount windowPosition
    (List.range tailCount) pointwisePast
  have windowSegEq : ([windowPosition, windowPosition + 1]).map compositeCount
      = [windowValue, windowValue] := by
    show compositeCount windowPosition :: compositeCount (windowPosition + 1) :: []
      = windowValue :: windowValue :: []
    rw [windowLeft, windowRight]
  have frontLengthEq : ((List.range windowPosition).map freshCount).length
      = windowPosition :=
    (mapLength freshCount (List.range windowPosition)).trans (rangeLength windowPosition)
  rw [rangeInterleaveAtWindow windowPosition tailCount,
    mapAppend compositeCount (List.range windowPosition ++ [windowPosition, windowPosition + 1])
      ((List.range tailCount).map (fun offset => windowPosition + 2 + offset)),
    mapAppend compositeCount (List.range windowPosition)
      [windowPosition, windowPosition + 1],
    rangeSplit windowPosition tailCount,
    mapAppend freshCount (List.range windowPosition)
      ((List.range tailCount).map (fun offset => windowPosition + offset)),
    natListInsertAt_splitsAtLength ((List.range windowPosition).map freshCount)
      windowPosition
      (((List.range tailCount).map (fun offset => windowPosition + offset)).map freshCount)
      [windowValue, windowValue] frontLengthEq,
    belowSegEq, windowSegEq, pastSegEq]
  exact appendAssoc ((List.range windowPosition).map freshCount)
    [windowValue, windowValue]
    (((List.range tailCount).map (fun offset => windowPosition + offset)).map freshCount)

/-! ## The assembled internal-count list correspondences -/

/-- ★ **The composite internal CAP-count list is the fresh list with `[1, 1]` spliced at
the window**: count values are boundary-invariant, below/past-window entries ride the
on-the-nose cap-event-count transport at shifted boundary reads, and both window ports
read the consumed strand carrying exactly the head's cap event. -/
theorem stringArcCapHeadFolded_internalCapCountsCorr
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained tailBoundary atoms) :
    (List.range
        (bottomCount
          + (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires.length)).map
      (internalEventCountAt
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (List.range bottomCount
          ++ (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires)
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).capEventNodes)
      = natListInsertAt
          ((List.range
              (tailBoundary
                + (processArcSpine
                  (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                  atoms).openWires.length)).map
            (internalEventCountAt
              (processArcSpine
                (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                atoms).links
              (List.range tailBoundary
                ++ (processArcSpine
                  (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                  atoms).openWires)
              (processArcSpine
                (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                atoms).capEventNodes))
          windowPosition [1, 1] := by
  have leftWireBelowBoundary : windowPosition < bottomCount :=
    Nat.lt_of_lt_of_le
      (Nat.lt_trans (Nat.lt_succ_self windowPosition)
        (Nat.lt_succ_self (windowPosition + 1)))
      windowFits
  have windowLeTail : windowPosition ≤ tailBoundary := by
    have paddedLe : windowPosition + 2 ≤ tailBoundary + 2 := by
      rw [tailBoundaryFits]
      exact windowFits
    exact Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ paddedLe)
  have windowLeTotal : windowPosition
      ≤ tailBoundary
        + (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          atoms).openWires.length :=
    Nat.le_trans windowLeTail
      (Nat.le_add_right tailBoundary
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          atoms).openWires.length)
  obtain ⟨tailCount, tailSpec⟩ := Nat.le.dest windowLeTotal
  have compositeCandidatesEq : List.range
      (bottomCount
        + (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires.length)
      = List.range ((windowPosition + 2) + tailCount) :=
    congrArg List.range
      ((stringArcCapHeadFolded_totalPorts bottomCount windowPosition tailBoundary windowFits
          tailBoundaryFits atoms).trans
        ((congrArg (fun totalPorts => totalPorts + 2) tailSpec.symm).trans
          (Nat.add_right_comm windowPosition tailCount 2)))
  have freshCandidatesEq : List.range
      (tailBoundary
        + (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          atoms).openWires.length)
      = List.range (windowPosition + tailCount) :=
    congrArg List.range tailSpec.symm
  have boundaryReadLeft : natListGetAt
      (List.range bottomCount
        ++ (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires)
      windowPosition = windowPosition := by
    have leftIndexInRange : windowPosition < (List.range bottomCount).length := by
      rw [rangeLength]
      exact leftWireBelowBoundary
    exact (natListGetAt_append_inside (List.range bottomCount)
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires
        windowPosition leftIndexInRange).trans
      (rangeGetAt_below bottomCount windowPosition leftWireBelowBoundary)
  have boundaryReadRight : natListGetAt
      (List.range bottomCount
        ++ (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires)
      (windowPosition + 1) = windowPosition + 1 := by
    have rightIndexInRange : windowPosition + 1 < (List.range bottomCount).length := by
      rw [rangeLength]
      exact windowFits
    exact (natListGetAt_append_inside (List.range bottomCount)
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires
        (windowPosition + 1) rightIndexInRange).trans
      (rangeGetAt_below bottomCount (windowPosition + 1) windowFits)
  rw [compositeCandidatesEq, freshCandidatesEq]
  exact internalCountListCorr_ofPointwise
    (internalEventCountAt
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (List.range bottomCount
        ++ (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires)
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).capEventNodes)
    (internalEventCountAt
      (processArcSpine
        (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
        atoms).links
      (List.range tailBoundary
        ++ (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          atoms).openWires)
      (processArcSpine
        (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
        atoms).capEventNodes)
    windowPosition tailCount 1
    (fun candidate candidateMem => by
      have candidateBelow : candidate < windowPosition := mem_range_imp_lt candidateMem
      have shiftFixed : freshShiftAbove windowPosition 2 candidate = candidate :=
        freshShiftAbove_ofNotLe windowPosition 2 candidate
          (fun windowLe =>
            Nat.lt_irrefl windowPosition (Nat.lt_of_le_of_lt windowLe candidateBelow))
      have readShifted := stringArcCapHeadFolded_boundaryRead_shifted bottomCount
        windowPosition tailBoundary windowFits tailBoundaryFits atoms candidate
        (Nat.lt_of_lt_of_le candidateBelow windowLeTotal)
      rw [shiftFixed] at readShifted
      show countEventsInRoot
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).links
          (unionFindRootOf
            (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).links
            (natListGetAt
              (List.range bottomCount
                ++ (processArcSpine
                  (stepCapArc
                    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                    windowPosition) atoms).openWires)
              candidate))
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).capEventNodes
        = countEventsInRoot
            (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              atoms).links
            (unionFindRootOf
              (processArcSpine
                (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                atoms).links
              (natListGetAt
                (List.range tailBoundary
                  ++ (processArcSpine
                    (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                    atoms).openWires)
                candidate))
            (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              atoms).capEventNodes
      rw [readShifted]
      exact stringArcCapHeadFolded_capEventCount_ofChained bottomCount windowPosition
        tailBoundary windowFits tailBoundaryFits atoms chained
        (natListGetAt
          (List.range tailBoundary
            ++ (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              atoms).openWires)
          candidate))
    (fun offset offsetMem => by
      have offsetBelow : offset < tailCount := mem_range_imp_lt offsetMem
      have excludeInRange : windowPosition + offset
          < tailBoundary
            + (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              atoms).openWires.length := by
        have shifted : windowPosition + offset < windowPosition + tailCount :=
          Nat.add_lt_add_left offsetBelow windowPosition
        rw [tailSpec] at shifted
        exact shifted
      have shiftPast : freshShiftAbove windowPosition 2 (windowPosition + offset)
          = windowPosition + offset + 2 :=
        freshShiftAbove_ofLe windowPosition 2 (windowPosition + offset)
          (Nat.le_add_right windowPosition offset)
      have readShifted := stringArcCapHeadFolded_boundaryRead_shifted bottomCount
        windowPosition tailBoundary windowFits tailBoundaryFits atoms
        (windowPosition + offset) excludeInRange
      rw [shiftPast, Nat.add_right_comm windowPosition offset 2] at readShifted
      show countEventsInRoot
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).links
          (unionFindRootOf
            (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).links
            (natListGetAt
              (List.range bottomCount
                ++ (processArcSpine
                  (stepCapArc
                    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                    windowPosition) atoms).openWires)
              (windowPosition + 2 + offset)))
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).capEventNodes
        = countEventsInRoot
            (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              atoms).links
            (unionFindRootOf
              (processArcSpine
                (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                atoms).links
              (natListGetAt
                (List.range tailBoundary
                  ++ (processArcSpine
                    (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                    atoms).openWires)
                (windowPosition + offset)))
            (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              atoms).capEventNodes
      rw [readShifted]
      exact stringArcCapHeadFolded_capEventCount_ofChained bottomCount windowPosition
        tailBoundary windowFits tailBoundaryFits atoms chained
        (natListGetAt
          (List.range tailBoundary
            ++ (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              atoms).openWires)
          (windowPosition + offset)))
    (by
      show countEventsInRoot
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).links
          (unionFindRootOf
            (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).links
            (natListGetAt
              (List.range bottomCount
                ++ (processArcSpine
                  (stepCapArc
                    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                    windowPosition) atoms).openWires)
              windowPosition))
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).capEventNodes = 1
      rw [boundaryReadLeft]
      exact stringArcCapHeadFolded_windowStrandCapCount bottomCount windowPosition tailBoundary
        windowFits tailBoundaryFits atoms chained)
    (by
      show countEventsInRoot
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).links
          (unionFindRootOf
            (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).links
            (natListGetAt
              (List.range bottomCount
                ++ (processArcSpine
                  (stepCapArc
                    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                    windowPosition) atoms).openWires)
              (windowPosition + 1)))
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).capEventNodes = 1
      rw [boundaryReadRight,
        stringArcCapHeadFolded_windowRightRootEq bottomCount windowPosition windowFits atoms]
      exact stringArcCapHeadFolded_windowStrandCapCount bottomCount windowPosition tailBoundary
        windowFits tailBoundaryFits atoms chained)

/-- ★ **The composite internal CUP-count list is the fresh list with `[0, 0]` spliced at
the window**: the cap head adds no cup event anywhere — below/past-window entries ride the
on-the-nose cup-event-count transport, and the consumed strand carries no cup event. -/
theorem stringArcCapHeadFolded_internalCupCountsCorr
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained tailBoundary atoms) :
    (List.range
        (bottomCount
          + (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires.length)).map
      (internalEventCountAt
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (List.range bottomCount
          ++ (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires)
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).cupEventNodes)
      = natListInsertAt
          ((List.range
              (tailBoundary
                + (processArcSpine
                  (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                  atoms).openWires.length)).map
            (internalEventCountAt
              (processArcSpine
                (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                atoms).links
              (List.range tailBoundary
                ++ (processArcSpine
                  (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                  atoms).openWires)
              (processArcSpine
                (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                atoms).cupEventNodes))
          windowPosition [0, 0] := by
  have leftWireBelowBoundary : windowPosition < bottomCount :=
    Nat.lt_of_lt_of_le
      (Nat.lt_trans (Nat.lt_succ_self windowPosition)
        (Nat.lt_succ_self (windowPosition + 1)))
      windowFits
  have windowLeTail : windowPosition ≤ tailBoundary := by
    have paddedLe : windowPosition + 2 ≤ tailBoundary + 2 := by
      rw [tailBoundaryFits]
      exact windowFits
    exact Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ paddedLe)
  have windowLeTotal : windowPosition
      ≤ tailBoundary
        + (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          atoms).openWires.length :=
    Nat.le_trans windowLeTail
      (Nat.le_add_right tailBoundary
        (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          atoms).openWires.length)
  obtain ⟨tailCount, tailSpec⟩ := Nat.le.dest windowLeTotal
  have compositeCandidatesEq : List.range
      (bottomCount
        + (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires.length)
      = List.range ((windowPosition + 2) + tailCount) :=
    congrArg List.range
      ((stringArcCapHeadFolded_totalPorts bottomCount windowPosition tailBoundary windowFits
          tailBoundaryFits atoms).trans
        ((congrArg (fun totalPorts => totalPorts + 2) tailSpec.symm).trans
          (Nat.add_right_comm windowPosition tailCount 2)))
  have freshCandidatesEq : List.range
      (tailBoundary
        + (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          atoms).openWires.length)
      = List.range (windowPosition + tailCount) :=
    congrArg List.range tailSpec.symm
  have boundaryReadLeft : natListGetAt
      (List.range bottomCount
        ++ (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires)
      windowPosition = windowPosition := by
    have leftIndexInRange : windowPosition < (List.range bottomCount).length := by
      rw [rangeLength]
      exact leftWireBelowBoundary
    exact (natListGetAt_append_inside (List.range bottomCount)
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires
        windowPosition leftIndexInRange).trans
      (rangeGetAt_below bottomCount windowPosition leftWireBelowBoundary)
  have boundaryReadRight : natListGetAt
      (List.range bottomCount
        ++ (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires)
      (windowPosition + 1) = windowPosition + 1 := by
    have rightIndexInRange : windowPosition + 1 < (List.range bottomCount).length := by
      rw [rangeLength]
      exact windowFits
    exact (natListGetAt_append_inside (List.range bottomCount)
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires
        (windowPosition + 1) rightIndexInRange).trans
      (rangeGetAt_below bottomCount (windowPosition + 1) windowFits)
  rw [compositeCandidatesEq, freshCandidatesEq]
  exact internalCountListCorr_ofPointwise
    (internalEventCountAt
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (List.range bottomCount
        ++ (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires)
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).cupEventNodes)
    (internalEventCountAt
      (processArcSpine
        (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
        atoms).links
      (List.range tailBoundary
        ++ (processArcSpine
          (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
          atoms).openWires)
      (processArcSpine
        (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
        atoms).cupEventNodes)
    windowPosition tailCount 0
    (fun candidate candidateMem => by
      have candidateBelow : candidate < windowPosition := mem_range_imp_lt candidateMem
      have shiftFixed : freshShiftAbove windowPosition 2 candidate = candidate :=
        freshShiftAbove_ofNotLe windowPosition 2 candidate
          (fun windowLe =>
            Nat.lt_irrefl windowPosition (Nat.lt_of_le_of_lt windowLe candidateBelow))
      have readShifted := stringArcCapHeadFolded_boundaryRead_shifted bottomCount
        windowPosition tailBoundary windowFits tailBoundaryFits atoms candidate
        (Nat.lt_of_lt_of_le candidateBelow windowLeTotal)
      rw [shiftFixed] at readShifted
      show countEventsInRoot
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).links
          (unionFindRootOf
            (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).links
            (natListGetAt
              (List.range bottomCount
                ++ (processArcSpine
                  (stepCapArc
                    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                    windowPosition) atoms).openWires)
              candidate))
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).cupEventNodes
        = countEventsInRoot
            (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              atoms).links
            (unionFindRootOf
              (processArcSpine
                (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                atoms).links
              (natListGetAt
                (List.range tailBoundary
                  ++ (processArcSpine
                    (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                    atoms).openWires)
                candidate))
            (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              atoms).cupEventNodes
      rw [readShifted]
      exact stringArcCapHeadFolded_cupEventCountAtImage bottomCount windowPosition
        tailBoundary windowFits tailBoundaryFits atoms chained
        (natListGetAt
          (List.range tailBoundary
            ++ (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              atoms).openWires)
          candidate))
    (fun offset offsetMem => by
      have offsetBelow : offset < tailCount := mem_range_imp_lt offsetMem
      have excludeInRange : windowPosition + offset
          < tailBoundary
            + (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              atoms).openWires.length := by
        have shifted : windowPosition + offset < windowPosition + tailCount :=
          Nat.add_lt_add_left offsetBelow windowPosition
        rw [tailSpec] at shifted
        exact shifted
      have shiftPast : freshShiftAbove windowPosition 2 (windowPosition + offset)
          = windowPosition + offset + 2 :=
        freshShiftAbove_ofLe windowPosition 2 (windowPosition + offset)
          (Nat.le_add_right windowPosition offset)
      have readShifted := stringArcCapHeadFolded_boundaryRead_shifted bottomCount
        windowPosition tailBoundary windowFits tailBoundaryFits atoms
        (windowPosition + offset) excludeInRange
      rw [shiftPast, Nat.add_right_comm windowPosition offset 2] at readShifted
      show countEventsInRoot
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).links
          (unionFindRootOf
            (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).links
            (natListGetAt
              (List.range bottomCount
                ++ (processArcSpine
                  (stepCapArc
                    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                    windowPosition) atoms).openWires)
              (windowPosition + 2 + offset)))
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).cupEventNodes
        = countEventsInRoot
            (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              atoms).links
            (unionFindRootOf
              (processArcSpine
                (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                atoms).links
              (natListGetAt
                (List.range tailBoundary
                  ++ (processArcSpine
                    (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
                    atoms).openWires)
                (windowPosition + offset)))
            (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              atoms).cupEventNodes
      rw [readShifted]
      exact stringArcCapHeadFolded_cupEventCountAtImage bottomCount windowPosition
        tailBoundary windowFits tailBoundaryFits atoms chained
        (natListGetAt
          (List.range tailBoundary
            ++ (processArcSpine
              (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
              atoms).openWires)
          (windowPosition + offset)))
    (by
      show countEventsInRoot
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).links
          (unionFindRootOf
            (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).links
            (natListGetAt
              (List.range bottomCount
                ++ (processArcSpine
                  (stepCapArc
                    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                    windowPosition) atoms).openWires)
              windowPosition))
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).cupEventNodes = 0
      rw [boundaryReadLeft]
      exact stringArcCapHeadFolded_windowStrandCupCount bottomCount windowPosition tailBoundary
        windowFits tailBoundaryFits atoms chained)
    (by
      show countEventsInRoot
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).links
          (unionFindRootOf
            (processArcSpine
              (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                windowPosition) atoms).links
            (natListGetAt
              (List.range bottomCount
                ++ (processArcSpine
                  (stepCapArc
                    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                    windowPosition) atoms).openWires)
              (windowPosition + 1)))
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).cupEventNodes = 0
      rw [boundaryReadRight,
        stringArcCapHeadFolded_windowRightRootEq bottomCount windowPosition windowFits atoms]
      exact stringArcCapHeadFolded_windowStrandCupCount bottomCount windowPosition tailBoundary
        windowFits tailBoundaryFits atoms chained)

/-! ## Honesty marker -/

/-- **Honesty marker — the composite internal-count lists are the spliced fresh lists, ported
(FC-3 r20 clone campaign).**  `stringArcCapHeadFolded_internalCapCountsCorr` /
`stringArcCapHeadFolded_internalCupCountsCorr`: at the cap-head folded end state the whole per-port
internal cap-count list equals the fresh list with `[1, 1]` spliced at the window (the head's own cap
event on both consumed-strand ports), and the cup-count list equals the fresh list with `[0, 0]`
spliced.  Count values are boundary-invariant, so the generic spliced-list assembly runs once over both
event kinds.  What this marker does NOT claim: the assembled `FullArcStructure` equality.  `= true`. -/
def fxString_hasArcCapInternalCounts : Bool := true

end FX1Poly.Polygraph
