import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapSeedClosure
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcEventCountTransport
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcStrandClosureFold

/-! # WalkingString/StringArcCapSeedClosure — the cap head's strand is closed, so its event indicator
is zero, ported (FC-3 r20, THE CLONE CAMPAIGN — floor)

Phantom-signature two-token clone of the walking-adjunction `ArcCapSeedClosure`, re-plumbed onto the
FOUR-generator adjoint-triple seed.  Firing the peeled CAP at the canonical seed closes the merged
strand; threading that `ArcStrandClosure` witness through the rung-2 fold (the string queries-stable
clone `stringIsSameComponent_processArcSpine_queriesStable`), every query against the anchor at the
composite END state answers as at the seed, and at the seed every reindexed probe misses the strand.
So the cap-head event indicator evaluates to ZERO, and the composite cap-event count at a reindexed
probe EQUALS the fresh tail run's count on the nose (riding the string count decomposition
`stringArcCapHeadFolded_capEventCountAtImage`).  The private range plumbing and the off-strand
computation are graph-neutral and re-declared verbatim (per-file copy); the public graph-neutral
`arcCapHeadReindex_missesRightWire` and `arcStrandClosure_capHeadSeed` are REUSED by import.  The
signature is a pure phantom, so ONLY the `SpineAtom`-quantified statements clone.

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


/-! ## The off-strand computation at the pinned seed links -/

/-- **A probe off the cap strand `{windowPosition, windowPosition + 1, bottomCount}` misses
the anchor's component at the seed links**: both join layers expand by the flat
characterization, and every disjunct dies on the three miss premises. -/
private theorem capSeedLinks_windowAnchorMissesOffStrand
    (bottomCount windowPosition probeNode : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (missesLeftWire : isSameComponent [] windowPosition probeNode = false)
    (missesRightWire : isSameComponent [] (windowPosition + 1) probeNode = false)
    (missesEventNode : isSameComponent [] bottomCount probeNode = false) :
    isSameComponent
      (unionFindJoin (unionFindJoin [] windowPosition (windowPosition + 1))
        bottomCount windowPosition)
      windowPosition probeNode = false := by
  have leftWireBelowBoundary : windowPosition < bottomCount :=
    Nat.lt_of_lt_of_le
      (Nat.lt_trans (Nat.lt_succ_self windowPosition)
        (Nat.lt_succ_self (windowPosition + 1)))
      windowFits
  have rightWireBelowBoundary : windowPosition + 1 < bottomCount :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self (windowPosition + 1)) windowFits
  have eventDiffersFromLeftWire : isSameComponent [] bottomCount windowPosition = false :=
    decide_eq_false (fun eventHitsWire => Nat.lt_irrefl bottomCount
      (Nat.lt_of_le_of_lt (Nat.le_of_eq eventHitsWire) leftWireBelowBoundary))
  have leftWireDiffersFromEvent : isSameComponent [] windowPosition bottomCount = false :=
    decide_eq_false (fun wireHitsEvent => Nat.lt_irrefl windowPosition
      (Nat.lt_of_lt_of_le leftWireBelowBoundary (Nat.le_of_eq wireHitsEvent.symm)))
  have eventDiffersFromRightWire :
      isSameComponent [] bottomCount (windowPosition + 1) = false :=
    decide_eq_false (fun eventHitsWire => Nat.lt_irrefl bottomCount
      (Nat.lt_of_le_of_lt (Nat.le_of_eq eventHitsWire) rightWireBelowBoundary))
  have innerAnchorMissesProbe : isSameComponent
      (unionFindJoin [] windowPosition (windowPosition + 1)) windowPosition probeNode
    = false := by
    rw [isSameComponent_unionFindJoin [] isUnionFindForest_nil windowPosition
        (windowPosition + 1) windowPosition probeNode,
      missesLeftWire, isSameComponent_self [] windowPosition, missesRightWire]
    rfl
  have innerEventMissesAnchor : isSameComponent
      (unionFindJoin [] windowPosition (windowPosition + 1)) bottomCount windowPosition
    = false := by
    rw [isSameComponent_unionFindJoin [] isUnionFindForest_nil windowPosition
        (windowPosition + 1) bottomCount windowPosition,
      eventDiffersFromLeftWire, leftWireDiffersFromEvent,
      isSameComponent_self [] windowPosition, eventDiffersFromRightWire]
    rfl
  have innerEventMissesProbe : isSameComponent
      (unionFindJoin [] windowPosition (windowPosition + 1)) bottomCount probeNode
    = false := by
    rw [isSameComponent_unionFindJoin [] isUnionFindForest_nil windowPosition
        (windowPosition + 1) bottomCount probeNode,
      missesEventNode, leftWireDiffersFromEvent, missesLeftWire]
    rfl
  rw [isSameComponent_unionFindJoin (unionFindJoin [] windowPosition (windowPosition + 1))
      (isUnionFindForest_unionFindJoin [] windowPosition (windowPosition + 1)
        isUnionFindForest_nil)
      bottomCount windowPosition windowPosition probeNode,
    innerAnchorMissesProbe, innerEventMissesAnchor, innerEventMissesProbe]
  rfl


/-! ## The payoff — the composite end state answers every reindexed query FALSE -/

/-- ★ **The cap head's event indicator is FALSE at the composite end state**: the seed
closure rides the rung-2 fold (queries stable end-to-start), and at the seed every
reindexed probe misses the strand by the three avoidance atoms. -/
theorem stringArcCapHeadFolded_windowAnchorMissesReindexed
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained tailBoundary atoms) (anchorProbe : Nat) :
    isSameComponent
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      windowPosition
      (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
        anchorProbe)
      = false := by
  have leftWireBelowBoundary : windowPosition < bottomCount :=
    Nat.lt_of_lt_of_le
      (Nat.lt_trans (Nat.lt_succ_self windowPosition)
        (Nat.lt_succ_self (windowPosition + 1)))
      windowFits
  have rightWireBelowBoundary : windowPosition + 1 < bottomCount :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self (windowPosition + 1)) windowFits
  have leftWireRead : natListGetAt (List.range bottomCount) windowPosition
      = windowPosition :=
    rangeGetAt_below bottomCount windowPosition leftWireBelowBoundary
  have rightWireRead : natListGetAt (List.range bottomCount) (windowPosition + 1)
      = windowPosition + 1 :=
    rangeGetAt_below bottomCount (windowPosition + 1) rightWireBelowBoundary
  have seedForest : isUnionFindForest
      (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        windowPosition).links :=
    isUnionFindForest_stepCapArc
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition
      isUnionFindForest_nil
  have seedTracks : (stepCapArc
        (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        windowPosition).openWires.length
      = tailBoundary :=
    capHeadOpenWires_length bottomCount windowPosition tailBoundary windowFits
      tailBoundaryFits
  rw [stringIsSameComponent_processArcSpine_queriesStable atoms
    (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      windowPosition)
    tailBoundary seedForest seedTracks chained windowPosition
    (arcStrandClosure_capHeadSeed bottomCount windowPosition windowFits)
    (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
      anchorProbe)]
  show isSameComponent
      (unionFindJoin
        (unionFindJoin [] (natListGetAt (List.range bottomCount) windowPosition)
          (natListGetAt (List.range bottomCount) (windowPosition + 1)))
        bottomCount (natListGetAt (List.range bottomCount) windowPosition))
      windowPosition
      (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
        anchorProbe)
    = false
  rw [leftWireRead, rightWireRead]
  exact capSeedLinks_windowAnchorMissesOffStrand bottomCount windowPosition
    (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
      anchorProbe)
    windowFits
    (arcCapHeadReindex_missesLeftWire bottomCount windowPosition tailBoundary anchorProbe
      windowFits tailBoundaryFits)
    (arcCapHeadReindex_missesRightWire bottomCount windowPosition tailBoundary anchorProbe
      windowFits tailBoundaryFits)
    (arcCapHeadReindex_missesEventNode bottomCount windowPosition tailBoundary anchorProbe
      windowFits tailBoundaryFits)

/-- ★ **The composite cap-event count at a reindexed probe EQUALS the fresh tail run's
count on the nose** — the rung-E decomposition with its head indicator evaluated to zero. -/
theorem stringArcCapHeadFolded_capEventCount_ofChained
    {overallSource overallTarget : adjointTripleGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjointTripleModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained tailBoundary atoms) (anchorProbe : Nat) :
    countEventsInRoot
        (processArcSpine
          (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).links
        (unionFindRootOf
          (processArcSpine
            (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).links
          (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3
            anchorProbe))
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
            anchorProbe)
          (processArcSpine
            (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
            atoms).capEventNodes := by
  have decomposition := stringArcCapHeadFolded_capEventCountAtImage bottomCount windowPosition
    tailBoundary windowFits tailBoundaryFits atoms chained anchorProbe
  rw [stringArcCapHeadFolded_windowAnchorMissesReindexed bottomCount windowPosition tailBoundary
    windowFits tailBoundaryFits atoms chained anchorProbe] at decomposition
  exact decomposition.trans (Nat.add_zero _)

/-! ## Honesty marker -/

/-- **Honesty marker — the cap-head seed closure and the ZERO indicator, ported (FC-3 r20 clone
campaign).**  The composite-end-state FALSE evaluation of the cap head's event indicator (seed closure
through the rung-2 fold) and the clean count equality: composite cap-event count at a reindexed probe
= fresh tail count, on the nose.  What this marker does NOT claim: the boundary-read maps and
partner-scan congruence (the diagram leg), the non-crossing invariant, and the final head-cancellation
assembly.  `= true`. -/
def fxString_hasArcCapSeedClosure : Bool := true

end FX1Poly.Polygraph
