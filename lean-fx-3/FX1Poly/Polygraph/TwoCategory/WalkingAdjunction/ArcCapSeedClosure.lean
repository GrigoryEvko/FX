import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcStrandClosureFold
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapReindexValues
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcEventCountTransport

/-! # ArcCapSeedClosure — the cap head's strand is closed, so its event indicator is zero

The strand-closure payoff (peel campaign H, strand-closure rung 3).  Firing the peeled CAP
at the canonical seed merges `{windowPosition, windowPosition + 1, bottomCount}` into one
component and drops both wires from the boundary — the merged strand is CLOSED: the anchor
`windowPosition` misses every remaining open wire (zone values `[0, windowPosition)` and
`[windowPosition + 2, bottomCount)`) and every future-fresh node (`≥ bottomCount + 1`).
Threading that `ArcStrandClosure` witness through the rung-2 fold, every query against the
anchor at the composite END state answers as at the seed — and at the seed every reindexed
probe misses the strand (the third avoidance atom, no probe hits the RIGHT wire, ships
here).  So the cap-head event indicator in the rung-E count decomposition evaluates to
ZERO, and the composite cap-event count at a reindexed probe EQUALS the fresh tail run's
count on the nose.

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

/-! ## The third avoidance atom — no reindexed probe hits the RIGHT wire -/

/-- ★ **No reindexed probe hits the right wire `windowPosition + 1`** — zone I values stay
strictly below the window, zone II values sit at least one above the right wire, zone III
values translate past the whole boundary. -/
theorem arcCapHeadReindex_missesRightWire
    (bottomCount windowPosition tailBoundary probeIndex : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount) :
    (windowPosition + 1 == arcHeadReindex
      (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3 probeIndex) = false := by
  cases Nat.lt_or_ge probeIndex windowPosition with
  | inl belowWindow =>
      rw [arcCapHeadReindex_belowWindow bottomCount windowPosition tailBoundary probeIndex
        windowFits tailBoundaryFits belowWindow]
      exact decide_eq_false (fun rightWireHitsProbe => Nat.lt_irrefl (windowPosition + 1)
        (Nat.lt_of_le_of_lt (Nat.le_of_eq rightWireHitsProbe)
          (Nat.lt_trans belowWindow (Nat.lt_succ_self windowPosition))))
  | inr atWindow =>
      cases Nat.lt_or_ge probeIndex tailBoundary with
      | inl belowTail =>
          obtain ⟨pastOffset, offsetSpec⟩ := Nat.le.dest atWindow
          have pastBound : windowPosition + pastOffset < tailBoundary := by
            rw [offsetSpec]
            exact belowTail
          rw [← offsetSpec,
            arcCapHeadReindex_pastWindow bottomCount windowPosition tailBoundary pastOffset
              windowFits tailBoundaryFits pastBound]
          exact decide_eq_false (fun rightWireHitsValue => Nat.lt_irrefl (windowPosition + 1)
            (Nat.lt_of_lt_of_le
              (Nat.lt_of_le_of_lt
                (Nat.succ_le_succ (Nat.le_add_right windowPosition pastOffset))
                (Nat.lt_succ_self (windowPosition + pastOffset + 1)))
              (Nat.le_of_eq rightWireHitsValue.symm)))
      | inr atTail =>
          rw [arcHeadReindex_capSeedShifts bottomCount windowPosition tailBoundary
            windowFits tailBoundaryFits probeIndex atTail]
          exact decide_eq_false (fun rightWireHitsShifted => Nat.lt_irrefl (windowPosition + 1)
            (Nat.lt_of_lt_of_le
              (Nat.lt_of_lt_of_le
                (Nat.lt_of_lt_of_le (Nat.lt_succ_self (windowPosition + 1)) windowFits)
                (Nat.le_trans (Nat.le_of_eq tailBoundaryFits.symm)
                  (Nat.le_trans (Nat.succ_le_succ (Nat.succ_le_succ atTail))
                    (Nat.le_succ (probeIndex + 2)))))
              (Nat.le_of_eq rightWireHitsShifted.symm)))

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

/-! ## The closed-strand witness at the cap-head seed -/

/-- ★ **The cap head's strand is closed at the seed**: after the peeled cap consumes the
window pair, the anchor `windowPosition` misses every remaining open wire (the removal's
two zones read range values off the strand) and every node at or above the advanced
frontier `bottomCount + 1`. -/
theorem arcStrandClosure_capHeadSeed (bottomCount windowPosition : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount) :
    ArcStrandClosure windowPosition
      (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        windowPosition) := by
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
  refine ⟨?_, ?_⟩
  · intro readPosition readInRange
    show isSameComponent
        (unionFindJoin
          (unionFindJoin [] (natListGetAt (List.range bottomCount) windowPosition)
            (natListGetAt (List.range bottomCount) (windowPosition + 1)))
          bottomCount (natListGetAt (List.range bottomCount) windowPosition))
        windowPosition
        (natListGetAt (natListRemoveTwoAt (List.range bottomCount) windowPosition)
          readPosition)
      = false
    rw [leftWireRead, rightWireRead]
    cases Nat.lt_or_ge readPosition windowPosition with
    | inl belowWindow =>
        have readValue : natListGetAt
            (natListRemoveTwoAt (List.range bottomCount) windowPosition) readPosition
          = readPosition :=
          (natListGetAt_natListRemoveTwoAt_below (List.range bottomCount) windowPosition
              readPosition belowWindow).trans
            (rangeGetAt_below bottomCount readPosition
              (Nat.lt_trans belowWindow leftWireBelowBoundary))
        rw [readValue]
        exact capSeedLinks_windowAnchorMissesOffStrand bottomCount windowPosition
          readPosition windowFits
          (decide_eq_false (fun anchorHitsRead => Nat.lt_irrefl windowPosition
            (Nat.lt_of_le_of_lt (Nat.le_of_eq anchorHitsRead) belowWindow)))
          (decide_eq_false (fun rightWireHitsRead => Nat.lt_irrefl (windowPosition + 1)
            (Nat.lt_of_le_of_lt (Nat.le_of_eq rightWireHitsRead)
              (Nat.lt_trans belowWindow (Nat.lt_succ_self windowPosition)))))
          (decide_eq_false (fun eventHitsRead => Nat.lt_irrefl bottomCount
            (Nat.lt_of_le_of_lt (Nat.le_of_eq eventHitsRead)
              (Nat.lt_trans belowWindow leftWireBelowBoundary))))
    | inr atWindow =>
        obtain ⟨pastOffset, pastOffsetEq⟩ := Nat.le.dest atWindow
        have windowFitsRange : windowPosition + 2 ≤ (List.range bottomCount).length := by
          rw [rangeLength]
          exact windowFits
        have removedShift : (natListRemoveTwoAt (List.range bottomCount)
              windowPosition).length + 2
            = bottomCount :=
          (natListRemoveTwoAt_length (List.range bottomCount) windowPosition
            windowFitsRange).trans (rangeLength bottomCount)
        have valueBelowBoundary : windowPosition + pastOffset + 2 < bottomCount := by
          rw [← pastOffsetEq] at readInRange
          exact Nat.lt_of_lt_of_le (Nat.succ_lt_succ (Nat.succ_lt_succ readInRange))
            (Nat.le_of_eq removedShift)
        have readValue : natListGetAt
            (natListRemoveTwoAt (List.range bottomCount) windowPosition) readPosition
          = windowPosition + pastOffset + 2 := by
          rw [← pastOffsetEq]
          exact (natListGetAt_natListRemoveTwoAt_pastPair (List.range bottomCount)
              windowPosition pastOffset windowFitsRange).trans
            (rangeGetAt_below bottomCount (windowPosition + pastOffset + 2)
              valueBelowBoundary)
        rw [readValue]
        exact capSeedLinks_windowAnchorMissesOffStrand bottomCount windowPosition
          (windowPosition + pastOffset + 2) windowFits
          (decide_eq_false (fun anchorHitsValue => Nat.lt_irrefl windowPosition
            (Nat.lt_of_lt_of_le
              (Nat.lt_of_le_of_lt (Nat.le_add_right windowPosition pastOffset)
                (Nat.lt_trans (Nat.lt_succ_self (windowPosition + pastOffset))
                  (Nat.lt_succ_self (windowPosition + pastOffset + 1))))
              (Nat.le_of_eq anchorHitsValue.symm))))
          (decide_eq_false (fun rightWireHitsValue => Nat.lt_irrefl (windowPosition + 1)
            (Nat.lt_of_lt_of_le
              (Nat.lt_of_le_of_lt
                (Nat.succ_le_succ (Nat.le_add_right windowPosition pastOffset))
                (Nat.lt_succ_self (windowPosition + pastOffset + 1)))
              (Nat.le_of_eq rightWireHitsValue.symm))))
          (decide_eq_false (fun eventHitsValue => Nat.lt_irrefl bottomCount
            (Nat.lt_of_le_of_lt (Nat.le_of_eq eventHitsValue) valueBelowBoundary)))
  · intro freshNode freshAtLeast
    have nodeAtLeast : bottomCount + 1 ≤ freshNode := freshAtLeast
    show isSameComponent
        (unionFindJoin
          (unionFindJoin [] (natListGetAt (List.range bottomCount) windowPosition)
            (natListGetAt (List.range bottomCount) (windowPosition + 1)))
          bottomCount (natListGetAt (List.range bottomCount) windowPosition))
        windowPosition freshNode
      = false
    rw [leftWireRead, rightWireRead]
    exact capSeedLinks_windowAnchorMissesOffStrand bottomCount windowPosition freshNode
      windowFits
      (decide_eq_false (fun anchorHitsNode => Nat.lt_irrefl windowPosition
        (Nat.lt_of_lt_of_le
          (Nat.lt_of_lt_of_le (Nat.lt_trans leftWireBelowBoundary
            (Nat.lt_succ_self bottomCount)) nodeAtLeast)
          (Nat.le_of_eq anchorHitsNode.symm))))
      (decide_eq_false (fun rightWireHitsNode => Nat.lt_irrefl (windowPosition + 1)
        (Nat.lt_of_lt_of_le
          (Nat.lt_of_lt_of_le (Nat.lt_trans rightWireBelowBoundary
            (Nat.lt_succ_self bottomCount)) nodeAtLeast)
          (Nat.le_of_eq rightWireHitsNode.symm))))
      (decide_eq_false (fun eventHitsNode => Nat.lt_irrefl bottomCount
        (Nat.lt_of_lt_of_le
          (Nat.lt_of_lt_of_le (Nat.lt_succ_self bottomCount) nodeAtLeast)
          (Nat.le_of_eq eventHitsNode.symm))))

/-! ## The payoff — the composite end state answers every reindexed query FALSE -/

/-- ★ **The cap head's event indicator is FALSE at the composite end state**: the seed
closure rides the rung-2 fold (queries stable end-to-start), and at the seed every
reindexed probe misses the strand by the three avoidance atoms. -/
theorem arcCapHeadFolded_windowAnchorMissesReindexed
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
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
  rw [isSameComponent_processArcSpine_queriesStable atoms
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
theorem arcCapHeadFolded_capEventCount_ofChained
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
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
  have decomposition := arcCapHeadFolded_capEventCountAtImage bottomCount windowPosition
    tailBoundary windowFits tailBoundaryFits atoms chained anchorProbe
  rw [arcCapHeadFolded_windowAnchorMissesReindexed bottomCount windowPosition tailBoundary
    windowFits tailBoundaryFits atoms chained anchorProbe] at decomposition
  exact decomposition.trans (Nat.add_zero _)

/-! ## Honesty marker -/

/-- **Honesty marker — the cap-head seed closure and the ZERO indicator (peel campaign H,
strand-closure rung 3).**  The third avoidance atom (no reindexed probe hits the RIGHT
wire), the off-strand computation at the pinned seed links (both join layers expanded by
the flat characterization, every disjunct dead on the three misses), the `ArcStrandClosure`
witness at the cap-head seed (both removal zones read range values off the strand; the
frontier field at `bottomCount + 1`), the composite-end-state FALSE evaluation of the cap
head's event indicator (seed closure through the rung-2 fold), and the clean count
equality: composite cap-event count at a reindexed probe = fresh tail count, on the nose.
What this marker does NOT claim: the boundary-read maps and partner-scan congruence (the
diagram leg, rung E-3), the non-crossing invariant (the cup-head orientation leg), and the
final head-cancellation assembly.  `= true`. -/
def fxMode_hasArcCapSeedClosure : Bool := true

end FX1Poly.Polygraph
