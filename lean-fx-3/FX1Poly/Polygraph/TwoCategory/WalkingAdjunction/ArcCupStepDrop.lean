import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupStepDropCore
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcFreshSelfSimulation
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingRangeInterleave

/-! # ArcCupStepDrop — a TOP-OF-STACK cup's field-drop formulas (S3 field legs)

Building on `ArcCupStepDropCore` (the old-port partner shift + fresh-component root), this file expresses each
field of `extractArc bc (stepCupArc S w)` as a fixed INJECTIVE function of the corresponding field of
`extractArc bc S`.  The internal cup/cap count lists are the fresh lists with a two-value block spliced in at the
window `bc + w`:

  * `internalCapCounts_stepCupArc` — the two fresh legs carry NO cap event, so `[0, 0]` is spliced.
  * `internalCupCounts_stepCupArc` — the two fresh legs each read the cup's own fresh event, so `[1, 1]` is
    spliced.

Both ride the generic boundary-invariant spliced-list assembly (`internalCountListCorr_ofPointwise`, re-proved
here as a file-private copy per the codebase pattern): count VALUES are boundary-invariant, below/past-window
entries ride the old-port count invariance (`internalEventCountAt_stepCupArc_oldPort`, from the core's boundary
read + root preservation), and the two window ports read the fresh 3-node component whose root sits at
`nextFresh + 1`.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private range / list plumbing (per-file copies, following the codebase pattern) -/

private theorem rangeLoopLength : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLength count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1, Nat.add_right_comm count accumulated.length 1]

private theorem rangeLength (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLength count []]
  exact Nat.add_zero count

private theorem rangeLoopGetAt_past : (count : Nat) → (accumulated : List Nat) → (offset : Nat) →
    natListGetAt (List.range.loop count accumulated) (offset + count) = natListGetAt accumulated offset
  | 0, _, _ => rfl
  | count + 1, accumulated, offset => by
      have inner := rangeLoopGetAt_past count (count :: accumulated) (offset + 1)
      rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
      exact inner

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
          rw [indexEq]; exact pastRead

private theorem rangeGetAt_below (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  rangeLoopGetAt_below count [] index indexBelow

private theorem appendAssoc : (front middle back : List Nat) →
    (front ++ middle) ++ back = front ++ (middle ++ back)
  | [], _, _ => rfl
  | headWire :: frontRest, middle, back =>
      congrArg (fun joined => headWire :: joined) (appendAssoc frontRest middle back)

/-- Inserting a block exactly at the front segment's length splices it between the segments. -/
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

/-- Two maps agree on a list when they agree pointwise on its members (structural — no `funext`). -/
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
          (fun laterCandidate laterMem => pointwise laterCandidate (List.Mem.tail headCandidate laterMem))]

/-- The past-window variant: composite counts at `windowPosition + 2 + offset` agree with fresh counts at
`windowPosition + offset` — both offset spellings baked into the statement so no fused-lambda rewriting is
ever needed. -/
private theorem listMapPastWindowCongr (compositeCount freshCount : Nat → Nat) (windowPosition : Nat) :
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
          (fun laterOffset laterMem => pointwise laterOffset (List.Mem.tail headOffset laterMem))]

/-- **The generic spliced-list assembly for boundary-invariant values** (file-private copy): a composite count
map over the interleaved range equals the fresh count map over the plain range with the window value pair
spliced in, granted the three zone facts. -/
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
    listMapCongrOnMembers compositeCount freshCount (List.range windowPosition) pointwiseBelow
  have pastSegEq := listMapPastWindowCongr compositeCount freshCount windowPosition
    (List.range tailCount) pointwisePast
  have windowSegEq : ([windowPosition, windowPosition + 1]).map compositeCount
      = [windowValue, windowValue] := by
    show compositeCount windowPosition :: compositeCount (windowPosition + 1) :: []
      = windowValue :: windowValue :: []
    rw [windowLeft, windowRight]
  have frontLengthEq : ((List.range windowPosition).map freshCount).length = windowPosition :=
    (mapLength freshCount (List.range windowPosition)).trans (rangeLength windowPosition)
  rw [rangeInterleaveAtWindow windowPosition tailCount,
    mapAppend compositeCount (List.range windowPosition ++ [windowPosition, windowPosition + 1])
      ((List.range tailCount).map (fun offset => windowPosition + 2 + offset)),
    mapAppend compositeCount (List.range windowPosition) [windowPosition, windowPosition + 1],
    rangeSplit windowPosition tailCount,
    mapAppend freshCount (List.range windowPosition)
      ((List.range tailCount).map (fun offset => windowPosition + offset)),
    natListInsertAt_splitsAtLength ((List.range windowPosition).map freshCount) windowPosition
      (((List.range tailCount).map (fun offset => windowPosition + offset)).map freshCount)
      [windowValue, windowValue] frontLengthEq,
    belowSegEq, windowSegEq, pastSegEq]
  exact appendAssoc ((List.range windowPosition).map freshCount) [windowValue, windowValue]
    (((List.range tailCount).map (fun offset => windowPosition + offset)).map freshCount)

/-! ## The boundary read through a top-of-stack cup (from the core's steppedRead block) -/

/-- Every old boundary read lies below `nextFresh`. -/
private theorem readBelowFresh (seedBoundary : Nat) (state : ArcWireState)
    (fresh : ArcStateFresh state) (seedBelowFresh : seedBoundary ≤ state.nextFresh)
    (portIndex : Nat) (portInRange : portIndex < seedBoundary + state.openWires.length) :
    natListGetAt (List.range seedBoundary ++ state.openWires) portIndex < state.nextFresh := by
  cases Nat.lt_or_ge portIndex seedBoundary with
  | inl cBelow =>
      rw [natListGetAt_append_inside (List.range seedBoundary) state.openWires portIndex
          (by rw [rangeLength]; exact cBelow),
        rangeGetAt_below seedBoundary portIndex cBelow]
      exact Nat.lt_of_lt_of_le cBelow seedBelowFresh
  | inr cAtLeast =>
      obtain ⟨k, hk⟩ := Nat.le.dest cAtLeast
      have kInRange : k < state.openWires.length := by
        have hlt : seedBoundary + k < seedBoundary + state.openWires.length := by rw [hk]; exact portInRange
        exact Nat.lt_of_add_lt_add_left hlt
      have readEq : natListGetAt (List.range seedBoundary ++ state.openWires) portIndex
          = natListGetAt state.openWires k := by
        have hIdx : portIndex = k + (List.range seedBoundary).length := by
          rw [rangeLength, ← hk, Nat.add_comm seedBoundary k]
        rw [hIdx, natListGetAt_append_pastBlock (List.range seedBoundary) state.openWires k]
      rw [readEq]
      exact natListGetAt_lt_ofInRange state.nextFresh state.openWires k kInRange fresh.1

/-- The shifted read into the stepped boundary is the same old node the base boundary read (the core's
steppedRead block, restated over the `stepCupArc` projection). -/
private theorem steppedBoundaryRead (seedBoundary : Nat) (state : ArcWireState) (windowPosition : Nat)
    (windowFits : windowPosition ≤ state.openWires.length)
    (portIndex : Nat) (portInRange : portIndex < seedBoundary + state.openWires.length) :
    natListGetAt (List.range seedBoundary ++ (stepCupArc state windowPosition).openWires)
        (freshShiftAbove (seedBoundary + windowPosition) 2 portIndex)
      = natListGetAt (List.range seedBoundary ++ state.openWires) portIndex := by
  show natListGetAt (List.range seedBoundary
      ++ natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1])
      (freshShiftAbove (seedBoundary + windowPosition) 2 portIndex)
    = natListGetAt (List.range seedBoundary ++ state.openWires) portIndex
  cases Nat.lt_or_ge portIndex (seedBoundary + windowPosition) with
  | inl cBelowThreshold =>
      rw [freshShiftAbove_ofNotLe (seedBoundary + windowPosition) 2 portIndex
        (Nat.not_le_of_gt cBelowThreshold)]
      cases Nat.lt_or_ge portIndex seedBoundary with
      | inl cBelowSeed =>
          rw [natListGetAt_append_inside (List.range seedBoundary)
              (natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1]) portIndex
              (by rw [rangeLength]; exact cBelowSeed),
            natListGetAt_append_inside (List.range seedBoundary) state.openWires portIndex
              (by rw [rangeLength]; exact cBelowSeed)]
      | inr cAtLeastSeed =>
          obtain ⟨j, hj⟩ := Nat.le.dest cAtLeastSeed
          have jBelowWindow : j < windowPosition := by
            have hlt : seedBoundary + j < seedBoundary + windowPosition := by rw [hj]; exact cBelowThreshold
            exact Nat.lt_of_add_lt_add_left hlt
          have jInOpen : j < state.openWires.length := Nat.lt_of_lt_of_le jBelowWindow windowFits
          have hIdxj : portIndex = j + (List.range seedBoundary).length := by
            rw [rangeLength, ← hj, Nat.add_comm seedBoundary j]
          rw [hIdxj,
            natListGetAt_append_pastBlock (List.range seedBoundary)
              (natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1]) j,
            natListGetAt_append_pastBlock (List.range seedBoundary) state.openWires j,
            natListGetAt_natListInsertAt_below state.openWires windowPosition
              [state.nextFresh, state.nextFresh + 1] j jBelowWindow jInOpen]
  | inr cAtLeastThreshold =>
      rw [freshShiftAbove_ofLe (seedBoundary + windowPosition) 2 portIndex cAtLeastThreshold]
      obtain ⟨t, ht⟩ := Nat.le.dest cAtLeastThreshold
      have baseRead : natListGetAt (List.range seedBoundary ++ state.openWires) portIndex
          = natListGetAt state.openWires (windowPosition + t) := by
        have hIdx : portIndex = (windowPosition + t) + (List.range seedBoundary).length := by
          rw [rangeLength, ← ht, Nat.add_comm (windowPosition + t) seedBoundary,
            Nat.add_assoc seedBoundary windowPosition t]
        rw [hIdx, natListGetAt_append_pastBlock (List.range seedBoundary) state.openWires (windowPosition + t)]
      have steppedReadValue : natListGetAt (List.range seedBoundary
            ++ natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1]) (portIndex + 2)
          = natListGetAt state.openWires (windowPosition + t) := by
        have hIdx2 : portIndex + 2 = (windowPosition + t + 2) + (List.range seedBoundary).length := by
          rw [rangeLength, ← ht, Nat.add_comm (windowPosition + t + 2) seedBoundary,
            Nat.add_assoc seedBoundary windowPosition t, Nat.add_assoc seedBoundary (windowPosition + t) 2]
        rw [hIdx2, natListGetAt_append_pastBlock (List.range seedBoundary)
          (natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1])
          (windowPosition + t + 2)]
        exact natListGetAt_natListInsertAt_pastBlock state.openWires windowPosition
          [state.nextFresh, state.nextFresh + 1] t windowFits
      rw [baseRead, steppedReadValue]

/-! ## The old-port internal-count invariance -/

/-- ★ **A top-of-stack cup leaves each OLD port's internal event count undisturbed at the shifted position.**  For
any event list all below `nextFresh` and any old port `portIndex`, the stepped internal event count at the shifted
boundary position equals the base count at `portIndex`: the shifted boundary reads the same old node
(`steppedBoundaryRead`), its component root is preserved (`unionFindRootOf_stepCupArc_old`), and each event node's
root is preserved too (so `countEventsInRoot` agrees, `countEventsInRoot_congr_links`). -/
private theorem internalEventCountAt_stepCupArc_oldPort (seedBoundary : Nat) (state : ArcWireState)
    (windowPosition : Nat) (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (seedBelowFresh : seedBoundary ≤ state.nextFresh) (windowFits : windowPosition ≤ state.openWires.length)
    (events : List Nat) (eventsBelow : ∀ node ∈ events, node < state.nextFresh)
    (portIndex : Nat) (portInRange : portIndex < seedBoundary + state.openWires.length) :
    internalEventCountAt (stepCupArc state windowPosition).links
        (List.range seedBoundary ++ (stepCupArc state windowPosition).openWires) events
        (freshShiftAbove (seedBoundary + windowPosition) 2 portIndex)
      = internalEventCountAt state.links (List.range seedBoundary ++ state.openWires) events portIndex := by
  have parentsBelow : ∀ edge ∈ state.links, edge.2 < state.nextFresh := fun edge he => (fresh.2.1 edge he).2
  have oldNodeBelow : natListGetAt (List.range seedBoundary ++ state.openWires) portIndex < state.nextFresh :=
    readBelowFresh seedBoundary state fresh seedBelowFresh portIndex portInRange
  have oldRootBelow : unionFindRootOf state.links
      (natListGetAt (List.range seedBoundary ++ state.openWires) portIndex) < state.nextFresh :=
    unionFindRootOf_lt_of_fresh state.links state.nextFresh parentsBelow
      (natListGetAt (List.range seedBoundary ++ state.openWires) portIndex) oldNodeBelow
  have readEq := steppedBoundaryRead seedBoundary state windowPosition windowFits portIndex portInRange
  have rootPreservedAtOld : unionFindRootOf (stepCupArc state windowPosition).links
      (natListGetAt (List.range seedBoundary ++ state.openWires) portIndex)
      = unionFindRootOf state.links
        (natListGetAt (List.range seedBoundary ++ state.openWires) portIndex) :=
    unionFindRootOf_stepCupArc_old state windowPosition fresh forest
      (natListGetAt (List.range seedBoundary ++ state.openWires) portIndex) oldRootBelow
  have eventsRootPreserved : ∀ eventNode ∈ events,
      unionFindRootOf (stepCupArc state windowPosition).links eventNode
        = unionFindRootOf state.links eventNode := by
    intro eventNode eventMem
    exact unionFindRootOf_stepCupArc_old state windowPosition fresh forest eventNode
      (unionFindRootOf_lt_of_fresh state.links state.nextFresh parentsBelow eventNode
        (eventsBelow eventNode eventMem))
  show countEventsInRoot (stepCupArc state windowPosition).links
      (unionFindRootOf (stepCupArc state windowPosition).links
        (natListGetAt (List.range seedBoundary ++ (stepCupArc state windowPosition).openWires)
          (freshShiftAbove (seedBoundary + windowPosition) 2 portIndex))) events
    = countEventsInRoot state.links
        (unionFindRootOf state.links (natListGetAt (List.range seedBoundary ++ state.openWires) portIndex)) events
  rw [readEq, rootPreservedAtOld,
    countEventsInRoot_congr_links (stepCupArc state windowPosition).links state.links
      (unionFindRootOf state.links (natListGetAt (List.range seedBoundary ++ state.openWires) portIndex))
      events eventsRootPreserved]

/-! ## The window value at the two fresh legs -/

/-- The stepped internal event count over an all-below-`nextFresh` event list at the fresh legs' root
`nextFresh + 1` is `0`: every event root is preserved (so below `nextFresh`), never reaching `nextFresh + 1`. -/
private theorem countEventsInRoot_stepCupArc_freshRoot_eq_zero (state : ArcWireState) (windowPosition : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (events : List Nat) (eventsBelow : ∀ node ∈ events, node < state.nextFresh) :
    countEventsInRoot (stepCupArc state windowPosition).links (state.nextFresh + 1) events = 0 := by
  have parentsBelow : ∀ edge ∈ state.links, edge.2 < state.nextFresh := fun edge he => (fresh.2.1 edge he).2
  have eventsRootPreserved : ∀ eventNode ∈ events,
      unionFindRootOf (stepCupArc state windowPosition).links eventNode
        = unionFindRootOf state.links eventNode := by
    intro eventNode eventMem
    exact unionFindRootOf_stepCupArc_old state windowPosition fresh forest eventNode
      (unionFindRootOf_lt_of_fresh state.links state.nextFresh parentsBelow eventNode
        (eventsBelow eventNode eventMem))
  rw [countEventsInRoot_congr_links (stepCupArc state windowPosition).links state.links
    (state.nextFresh + 1) events eventsRootPreserved]
  exact countEventsInRoot_eq_zero_of_freshRoot state.links state.nextFresh parentsBelow
    (state.nextFresh + 1) (Nat.le_succ state.nextFresh) events eventsBelow

/-- The left fresh leg is read at boundary index `seedBoundary + windowPosition`. -/
private theorem legLeftRead (seedBoundary : Nat) (state : ArcWireState) (windowPosition : Nat)
    (windowFits : windowPosition ≤ state.openWires.length) :
    natListGetAt (List.range seedBoundary ++ (stepCupArc state windowPosition).openWires)
        (seedBoundary + windowPosition) = state.nextFresh := by
  show natListGetAt (List.range seedBoundary
      ++ natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1])
      (seedBoundary + windowPosition) = state.nextFresh
  have hIdx : seedBoundary + windowPosition = windowPosition + (List.range seedBoundary).length := by
    rw [rangeLength, Nat.add_comm seedBoundary windowPosition]
  rw [hIdx, natListGetAt_append_pastBlock (List.range seedBoundary)
    (natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1]) windowPosition]
  have inside := natListGetAt_natListInsertAt_inside state.openWires windowPosition
    [state.nextFresh, state.nextFresh + 1] 0 (Nat.succ_pos 1) windowFits
  rw [Nat.add_zero] at inside
  exact inside

/-- The right fresh leg is read at boundary index `seedBoundary + windowPosition + 1`. -/
private theorem legRightRead (seedBoundary : Nat) (state : ArcWireState) (windowPosition : Nat)
    (windowFits : windowPosition ≤ state.openWires.length) :
    natListGetAt (List.range seedBoundary ++ (stepCupArc state windowPosition).openWires)
        (seedBoundary + windowPosition + 1) = state.nextFresh + 1 := by
  show natListGetAt (List.range seedBoundary
      ++ natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1])
      (seedBoundary + windowPosition + 1) = state.nextFresh + 1
  have hIdx : seedBoundary + windowPosition + 1 = (windowPosition + 1) + (List.range seedBoundary).length := by
    rw [rangeLength, Nat.add_comm (windowPosition + 1) seedBoundary, Nat.add_assoc seedBoundary windowPosition 1]
  rw [hIdx, natListGetAt_append_pastBlock (List.range seedBoundary)
    (natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1]) (windowPosition + 1)]
  exact natListGetAt_natListInsertAt_inside state.openWires windowPosition
    [state.nextFresh, state.nextFresh + 1] 1 (Nat.lt_succ_self 1) windowFits

/-! ## The tail-count split shared by both count legs -/

/-- Package the window-fit split: `state.openWires.length = windowPosition + tailCount`, with the two range-total
identities the generic assembly needs. -/
private theorem windowSplitTotals (seedBoundary : Nat) (state : ArcWireState) (windowPosition tailCount : Nat)
    (tailSpec : windowPosition + tailCount = state.openWires.length) :
    seedBoundary + (state.openWires.length + 2)
        = (seedBoundary + windowPosition + 2) + tailCount
      ∧ seedBoundary + state.openWires.length = (seedBoundary + windowPosition) + tailCount := by
  refine ⟨?_, ?_⟩
  · rw [← tailSpec, ← Nat.add_assoc seedBoundary (windowPosition + tailCount) 2,
      ← Nat.add_assoc seedBoundary windowPosition tailCount,
      Nat.add_right_comm (seedBoundary + windowPosition) tailCount 2]
  · rw [← tailSpec, ← Nat.add_assoc seedBoundary windowPosition tailCount]

/-! ## LEG 1 — the internal CAP-count list -/

/-- ★ **A top-of-stack cup splices `[0, 0]` into the internal CAP-count list at the window.**  The two fresh legs
carry no cap event (the cup allocates only a cup event), and every old port keeps its cap count at the shifted
position — so the stepped cap-count list is the base list with `[0, 0]` inserted at `seedBoundary + windowPosition`.
An injective function of the base list (`natListInsertAt` is left-invertible by erasure). -/
theorem internalCapCounts_stepCupArc (seedBoundary : Nat) (state : ArcWireState) (windowPosition : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (seedBelowFresh : seedBoundary ≤ state.nextFresh)
    (windowFits : windowPosition ≤ state.openWires.length) :
    (extractArc seedBoundary (stepCupArc state windowPosition)).internalCapCounts
      = natListInsertAt (extractArc seedBoundary state).internalCapCounts
          (seedBoundary + windowPosition) [0, 0] := by
  obtain ⟨tailCount, tailSpec⟩ := Nat.le.dest windowFits
  obtain ⟨steppedTotalEq, baseTotalEq⟩ := windowSplitTotals seedBoundary state windowPosition tailCount tailSpec
  have windowLeSum : seedBoundary + windowPosition ≤ seedBoundary + state.openWires.length :=
    Nat.add_le_add_left windowFits seedBoundary
  show (List.range (seedBoundary + (stepCupArc state windowPosition).openWires.length)).map
      (internalEventCountAt (stepCupArc state windowPosition).links
        (List.range seedBoundary ++ (stepCupArc state windowPosition).openWires)
        (stepCupArc state windowPosition).capEventNodes)
    = natListInsertAt ((List.range (seedBoundary + state.openWires.length)).map
        (internalEventCountAt state.links (List.range seedBoundary ++ state.openWires) state.capEventNodes))
        (seedBoundary + windowPosition) [0, 0]
  have steppedOpenLen : (stepCupArc state windowPosition).openWires.length = state.openWires.length + 2 :=
    natListInsertAt_length state.openWires windowPosition [state.nextFresh, state.nextFresh + 1]
  rw [steppedOpenLen, steppedTotalEq, baseTotalEq]
  refine internalCountListCorr_ofPointwise
    (internalEventCountAt (stepCupArc state windowPosition).links
      (List.range seedBoundary ++ (stepCupArc state windowPosition).openWires)
      (stepCupArc state windowPosition).capEventNodes)
    (internalEventCountAt state.links (List.range seedBoundary ++ state.openWires) state.capEventNodes)
    (seedBoundary + windowPosition) tailCount 0 ?below ?past ?left ?right
  case below =>
    intro candidate candidateMem
    have cLt : candidate < seedBoundary + windowPosition := mem_range_imp_lt candidateMem
    have cInRange : candidate < seedBoundary + state.openWires.length := Nat.lt_of_lt_of_le cLt windowLeSum
    have h := internalEventCountAt_stepCupArc_oldPort seedBoundary state windowPosition fresh forest
      seedBelowFresh windowFits state.capEventNodes fresh.2.2.2 candidate cInRange
    rw [freshShiftAbove_ofNotLe (seedBoundary + windowPosition) 2 candidate (Nat.not_le_of_gt cLt)] at h
    exact h
  case past =>
    intro offset offsetMem
    have oLt : offset < tailCount := mem_range_imp_lt offsetMem
    have idxInRange : seedBoundary + windowPosition + offset < seedBoundary + state.openWires.length := by
      rw [baseTotalEq]; exact Nat.add_lt_add_left oLt (seedBoundary + windowPosition)
    have h := internalEventCountAt_stepCupArc_oldPort seedBoundary state windowPosition fresh forest
      seedBelowFresh windowFits state.capEventNodes fresh.2.2.2 (seedBoundary + windowPosition + offset) idxInRange
    rw [freshShiftAbove_ofLe (seedBoundary + windowPosition) 2 (seedBoundary + windowPosition + offset)
      (Nat.le_add_right (seedBoundary + windowPosition) offset),
      Nat.add_right_comm (seedBoundary + windowPosition) offset 2] at h
    exact h
  case left =>
    show internalEventCountAt (stepCupArc state windowPosition).links
        (List.range seedBoundary ++ (stepCupArc state windowPosition).openWires)
        (stepCupArc state windowPosition).capEventNodes (seedBoundary + windowPosition) = 0
    show countEventsInRoot (stepCupArc state windowPosition).links
        (unionFindRootOf (stepCupArc state windowPosition).links
          (natListGetAt (List.range seedBoundary ++ (stepCupArc state windowPosition).openWires)
            (seedBoundary + windowPosition)))
        (stepCupArc state windowPosition).capEventNodes = 0
    rw [legLeftRead seedBoundary state windowPosition windowFits,
      (stepCupArc_freshComponentRoot state windowPosition fresh forest).1]
    exact countEventsInRoot_stepCupArc_freshRoot_eq_zero state windowPosition fresh forest
      state.capEventNodes fresh.2.2.2
  case right =>
    show internalEventCountAt (stepCupArc state windowPosition).links
        (List.range seedBoundary ++ (stepCupArc state windowPosition).openWires)
        (stepCupArc state windowPosition).capEventNodes (seedBoundary + windowPosition + 1) = 0
    show countEventsInRoot (stepCupArc state windowPosition).links
        (unionFindRootOf (stepCupArc state windowPosition).links
          (natListGetAt (List.range seedBoundary ++ (stepCupArc state windowPosition).openWires)
            (seedBoundary + windowPosition + 1)))
        (stepCupArc state windowPosition).capEventNodes = 0
    rw [legRightRead seedBoundary state windowPosition windowFits,
      (stepCupArc_freshComponentRoot state windowPosition fresh forest).2.1]
    exact countEventsInRoot_stepCupArc_freshRoot_eq_zero state windowPosition fresh forest
      state.capEventNodes fresh.2.2.2

/-! ## LEG 2 — the internal CUP-count list -/

/-- The stepped cup-event list `nextFresh + 2 :: state.cupEventNodes` at an OLD port reads the same as the base
cup-event list `state.cupEventNodes`: the fresh event `nextFresh + 2` roots at `nextFresh + 1`, distinct from the
old port's root (below `nextFresh`), so its indicator vanishes, and the tail rides the old-port invariance. -/
private theorem internalCupEventCountAt_stepCupArc_oldPort (seedBoundary : Nat) (state : ArcWireState)
    (windowPosition : Nat) (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (seedBelowFresh : seedBoundary ≤ state.nextFresh) (windowFits : windowPosition ≤ state.openWires.length)
    (portIndex : Nat) (portInRange : portIndex < seedBoundary + state.openWires.length) :
    internalEventCountAt (stepCupArc state windowPosition).links
        (List.range seedBoundary ++ (stepCupArc state windowPosition).openWires)
        ((state.nextFresh + 2) :: state.cupEventNodes)
        (freshShiftAbove (seedBoundary + windowPosition) 2 portIndex)
      = internalEventCountAt state.links (List.range seedBoundary ++ state.openWires) state.cupEventNodes
          portIndex := by
  have parentsBelow : ∀ edge ∈ state.links, edge.2 < state.nextFresh := fun edge he => (fresh.2.1 edge he).2
  have oldNodeBelow : natListGetAt (List.range seedBoundary ++ state.openWires) portIndex < state.nextFresh :=
    readBelowFresh seedBoundary state fresh seedBelowFresh portIndex portInRange
  have oldRootBelow : unionFindRootOf state.links
      (natListGetAt (List.range seedBoundary ++ state.openWires) portIndex) < state.nextFresh :=
    unionFindRootOf_lt_of_fresh state.links state.nextFresh parentsBelow
      (natListGetAt (List.range seedBoundary ++ state.openWires) portIndex) oldNodeBelow
  have readEq := steppedBoundaryRead seedBoundary state windowPosition windowFits portIndex portInRange
  have rootPreservedAtOld : unionFindRootOf (stepCupArc state windowPosition).links
      (natListGetAt (List.range seedBoundary ++ state.openWires) portIndex)
      = unionFindRootOf state.links
        (natListGetAt (List.range seedBoundary ++ state.openWires) portIndex) :=
    unionFindRootOf_stepCupArc_old state windowPosition fresh forest
      (natListGetAt (List.range seedBoundary ++ state.openWires) portIndex) oldRootBelow
  -- the stepped root at the old port, expressed base-side (below nextFresh)
  have steppedRootAtOld : unionFindRootOf (stepCupArc state windowPosition).links
      (natListGetAt (List.range seedBoundary ++ (stepCupArc state windowPosition).openWires)
        (freshShiftAbove (seedBoundary + windowPosition) 2 portIndex))
      = unionFindRootOf state.links
        (natListGetAt (List.range seedBoundary ++ state.openWires) portIndex) := by
    rw [readEq]; exact rootPreservedAtOld
  -- the fresh cup event roots at nextFresh + 1, distinct from the old root
  have freshEventRoot : unionFindRootOf (stepCupArc state windowPosition).links (state.nextFresh + 2)
      = state.nextFresh + 1 := (stepCupArc_freshComponentRoot state windowPosition fresh forest).2.2
  have indicatorFalse : (unionFindRootOf (stepCupArc state windowPosition).links (state.nextFresh + 2)
      == unionFindRootOf (stepCupArc state windowPosition).links
          (natListGetAt (List.range seedBoundary ++ (stepCupArc state windowPosition).openWires)
            (freshShiftAbove (seedBoundary + windowPosition) 2 portIndex))) = false := by
    rw [freshEventRoot, steppedRootAtOld]
    exact beq_false_of_lt (Nat.lt_succ_of_lt oldRootBelow)
  show (if unionFindRootOf (stepCupArc state windowPosition).links (state.nextFresh + 2)
        == unionFindRootOf (stepCupArc state windowPosition).links
            (natListGetAt (List.range seedBoundary ++ (stepCupArc state windowPosition).openWires)
              (freshShiftAbove (seedBoundary + windowPosition) 2 portIndex)) then 1 else 0)
      + countEventsInRoot (stepCupArc state windowPosition).links
          (unionFindRootOf (stepCupArc state windowPosition).links
            (natListGetAt (List.range seedBoundary ++ (stepCupArc state windowPosition).openWires)
              (freshShiftAbove (seedBoundary + windowPosition) 2 portIndex)))
          state.cupEventNodes
    = internalEventCountAt state.links (List.range seedBoundary ++ state.openWires) state.cupEventNodes portIndex
  rw [indicatorFalse]
  show (0 : Nat) + countEventsInRoot (stepCupArc state windowPosition).links
        (unionFindRootOf (stepCupArc state windowPosition).links
          (natListGetAt (List.range seedBoundary ++ (stepCupArc state windowPosition).openWires)
            (freshShiftAbove (seedBoundary + windowPosition) 2 portIndex)))
        state.cupEventNodes
    = internalEventCountAt state.links (List.range seedBoundary ++ state.openWires) state.cupEventNodes portIndex
  rw [Nat.zero_add]
  exact internalEventCountAt_stepCupArc_oldPort seedBoundary state windowPosition fresh forest
    seedBelowFresh windowFits state.cupEventNodes fresh.2.2.1 portIndex portInRange

/-- ★ **A top-of-stack cup splices `[1, 1]` into the internal CUP-count list at the window.**  The two fresh legs
each carry the cup's own fresh cup event (`nextFresh + 2`, on their shared component root `nextFresh + 1`), and
every old port keeps its cup count at the shifted position — so the stepped cup-count list is the base list with
`[1, 1]` inserted at `seedBoundary + windowPosition`. -/
theorem internalCupCounts_stepCupArc (seedBoundary : Nat) (state : ArcWireState) (windowPosition : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (seedBelowFresh : seedBoundary ≤ state.nextFresh)
    (windowFits : windowPosition ≤ state.openWires.length) :
    (extractArc seedBoundary (stepCupArc state windowPosition)).internalCupCounts
      = natListInsertAt (extractArc seedBoundary state).internalCupCounts
          (seedBoundary + windowPosition) [1, 1] := by
  obtain ⟨tailCount, tailSpec⟩ := Nat.le.dest windowFits
  obtain ⟨steppedTotalEq, baseTotalEq⟩ := windowSplitTotals seedBoundary state windowPosition tailCount tailSpec
  have windowLeSum : seedBoundary + windowPosition ≤ seedBoundary + state.openWires.length :=
    Nat.add_le_add_left windowFits seedBoundary
  show (List.range (seedBoundary + (stepCupArc state windowPosition).openWires.length)).map
      (internalEventCountAt (stepCupArc state windowPosition).links
        (List.range seedBoundary ++ (stepCupArc state windowPosition).openWires)
        (stepCupArc state windowPosition).cupEventNodes)
    = natListInsertAt ((List.range (seedBoundary + state.openWires.length)).map
        (internalEventCountAt state.links (List.range seedBoundary ++ state.openWires) state.cupEventNodes))
        (seedBoundary + windowPosition) [1, 1]
  have steppedOpenLen : (stepCupArc state windowPosition).openWires.length = state.openWires.length + 2 :=
    natListInsertAt_length state.openWires windowPosition [state.nextFresh, state.nextFresh + 1]
  have steppedCupEv : (stepCupArc state windowPosition).cupEventNodes
      = (state.nextFresh + 2) :: state.cupEventNodes := rfl
  rw [steppedOpenLen, steppedTotalEq, baseTotalEq, steppedCupEv]
  refine internalCountListCorr_ofPointwise
    (internalEventCountAt (stepCupArc state windowPosition).links
      (List.range seedBoundary ++ (stepCupArc state windowPosition).openWires)
      ((state.nextFresh + 2) :: state.cupEventNodes))
    (internalEventCountAt state.links (List.range seedBoundary ++ state.openWires) state.cupEventNodes)
    (seedBoundary + windowPosition) tailCount 1 ?below ?past ?left ?right
  case below =>
    intro candidate candidateMem
    have cLt : candidate < seedBoundary + windowPosition := mem_range_imp_lt candidateMem
    have cInRange : candidate < seedBoundary + state.openWires.length := Nat.lt_of_lt_of_le cLt windowLeSum
    have h := internalCupEventCountAt_stepCupArc_oldPort seedBoundary state windowPosition fresh forest
      seedBelowFresh windowFits candidate cInRange
    rw [freshShiftAbove_ofNotLe (seedBoundary + windowPosition) 2 candidate (Nat.not_le_of_gt cLt)] at h
    exact h
  case past =>
    intro offset offsetMem
    have oLt : offset < tailCount := mem_range_imp_lt offsetMem
    have idxInRange : seedBoundary + windowPosition + offset < seedBoundary + state.openWires.length := by
      rw [baseTotalEq]; exact Nat.add_lt_add_left oLt (seedBoundary + windowPosition)
    have h := internalCupEventCountAt_stepCupArc_oldPort seedBoundary state windowPosition fresh forest
      seedBelowFresh windowFits (seedBoundary + windowPosition + offset) idxInRange
    rw [freshShiftAbove_ofLe (seedBoundary + windowPosition) 2 (seedBoundary + windowPosition + offset)
      (Nat.le_add_right (seedBoundary + windowPosition) offset),
      Nat.add_right_comm (seedBoundary + windowPosition) offset 2] at h
    exact h
  case left =>
    show internalEventCountAt (stepCupArc state windowPosition).links
        (List.range seedBoundary ++ (stepCupArc state windowPosition).openWires)
        ((state.nextFresh + 2) :: state.cupEventNodes) (seedBoundary + windowPosition) = 1
    show countEventsInRoot (stepCupArc state windowPosition).links
        (unionFindRootOf (stepCupArc state windowPosition).links
          (natListGetAt (List.range seedBoundary ++ (stepCupArc state windowPosition).openWires)
            (seedBoundary + windowPosition)))
        ((state.nextFresh + 2) :: state.cupEventNodes) = 1
    rw [legLeftRead seedBoundary state windowPosition windowFits,
      (stepCupArc_freshComponentRoot state windowPosition fresh forest).1]
    show (if unionFindRootOf (stepCupArc state windowPosition).links (state.nextFresh + 2)
          == state.nextFresh + 1 then 1 else 0)
        + countEventsInRoot (stepCupArc state windowPosition).links (state.nextFresh + 1)
            state.cupEventNodes = 1
    rw [(stepCupArc_freshComponentRoot state windowPosition fresh forest).2.2,
      countEventsInRoot_stepCupArc_freshRoot_eq_zero state windowPosition fresh forest
        state.cupEventNodes fresh.2.2.1]
    show (if (state.nextFresh + 1 == state.nextFresh + 1) then 1 else 0) + 0 = 1
    rw [Nat.add_zero]
    cases hc : (state.nextFresh + 1 == state.nextFresh + 1) with
    | true => rfl
    | false =>
        exact Bool.noConfusion
          ((decide_eq_true (rfl : state.nextFresh + 1 = state.nextFresh + 1)).symm.trans hc)
  case right =>
    show internalEventCountAt (stepCupArc state windowPosition).links
        (List.range seedBoundary ++ (stepCupArc state windowPosition).openWires)
        ((state.nextFresh + 2) :: state.cupEventNodes) (seedBoundary + windowPosition + 1) = 1
    show countEventsInRoot (stepCupArc state windowPosition).links
        (unionFindRootOf (stepCupArc state windowPosition).links
          (natListGetAt (List.range seedBoundary ++ (stepCupArc state windowPosition).openWires)
            (seedBoundary + windowPosition + 1)))
        ((state.nextFresh + 2) :: state.cupEventNodes) = 1
    rw [legRightRead seedBoundary state windowPosition windowFits,
      (stepCupArc_freshComponentRoot state windowPosition fresh forest).2.1]
    show (if unionFindRootOf (stepCupArc state windowPosition).links (state.nextFresh + 2)
          == state.nextFresh + 1 then 1 else 0)
        + countEventsInRoot (stepCupArc state windowPosition).links (state.nextFresh + 1)
            state.cupEventNodes = 1
    rw [(stepCupArc_freshComponentRoot state windowPosition fresh forest).2.2,
      countEventsInRoot_stepCupArc_freshRoot_eq_zero state windowPosition fresh forest
        state.cupEventNodes fresh.2.2.1]
    show (if (state.nextFresh + 1 == state.nextFresh + 1) then 1 else 0) + 0 = 1
    rw [Nat.add_zero]
    cases hc : (state.nextFresh + 1 == state.nextFresh + 1) with
    | true => rfl
    | false =>
        exact Bool.noConfusion
          ((decide_eq_true (rfl : state.nextFresh + 1 = state.nextFresh + 1)).symm.trans hc)

end FX1Poly.Polygraph
