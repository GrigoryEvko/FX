import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupStepDropCore
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcFreshSelfSimulation
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupLastCupReadoff
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusCupPreservation
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusPartnerInvolution
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcDisciplineFold
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

/-! ## LEG 3 — the boundary partner list -/

/-- A map whose every entry factors through a shifted base read IS the double map (structural — no `funext`). -/
private theorem listMapFactorsThroughShift (compositeRead freshRead indexShift : Nat → Nat) :
    (candidates : List Nat) →
    (∀ candidate, candidate ∈ candidates → compositeRead candidate = indexShift (freshRead candidate)) →
    candidates.map compositeRead = (candidates.map freshRead).map indexShift
  | [], _ => rfl
  | headCandidate :: rest, pointwise => by
      show compositeRead headCandidate :: rest.map compositeRead
        = indexShift (freshRead headCandidate) :: (rest.map freshRead).map indexShift
      rw [pointwise headCandidate (List.Mem.head rest),
        listMapFactorsThroughShift compositeRead freshRead indexShift rest
          (fun laterCandidate laterMem => pointwise laterCandidate (List.Mem.tail headCandidate laterMem))]

/-- The past-window variant: composite reads at `windowPosition + 2 + offset` factor through fresh reads at
`windowPosition + offset`. -/
private theorem listMapPastWindowFactors (compositeRead freshRead indexShift : Nat → Nat) (windowPosition : Nat) :
    (offsets : List Nat) →
    (∀ offset, offset ∈ offsets →
      compositeRead (windowPosition + 2 + offset) = indexShift (freshRead (windowPosition + offset))) →
    (offsets.map (fun offset => windowPosition + 2 + offset)).map compositeRead
      = ((offsets.map (fun offset => windowPosition + offset)).map freshRead).map indexShift
  | [], _ => rfl
  | headOffset :: rest, pointwise => by
      show compositeRead (windowPosition + 2 + headOffset)
          :: (rest.map (fun offset => windowPosition + 2 + offset)).map compositeRead
        = indexShift (freshRead (windowPosition + headOffset))
          :: ((rest.map (fun offset => windowPosition + offset)).map freshRead).map indexShift
      rw [pointwise headOffset (List.Mem.head rest),
        listMapPastWindowFactors compositeRead freshRead indexShift windowPosition rest
          (fun laterOffset laterMem => pointwise laterOffset (List.Mem.tail headOffset laterMem))]

/-- ★ **A top-of-stack cup splices the short chord into the boundary partner list.**  The composite extract's
partner list equals the base partner list transported through the window index shift `freshShiftAbove (bc + w) 2`
with the new short chord pair `[bc + w + 1, bc + w]` spliced in at the window: old ports keep their partner at the
shifted position (`partnerIndexOf_stepCupArc_old`), and the two fresh legs partner each other
(`generalStateCupForwardPartner` and its involution). -/
theorem diagramPartner_stepCupArc (seedBoundary : Nat) (state : ArcWireState) (windowPosition : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (seedBelowFresh : seedBoundary ≤ state.nextFresh) (census : ArcBoundaryCensus seedBoundary state)
    (windowFits : windowPosition ≤ state.openWires.length) :
    (extractArc seedBoundary (stepCupArc state windowPosition)).diagram.partner
      = natListInsertAt
          ((extractArc seedBoundary state).diagram.partner.map
            (freshShiftAbove (seedBoundary + windowPosition) 2))
          (seedBoundary + windowPosition)
          [seedBoundary + windowPosition + 1, seedBoundary + windowPosition] := by
  obtain ⟨tailCount, tailSpec⟩ := Nat.le.dest windowFits
  have steppedOpenLen : (stepCupArc state windowPosition).openWires.length = state.openWires.length + 2 :=
    natListInsertAt_length state.openWires windowPosition [state.nextFresh, state.nextFresh + 1]
  obtain ⟨steppedTotalEq, baseTotalEq⟩ := windowSplitTotals seedBoundary state windowPosition tailCount tailSpec
  have windowLeSum : seedBoundary + windowPosition ≤ seedBoundary + state.openWires.length :=
    Nat.add_le_add_left windowFits seedBoundary
  -- shorthands
  have censusStepped : ArcBoundaryCensus seedBoundary (stepCupArc state windowPosition) :=
    arcBoundaryCensus_stepCupArc seedBoundary state windowPosition fresh forest seedBelowFresh windowFits census
  -- the two window entries
  have windowLeft : partnerIndexOf (stepCupArc state windowPosition).links
      (List.range seedBoundary ++ (stepCupArc state windowPosition).openWires)
      (seedBoundary + (stepCupArc state windowPosition).openWires.length) (seedBoundary + windowPosition)
      = seedBoundary + windowPosition + 1 :=
    generalStateCupForwardPartner seedBoundary state windowPosition forest fresh seedBelowFresh census windowFits
  have windowFixed : partnerIndexOf (stepCupArc state windowPosition).links
      (List.range seedBoundary ++ (stepCupArc state windowPosition).openWires)
      (seedBoundary + (stepCupArc state windowPosition).openWires.length) (seedBoundary + windowPosition)
      ≠ seedBoundary + windowPosition := by
    rw [windowLeft]
    exact fun heq => Nat.lt_irrefl (seedBoundary + windowPosition)
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self (seedBoundary + windowPosition)) (Nat.le_of_eq heq))
  have windowLeftInRange : seedBoundary + windowPosition
      < seedBoundary + (stepCupArc state windowPosition).openWires.length := by
    rw [steppedOpenLen]
    exact Nat.add_lt_add_left
      (Nat.lt_of_le_of_lt windowFits
        (Nat.lt_of_lt_of_le (Nat.lt_succ_self state.openWires.length)
          (Nat.le_succ (state.openWires.length + 1)))) seedBoundary
  have windowRight : partnerIndexOf (stepCupArc state windowPosition).links
      (List.range seedBoundary ++ (stepCupArc state windowPosition).openWires)
      (seedBoundary + (stepCupArc state windowPosition).openWires.length) (seedBoundary + windowPosition + 1)
      = seedBoundary + windowPosition := by
    have involuted := partnerIndexOf_isInvolution seedBoundary (stepCupArc state windowPosition) censusStepped
      (seedBoundary + windowPosition) windowLeftInRange windowFixed
    rw [windowLeft] at involuted
    exact involuted
  -- unfold both sides to the map forms
  show (List.range (seedBoundary + (stepCupArc state windowPosition).openWires.length)).map
      (partnerIndexOf (stepCupArc state windowPosition).links
        (List.range seedBoundary ++ (stepCupArc state windowPosition).openWires)
        (seedBoundary + (stepCupArc state windowPosition).openWires.length))
    = natListInsertAt
        (((List.range (seedBoundary + state.openWires.length)).map
          (partnerIndexOf state.links (List.range seedBoundary ++ state.openWires)
            (seedBoundary + state.openWires.length))).map (freshShiftAbove (seedBoundary + windowPosition) 2))
        (seedBoundary + windowPosition)
        [seedBoundary + windowPosition + 1, seedBoundary + windowPosition]
  have compositeCandidatesEq : List.range (seedBoundary + (stepCupArc state windowPosition).openWires.length)
      = List.range ((seedBoundary + windowPosition + 2) + tailCount) := by
    rw [steppedOpenLen, steppedTotalEq]
  have freshCandidatesSplitEq : List.range (seedBoundary + state.openWires.length)
      = List.range (seedBoundary + windowPosition)
          ++ (List.range tailCount).map (fun offset => (seedBoundary + windowPosition) + offset) :=
    (congrArg List.range baseTotalEq).trans (rangeSplit (seedBoundary + windowPosition) tailCount)
  have belowSegEq : (List.range (seedBoundary + windowPosition)).map
      (partnerIndexOf (stepCupArc state windowPosition).links
        (List.range seedBoundary ++ (stepCupArc state windowPosition).openWires)
        (seedBoundary + (stepCupArc state windowPosition).openWires.length))
      = ((List.range (seedBoundary + windowPosition)).map
          (partnerIndexOf state.links (List.range seedBoundary ++ state.openWires)
            (seedBoundary + state.openWires.length))).map (freshShiftAbove (seedBoundary + windowPosition) 2) :=
    listMapFactorsThroughShift
      (partnerIndexOf (stepCupArc state windowPosition).links
        (List.range seedBoundary ++ (stepCupArc state windowPosition).openWires)
        (seedBoundary + (stepCupArc state windowPosition).openWires.length))
      (partnerIndexOf state.links (List.range seedBoundary ++ state.openWires)
        (seedBoundary + state.openWires.length))
      (freshShiftAbove (seedBoundary + windowPosition) 2) (List.range (seedBoundary + windowPosition))
      (fun candidate candidateMem => by
        have candidateBelow : candidate < seedBoundary + windowPosition := mem_range_imp_lt candidateMem
        have shiftFixed : freshShiftAbove (seedBoundary + windowPosition) 2 candidate = candidate :=
          freshShiftAbove_ofNotLe (seedBoundary + windowPosition) 2 candidate (Nat.not_le_of_gt candidateBelow)
        have corr := partnerIndexOf_stepCupArc_old seedBoundary state windowPosition fresh forest
          seedBelowFresh windowFits candidate (Nat.lt_of_lt_of_le candidateBelow windowLeSum)
        rw [shiftFixed] at corr
        exact corr)
  have pastSegEq : ((List.range tailCount).map (fun offset => (seedBoundary + windowPosition) + 2 + offset)).map
      (partnerIndexOf (stepCupArc state windowPosition).links
        (List.range seedBoundary ++ (stepCupArc state windowPosition).openWires)
        (seedBoundary + (stepCupArc state windowPosition).openWires.length))
      = (((List.range tailCount).map (fun offset => (seedBoundary + windowPosition) + offset)).map
          (partnerIndexOf state.links (List.range seedBoundary ++ state.openWires)
            (seedBoundary + state.openWires.length))).map (freshShiftAbove (seedBoundary + windowPosition) 2) :=
    listMapPastWindowFactors
      (partnerIndexOf (stepCupArc state windowPosition).links
        (List.range seedBoundary ++ (stepCupArc state windowPosition).openWires)
        (seedBoundary + (stepCupArc state windowPosition).openWires.length))
      (partnerIndexOf state.links (List.range seedBoundary ++ state.openWires)
        (seedBoundary + state.openWires.length))
      (freshShiftAbove (seedBoundary + windowPosition) 2) (seedBoundary + windowPosition) (List.range tailCount)
      (fun offset offsetMem => by
        have offsetBelow : offset < tailCount := mem_range_imp_lt offsetMem
        have idxInRange : seedBoundary + windowPosition + offset < seedBoundary + state.openWires.length := by
          rw [baseTotalEq]; exact Nat.add_lt_add_left offsetBelow (seedBoundary + windowPosition)
        have shiftPast : freshShiftAbove (seedBoundary + windowPosition) 2 (seedBoundary + windowPosition + offset)
            = seedBoundary + windowPosition + offset + 2 :=
          freshShiftAbove_ofLe (seedBoundary + windowPosition) 2 (seedBoundary + windowPosition + offset)
            (Nat.le_add_right (seedBoundary + windowPosition) offset)
        have corr := partnerIndexOf_stepCupArc_old seedBoundary state windowPosition fresh forest
          seedBelowFresh windowFits (seedBoundary + windowPosition + offset) idxInRange
        rw [shiftPast, Nat.add_right_comm (seedBoundary + windowPosition) offset 2] at corr
        exact corr)
  have windowSegEq : ([seedBoundary + windowPosition, seedBoundary + windowPosition + 1]).map
      (partnerIndexOf (stepCupArc state windowPosition).links
        (List.range seedBoundary ++ (stepCupArc state windowPosition).openWires)
        (seedBoundary + (stepCupArc state windowPosition).openWires.length))
      = [seedBoundary + windowPosition + 1, seedBoundary + windowPosition] := by
    show partnerIndexOf (stepCupArc state windowPosition).links
        (List.range seedBoundary ++ (stepCupArc state windowPosition).openWires)
        (seedBoundary + (stepCupArc state windowPosition).openWires.length) (seedBoundary + windowPosition)
      :: partnerIndexOf (stepCupArc state windowPosition).links
          (List.range seedBoundary ++ (stepCupArc state windowPosition).openWires)
          (seedBoundary + (stepCupArc state windowPosition).openWires.length) (seedBoundary + windowPosition + 1)
      :: [] = [seedBoundary + windowPosition + 1, seedBoundary + windowPosition]
    rw [windowLeft, windowRight]
  have frontLengthEq : (((List.range (seedBoundary + windowPosition)).map
      (partnerIndexOf state.links (List.range seedBoundary ++ state.openWires)
        (seedBoundary + state.openWires.length))).map (freshShiftAbove (seedBoundary + windowPosition) 2)).length
      = seedBoundary + windowPosition :=
    (mapLength (freshShiftAbove (seedBoundary + windowPosition) 2)
        ((List.range (seedBoundary + windowPosition)).map
          (partnerIndexOf state.links (List.range seedBoundary ++ state.openWires)
            (seedBoundary + state.openWires.length)))).trans
      ((mapLength
          (partnerIndexOf state.links (List.range seedBoundary ++ state.openWires)
            (seedBoundary + state.openWires.length)) (List.range (seedBoundary + windowPosition))).trans
        (rangeLength (seedBoundary + windowPosition)))
  rw [compositeCandidatesEq, rangeInterleaveAtWindow (seedBoundary + windowPosition) tailCount,
    mapAppend
      (partnerIndexOf (stepCupArc state windowPosition).links
        (List.range seedBoundary ++ (stepCupArc state windowPosition).openWires)
        (seedBoundary + (stepCupArc state windowPosition).openWires.length))
      (List.range (seedBoundary + windowPosition) ++ [seedBoundary + windowPosition, seedBoundary + windowPosition + 1])
      ((List.range tailCount).map (fun offset => (seedBoundary + windowPosition) + 2 + offset)),
    mapAppend
      (partnerIndexOf (stepCupArc state windowPosition).links
        (List.range seedBoundary ++ (stepCupArc state windowPosition).openWires)
        (seedBoundary + (stepCupArc state windowPosition).openWires.length))
      (List.range (seedBoundary + windowPosition))
      [seedBoundary + windowPosition, seedBoundary + windowPosition + 1],
    freshCandidatesSplitEq,
    mapAppend
      (partnerIndexOf state.links (List.range seedBoundary ++ state.openWires)
        (seedBoundary + state.openWires.length))
      (List.range (seedBoundary + windowPosition))
      ((List.range tailCount).map (fun offset => (seedBoundary + windowPosition) + offset)),
    mapAppend (freshShiftAbove (seedBoundary + windowPosition) 2)
      ((List.range (seedBoundary + windowPosition)).map
        (partnerIndexOf state.links (List.range seedBoundary ++ state.openWires)
          (seedBoundary + state.openWires.length)))
      (((List.range tailCount).map (fun offset => (seedBoundary + windowPosition) + offset)).map
        (partnerIndexOf state.links (List.range seedBoundary ++ state.openWires)
          (seedBoundary + state.openWires.length))),
    natListInsertAt_splitsAtLength
      (((List.range (seedBoundary + windowPosition)).map
        (partnerIndexOf state.links (List.range seedBoundary ++ state.openWires)
          (seedBoundary + state.openWires.length))).map (freshShiftAbove (seedBoundary + windowPosition) 2))
      (seedBoundary + windowPosition)
      ((((List.range tailCount).map (fun offset => (seedBoundary + windowPosition) + offset)).map
        (partnerIndexOf state.links (List.range seedBoundary ++ state.openWires)
          (seedBoundary + state.openWires.length))).map (freshShiftAbove (seedBoundary + windowPosition) 2))
      [seedBoundary + windowPosition + 1, seedBoundary + windowPosition] frontLengthEq,
    belowSegEq, windowSegEq, pastSegEq]
  exact appendAssoc
    (((List.range (seedBoundary + windowPosition)).map
      (partnerIndexOf state.links (List.range seedBoundary ++ state.openWires)
        (seedBoundary + state.openWires.length))).map (freshShiftAbove (seedBoundary + windowPosition) 2))
    [seedBoundary + windowPosition + 1, seedBoundary + windowPosition]
    ((((List.range tailCount).map (fun offset => (seedBoundary + windowPosition) + offset)).map
      (partnerIndexOf state.links (List.range seedBoundary ++ state.openWires)
        (seedBoundary + state.openWires.length))).map (freshShiftAbove (seedBoundary + windowPosition) 2))

/-! ## LEG 4 — the assembly: dropping a top-of-stack cup is injective on arc structures

Kit: `natListInsertAt` is left-injective, and `freshShiftAbove` (hence its list-map) is injective — so each field
formula of the three legs is invertible, and the whole `extractArc` is recovered from the stepped `extractArc`. -/

/-- `Nat` right-cancellation, propext-free (structural on the cancelled summand; `Nat.add_right_cancel`
routes through `propext`). -/
private theorem addRightCancel : (summand leftValue rightValue : Nat) →
    leftValue + summand = rightValue + summand → leftValue = rightValue
  | 0, _, _, h => h
  | summand + 1, leftValue, rightValue, h => addRightCancel summand leftValue rightValue (Nat.succ.inj h)

/-- `List` append is left-cancellative (structural on the shared front). -/
private theorem appendLeftCancel : (block first second : List Nat) →
    block ++ first = block ++ second → first = second
  | [], _, _, h => h
  | headWire :: rest, first, second, h => by
      have hcons : headWire :: (rest ++ first) = headWire :: (rest ++ second) := h
      injection hcons with _ tailEq
      exact appendLeftCancel rest first second tailEq

/-- Coerce the position-0 splice through the append form (helper for the injectivity base case). -/
private theorem natListInsertAtZeroCancel (block first second : List Nat)
    (h : natListInsertAt first 0 block = natListInsertAt second 0 block) : first = second := by
  rw [natListInsertAt_zero, natListInsertAt_zero] at h
  exact appendLeftCancel block first second h

/-- `natListInsertAt` at a fixed in-range position with a fixed block is left-injective. -/
private theorem natListInsertAt_leftInjective : (position : Nat) → (block first second : List Nat) →
    position ≤ first.length → position ≤ second.length →
    natListInsertAt first position block = natListInsertAt second position block → first = second
  | 0, block, first, second, _, _, h => natListInsertAtZeroCancel block first second h
  | _ + 1, _, [], _, pLe, _, _ => absurd pLe (Nat.not_succ_le_zero _)
  | _ + 1, _, _ :: _, [], _, pLe, _ => absurd pLe (Nat.not_succ_le_zero _)
  | position + 1, block, headFirst :: restFirst, headSecond :: restSecond, pLeFirst, pLeSecond, h => by
      have hcons : headFirst :: natListInsertAt restFirst position block
          = headSecond :: natListInsertAt restSecond position block := h
      injection hcons with hHead hRest
      rw [hHead, natListInsertAt_leftInjective position block restFirst restSecond
        (Nat.le_of_succ_le_succ pLeFirst) (Nat.le_of_succ_le_succ pLeSecond) hRest]

/-- `freshShiftAbove threshold 2` is injective — by the four threshold-comparison cases (cross cases are
impossible: a below-threshold image is fixed and stays below, an at-or-above image lands two higher). -/
private theorem freshShiftInjective (threshold a b : Nat)
    (shiftEq : freshShiftAbove threshold 2 a = freshShiftAbove threshold 2 b) : a = b := by
  cases Nat.decLe threshold a with
  | isTrue aGe =>
      cases Nat.decLe threshold b with
      | isTrue bGe =>
          rw [freshShiftAbove_ofLe threshold 2 a aGe, freshShiftAbove_ofLe threshold 2 b bGe] at shiftEq
          exact addRightCancel 2 a b shiftEq
      | isFalse bLt =>
          exfalso
          rw [freshShiftAbove_ofLe threshold 2 a aGe, freshShiftAbove_ofNotLe threshold 2 b bLt] at shiftEq
          have bBelow : b < a + 2 :=
            Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_not_le bLt) aGe) (Nat.le_add_right a 2)
          rw [shiftEq] at bBelow
          exact Nat.lt_irrefl b bBelow
  | isFalse aLt =>
      cases Nat.decLe threshold b with
      | isTrue bGe =>
          exfalso
          rw [freshShiftAbove_ofNotLe threshold 2 a aLt, freshShiftAbove_ofLe threshold 2 b bGe] at shiftEq
          have aBelow : a < b + 2 :=
            Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_not_le aLt) bGe) (Nat.le_add_right b 2)
          rw [← shiftEq] at aBelow
          exact Nat.lt_irrefl a aBelow
      | isFalse bLt =>
          rw [freshShiftAbove_ofNotLe threshold 2 a aLt, freshShiftAbove_ofNotLe threshold 2 b bLt] at shiftEq
          exact shiftEq

/-- Mapping `freshShiftAbove threshold 2` over a list is injective. -/
private theorem mapFreshShiftInjective (threshold : Nat) : (first second : List Nat) →
    first.map (freshShiftAbove threshold 2) = second.map (freshShiftAbove threshold 2) → first = second
  | [], [], _ => rfl
  | [], headSecond :: restSecond, h => by
      have hcons : ([] : List Nat)
          = freshShiftAbove threshold 2 headSecond :: restSecond.map (freshShiftAbove threshold 2) := h
      injection hcons
  | headFirst :: restFirst, [], h => by
      have hcons : freshShiftAbove threshold 2 headFirst :: restFirst.map (freshShiftAbove threshold 2)
          = ([] : List Nat) := h
      injection hcons
  | headFirst :: restFirst, headSecond :: restSecond, h => by
      have hcons : freshShiftAbove threshold 2 headFirst :: restFirst.map (freshShiftAbove threshold 2)
          = freshShiftAbove threshold 2 headSecond :: restSecond.map (freshShiftAbove threshold 2) := h
      injection hcons with hHead hRest
      rw [freshShiftInjective threshold headFirst headSecond hHead,
        mapFreshShiftInjective threshold restFirst restSecond hRest]

/-- The right summand of a vanishing `Nat` sum is zero (a `noConfusion` peel). -/
private theorem addRightVanish : {leftSummand rightSummand : Nat} →
    leftSummand + rightSummand = 0 → rightSummand = 0
  | _, 0, _ => rfl
  | _, _ + 1, sumZero => by rw [Nat.add_succ] at sumZero; exact Nat.noConfusion sumZero

/-- A cap-tally-free singleton atom is a cup (routed through the cap count, `propext`-free). -/
private theorem singletonCupArity {overallSource overallTarget : adjunctionGraph.Mode}
    (atom : SpineAtom adjunctionModeSignature overallSource overallTarget) (capZero : capAtomCount [atom] = 0) :
    atom.generatorDom.length = 0 ∧ atom.generatorCod.length = 2 := by
  cases adjunctionSpineAtom_isCupOrCap atom with
  | inl cupArity => exact cupArity
  | inr capArity =>
      exfalso
      have guardTrue : (atom.generatorDom.length == 2 && atom.generatorCod.length == 0) = true := by
        rw [capArity.1, capArity.2]; rfl
      dsimp only [capAtomCount] at capZero
      rw [if_pos guardTrue] at capZero
      exact Nat.noConfusion capZero

/-- Reduce a pure-cup boundary-chained spine `prefixAtoms ++ [lastCup]` to a top-of-stack cup fired onto the
processed prefix, and supply the prefix state's shipped invariants — the shared front-matter of the assembly. -/
private theorem dropStepReduce {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (prefixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (chained : SpineBoundaryChained bottomCount (prefixAtoms ++ [lastCup]))
    (pureCup : AllCupArity (prefixAtoms ++ [lastCup])) :
    arcStructureOfSpineList bottomCount (prefixAtoms ++ [lastCup])
        = extractArc bottomCount
            (stepCupArc (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              prefixAtoms) lastCup.leftContext.length)
      ∧ ArcStateFresh (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          prefixAtoms)
      ∧ isUnionFindForest (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          prefixAtoms).links
      ∧ bottomCount ≤ (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          prefixAtoms).nextFresh
      ∧ ArcBoundaryCensus bottomCount (processArcSpine
          (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) prefixAtoms)
      ∧ lastCup.leftContext.length ≤ (processArcSpine
          (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) prefixAtoms).openWires.length := by
  have lastCapZero : capAtomCount (prefixAtoms ++ [lastCup]) = 0 :=
    capAtomCount_ofAllCupArity (prefixAtoms ++ [lastCup]) pureCup
  have sumZero : capAtomCount prefixAtoms + capAtomCount [lastCup] = 0 :=
    (capAtomCount_append prefixAtoms [lastCup]).symm.trans lastCapZero
  obtain ⟨lastDom, lastCod⟩ := singletonCupArity lastCup (addRightVanish sumZero)
  have prefixChained : SpineBoundaryChained bottomCount prefixAtoms :=
    spineBoundaryChained_prefix_ofAppend prefixAtoms [lastCup] bottomCount chained
  have freshS := arcStateFresh_processArcSpine prefixAtoms
    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) (arcStateFresh_initial bottomCount)
  have forestS := isUnionFindForest_processArcSpine prefixAtoms
    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) isUnionFindForest_nil
  have censusS := arcBoundaryCensus_ofChainedSpineList bottomCount prefixAtoms prefixChained
  have seedBelowS := seedBottomCount_le_processArcSpine_nextFresh bottomCount prefixAtoms
  have domLen := processArcSpine_prefix_openWires_eq_lastDomBoundary bottomCount prefixAtoms lastCup chained
  have windowFitsS : lastCup.leftContext.length
      ≤ (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          prefixAtoms).openWires.length := by
    rw [domLen]
    show lastCup.leftContext.length
      ≤ lastCup.leftContext.length + lastCup.generatorDom.length + lastCup.rightContext.length
    exact Nat.le_trans (Nat.le_add_right lastCup.leftContext.length lastCup.generatorDom.length)
      (Nat.le_add_right (lastCup.leftContext.length + lastCup.generatorDom.length)
        lastCup.rightContext.length)
  have structEq : arcStructureOfSpineList bottomCount (prefixAtoms ++ [lastCup])
      = extractArc bottomCount
          (stepCupArc (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            prefixAtoms) lastCup.leftContext.length) := by
    show extractArc bottomCount
        (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          (prefixAtoms ++ [lastCup]))
      = extractArc bottomCount
          (stepCupArc (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            prefixAtoms) lastCup.leftContext.length)
    rw [processArcSpine_append prefixAtoms [lastCup]
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])]
    show extractArc bottomCount
        (stepArcAtom (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          prefixAtoms) lastCup)
      = extractArc bottomCount
          (stepCupArc (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            prefixAtoms) lastCup.leftContext.length)
    rw [stepArcAtom_eq_stepCupArc
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) prefixAtoms)
      lastCup lastDom lastCod]
  exact ⟨structEq, freshS, forestS, seedBelowS, censusS, windowFitsS⟩

/-- The `extractArc` internal cap-count / cup-count / partner lists all have length `bottomCount + openWires`. -/
private theorem extractArc_internalCapCounts_length (bottomCount : Nat) (state : ArcWireState) :
    (extractArc bottomCount state).internalCapCounts.length = bottomCount + state.openWires.length := by
  show ((List.range (bottomCount + state.openWires.length)).map
      (internalEventCountAt state.links (List.range bottomCount ++ state.openWires)
        state.capEventNodes)).length = bottomCount + state.openWires.length
  rw [mapLength, rangeLength]

private theorem extractArc_internalCupCounts_length (bottomCount : Nat) (state : ArcWireState) :
    (extractArc bottomCount state).internalCupCounts.length = bottomCount + state.openWires.length := by
  show ((List.range (bottomCount + state.openWires.length)).map
      (internalEventCountAt state.links (List.range bottomCount ++ state.openWires)
        state.cupEventNodes)).length = bottomCount + state.openWires.length
  rw [mapLength, rangeLength]

private theorem extractArc_partner_length (bottomCount : Nat) (state : ArcWireState) :
    (extractArc bottomCount state).diagram.partner.length = bottomCount + state.openWires.length := by
  show ((List.range (bottomCount + state.openWires.length)).map
      (partnerIndexOf state.links (List.range bottomCount ++ state.openWires)
        (bottomCount + state.openWires.length))).length = bottomCount + state.openWires.length
  rw [mapLength, rangeLength]

/-- The top-count field rises by exactly two through a top-of-stack cup (defeq to `natListInsertAt_length`). -/
private theorem topCount_stepCupArc (bottomCount : Nat) (state : ArcWireState) (windowPosition : Nat) :
    (extractArc bottomCount (stepCupArc state windowPosition)).diagram.topCount
      = (extractArc bottomCount state).diagram.topCount + 2 :=
  natListInsertAt_length state.openWires windowPosition [state.nextFresh, state.nextFresh + 1]

/-- ★ **Dropping a top-of-stack cup is injective on arc structures (the S3 linchpin).**  If two pure-cup
boundary-chained spines sharing a last cup have equal arc structures, then their prefixes do: the last cup fires
LAST onto each processed prefix as a top-of-stack cup, and each field of the resulting `extractArc` is a fixed
injective image of the prefix's field (`internalCapCounts_stepCupArc` / `internalCupCounts_stepCupArc` splice
`[0,0]`/`[1,1]`, `diagramPartner_stepCupArc` splices the short chord over the shift, `cupCount` adds one,
`topCount` adds two, `capCount`/`loops` are fixed) — so the shared last cup cancels and the prefixes' arc
structures coincide. -/
theorem dropLastCup_arc_injective {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (firstPrefix secondPrefix : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (chainedFirst : SpineBoundaryChained bottomCount (firstPrefix ++ [lastCup]))
    (chainedSecond : SpineBoundaryChained bottomCount (secondPrefix ++ [lastCup]))
    (pureCupFirst : AllCupArity (firstPrefix ++ [lastCup]))
    (pureCupSecond : AllCupArity (secondPrefix ++ [lastCup]))
    (appendedEqual : arcStructureOfSpineList bottomCount (firstPrefix ++ [lastCup])
      = arcStructureOfSpineList bottomCount (secondPrefix ++ [lastCup])) :
    arcStructureOfSpineList bottomCount firstPrefix = arcStructureOfSpineList bottomCount secondPrefix := by
  obtain ⟨structEqFirst, freshFirst, forestFirst, seedBelowFirst, censusFirst, windowFitsFirst⟩ :=
    dropStepReduce bottomCount firstPrefix lastCup chainedFirst pureCupFirst
  obtain ⟨structEqSecond, freshSecond, forestSecond, seedBelowSecond, censusSecond, windowFitsSecond⟩ :=
    dropStepReduce bottomCount secondPrefix lastCup chainedSecond pureCupSecond
  rw [structEqFirst, structEqSecond] at appendedEqual
  -- abbreviations for the two processed prefix states and the window
  show extractArc bottomCount
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) firstPrefix)
    = extractArc bottomCount
        (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) secondPrefix)
  -- per-field inversions
  have eCup : (extractArc bottomCount
        (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) firstPrefix)).cupCount
      = (extractArc bottomCount
        (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) secondPrefix)).cupCount := by
    have h : (extractArc bottomCount
          (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) firstPrefix)).cupCount + 1
        = (extractArc bottomCount
          (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) secondPrefix)).cupCount + 1 :=
      congrArg FullArcStructure.cupCount appendedEqual
    exact addRightCancel 1 _ _ h
  have eCap : (extractArc bottomCount
        (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) firstPrefix)).capCount
      = (extractArc bottomCount
        (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) secondPrefix)).capCount := by
    have h := congrArg FullArcStructure.capCount appendedEqual
    exact h
  have eLoops : (extractArc bottomCount
        (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) firstPrefix)).diagram.loops
      = (extractArc bottomCount
        (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) secondPrefix)).diagram.loops := by
    have h := congrArg DiagramType.loops (congrArg FullArcStructure.diagram appendedEqual)
    exact h
  have eTop : (extractArc bottomCount
        (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) firstPrefix)).diagram.topCount
      = (extractArc bottomCount
        (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) secondPrefix)).diagram.topCount := by
    have h := congrArg DiagramType.topCount (congrArg FullArcStructure.diagram appendedEqual)
    rw [topCount_stepCupArc, topCount_stepCupArc] at h
    exact addRightCancel 2 _ _ h
  have eICap : (extractArc bottomCount
        (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) firstPrefix)).internalCapCounts
      = (extractArc bottomCount
        (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) secondPrefix)).internalCapCounts := by
    have h : natListInsertAt (extractArc bottomCount
            (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) firstPrefix)).internalCapCounts
          (bottomCount + lastCup.leftContext.length) [0, 0]
        = natListInsertAt (extractArc bottomCount
            (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) secondPrefix)).internalCapCounts
          (bottomCount + lastCup.leftContext.length) [0, 0] := by
      rw [← internalCapCounts_stepCupArc bottomCount (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) firstPrefix) lastCup.leftContext.length freshFirst forestFirst
          seedBelowFirst windowFitsFirst,
        ← internalCapCounts_stepCupArc bottomCount (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) secondPrefix) lastCup.leftContext.length freshSecond forestSecond
          seedBelowSecond windowFitsSecond]
      exact congrArg FullArcStructure.internalCapCounts appendedEqual
    exact natListInsertAt_leftInjective (bottomCount + lastCup.leftContext.length) [0, 0] _ _
      (by rw [extractArc_internalCapCounts_length]; exact Nat.add_le_add_left windowFitsFirst bottomCount)
      (by rw [extractArc_internalCapCounts_length]; exact Nat.add_le_add_left windowFitsSecond bottomCount) h
  have eICup : (extractArc bottomCount
        (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) firstPrefix)).internalCupCounts
      = (extractArc bottomCount
        (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) secondPrefix)).internalCupCounts := by
    have h : natListInsertAt (extractArc bottomCount
            (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) firstPrefix)).internalCupCounts
          (bottomCount + lastCup.leftContext.length) [1, 1]
        = natListInsertAt (extractArc bottomCount
            (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) secondPrefix)).internalCupCounts
          (bottomCount + lastCup.leftContext.length) [1, 1] := by
      rw [← internalCupCounts_stepCupArc bottomCount (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) firstPrefix) lastCup.leftContext.length freshFirst forestFirst
          seedBelowFirst windowFitsFirst,
        ← internalCupCounts_stepCupArc bottomCount (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) secondPrefix) lastCup.leftContext.length freshSecond forestSecond
          seedBelowSecond windowFitsSecond]
      exact congrArg FullArcStructure.internalCupCounts appendedEqual
    exact natListInsertAt_leftInjective (bottomCount + lastCup.leftContext.length) [1, 1] _ _
      (by rw [extractArc_internalCupCounts_length]; exact Nat.add_le_add_left windowFitsFirst bottomCount)
      (by rw [extractArc_internalCupCounts_length]; exact Nat.add_le_add_left windowFitsSecond bottomCount) h
  have ePart : (extractArc bottomCount
        (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) firstPrefix)).diagram.partner
      = (extractArc bottomCount
        (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) secondPrefix)).diagram.partner := by
    have hMapEq : (extractArc bottomCount
            (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) firstPrefix)).diagram.partner.map
          (freshShiftAbove (bottomCount + lastCup.leftContext.length) 2)
        = (extractArc bottomCount
            (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) secondPrefix)).diagram.partner.map
          (freshShiftAbove (bottomCount + lastCup.leftContext.length) 2) := by
      apply natListInsertAt_leftInjective (bottomCount + lastCup.leftContext.length)
        [bottomCount + lastCup.leftContext.length + 1, bottomCount + lastCup.leftContext.length] _ _
        (by rw [mapLength, extractArc_partner_length]; exact Nat.add_le_add_left windowFitsFirst bottomCount)
        (by rw [mapLength, extractArc_partner_length]; exact Nat.add_le_add_left windowFitsSecond bottomCount)
      rw [← diagramPartner_stepCupArc bottomCount (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) firstPrefix) lastCup.leftContext.length freshFirst forestFirst
          seedBelowFirst censusFirst windowFitsFirst,
        ← diagramPartner_stepCupArc bottomCount (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) secondPrefix) lastCup.leftContext.length freshSecond forestSecond
          seedBelowSecond censusSecond windowFitsSecond]
      exact congrArg DiagramType.partner (congrArg FullArcStructure.diagram appendedEqual)
    exact mapFreshShiftInjective (bottomCount + lastCup.leftContext.length) _ _ hMapEq
  -- reassemble via double structure eta (FullArcStructure over DiagramType), rewriting each field
  have eBottom : (extractArc bottomCount
        (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) firstPrefix)).diagram.bottomCount
      = (extractArc bottomCount
        (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) secondPrefix)).diagram.bottomCount :=
    rfl
  show FullArcStructure.mk
      (DiagramType.mk
        (extractArc bottomCount
          (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) firstPrefix)).diagram.bottomCount
        (extractArc bottomCount
          (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) firstPrefix)).diagram.topCount
        (extractArc bottomCount
          (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) firstPrefix)).diagram.partner
        (extractArc bottomCount
          (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) firstPrefix)).diagram.loops)
      (extractArc bottomCount
        (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) firstPrefix)).cupCount
      (extractArc bottomCount
        (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) firstPrefix)).capCount
      (extractArc bottomCount
        (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) firstPrefix)).internalCupCounts
      (extractArc bottomCount
        (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) firstPrefix)).internalCapCounts
    = FullArcStructure.mk
      (DiagramType.mk
        (extractArc bottomCount
          (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) secondPrefix)).diagram.bottomCount
        (extractArc bottomCount
          (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) secondPrefix)).diagram.topCount
        (extractArc bottomCount
          (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) secondPrefix)).diagram.partner
        (extractArc bottomCount
          (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) secondPrefix)).diagram.loops)
      (extractArc bottomCount
        (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) secondPrefix)).cupCount
      (extractArc bottomCount
        (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) secondPrefix)).capCount
      (extractArc bottomCount
        (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) secondPrefix)).internalCupCounts
      (extractArc bottomCount
        (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) secondPrefix)).internalCapCounts
  rw [eBottom, eTop, ePart, eLoops, eCup, eCap, eICup, eICap]

end FX1Poly.Polygraph
