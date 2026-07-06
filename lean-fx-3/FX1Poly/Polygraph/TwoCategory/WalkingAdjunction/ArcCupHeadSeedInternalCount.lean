import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupEventNodeSameComponent
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWindowSuffix
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFreshShift

/-! # ArcCupHeadSeedInternalCount — the head cup's `internalCupCounts` contribution is EXACTLY one (R1a)

R1 (the head-cup window is a function of `internalCupCounts`) rests on the foundational readoff of HOW a cup
head increments `internalCupCounts`.  This file lands that readoff on the fresh seed: fold a single cup at
window `windowPosition ≤ bottomCount` onto `ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []`,
and the head cup contributes EXACTLY one cup event to its two leg ports' strand — no more, no less.

The mechanism is `stepCupArc`'s two nested joins: the inner join relates the two fresh legs
(`bottomCount`, `bottomCount + 1`), the outer join relates the fresh cup-event node (`bottomCount + 2`) to the
left leg (already read off, forest-conditioned, by `arcCupEventNode_sameComponent_leftLeg` /
`…_rightLeg`).  On the fresh seed the whole cup-event list is the SINGLETON `[bottomCount + 2]`, so the
per-strand scan `countEventsInRoot` collapses to that one node's membership test — which the same-component
fact makes `true`.  Hence the count is exactly `1`, at BOTH leg ports.

  * `arcCupHeadSeed_cupEventCount_leftLeg` / `…_rightLeg` — the node-level count: scanning the single cup
    event against either leg's root gives `1`;
  * `arcCupHeadSeed_internalCupCountAt_leftLegPort` / `…_rightLegPort` — the port-indexed form: the raw
    `internalEventCountAt` readoff at boundary indices `bottomCount + windowPosition` and
    `bottomCount + windowPosition + 1` is `1`;
  * ★ `arcCupHeadSeed_internalCupCounts_leftLegField` / `…_rightLegField` — the FIELD-level readoff: the
    `FullArcStructure.internalCupCounts` list of `extractArc bottomCount (stepCupArc seed windowPosition)`
    reads `1` at the two leg ports.

This is the foundational quantitative readoff R1 needs (the qualitative same-component facts were shipped in
`ArcCupEventNodeSameComponent`; the partner readoff in `ArcCupSingleWindowReadoff`).  It does NOT by itself
pin the window — it pins the head cup's own count contribution, the increment that R1's function must invert.

Raw Lean 4 + Init; the range-read kit is the established per-file private idiom; per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The range-read kit (the established per-file private idiom) -/

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

/-- The cup-event scan on the fresh-seed SINGLETON `[bottomCount + 2]` is its one membership test. -/
private theorem countEventsInRoot_singletonLocal (links : List (Nat × Nat)) (rootHere eventNode : Nat) :
    countEventsInRoot links rootHere [eventNode]
      = if unionFindRootOf links eventNode == rootHere then 1 else 0 := rfl

/-! ## The node-level count: the head cup contributes exactly one event to each leg's strand -/

/-- ★ **The head cup's cup-event count at its LEFT leg's root is exactly one.**  On the fresh seed the whole
cup-event list is the singleton `[bottomCount + 2]`, so `countEventsInRoot` collapses to that node's one
membership test against the left leg's root — which the shipped same-component fact
(`arcCupEventNode_sameComponent_leftLeg`, forest-conditioned by the empty seed links) makes `true`.  Hence
the count is `1`. -/
theorem arcCupHeadSeed_cupEventCount_leftLeg (bottomCount windowPosition : Nat) :
    countEventsInRoot
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).links
        (unionFindRootOf
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).links
          bottomCount)
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).cupEventNodes
      = 1 := by
  have cupNodes :
      (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).cupEventNodes
        = [bottomCount + 2] := rfl
  have same :
      isSameComponent
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).links
          (bottomCount + 2) bottomCount = true :=
    arcCupEventNode_sameComponent_leftLeg
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition isUnionFindForest_nil
  have cond :
      (unionFindRootOf
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).links
          (bottomCount + 2)
        == unionFindRootOf
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).links
          bottomCount) = true := same
  rw [cupNodes, countEventsInRoot_singletonLocal]
  exact if_pos cond

/-- ★ **The head cup's cup-event count at its RIGHT leg's root is exactly one.**  The right-leg sibling of
`arcCupHeadSeed_cupEventCount_leftLeg`: the same singleton scan, closed by
`arcCupEventNode_sameComponent_rightLeg` (the event node rides the merged strand onto the right leg too). -/
theorem arcCupHeadSeed_cupEventCount_rightLeg (bottomCount windowPosition : Nat) :
    countEventsInRoot
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).links
        (unionFindRootOf
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).links
          (bottomCount + 1))
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).cupEventNodes
      = 1 := by
  have cupNodes :
      (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).cupEventNodes
        = [bottomCount + 2] := rfl
  have same :
      isSameComponent
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).links
          (bottomCount + 2) (bottomCount + 1) = true :=
    arcCupEventNode_sameComponent_rightLeg
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition isUnionFindForest_nil
  have cond :
      (unionFindRootOf
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).links
          (bottomCount + 2)
        == unionFindRootOf
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).links
          (bottomCount + 1)) = true := same
  rw [cupNodes, countEventsInRoot_singletonLocal]
  exact if_pos cond

/-! ## The port-indexed readoff: the two leg boundary indices carry the count one -/

/-- The left-leg boundary read: at boundary index `bottomCount + windowPosition` the seed's open-wire block
holds the fresh left leg `bottomCount`. -/
private theorem seedLeftLegRead (bottomCount windowPosition : Nat)
    (windowFits : windowPosition ≤ bottomCount) :
    natListGetAt
        (List.range bottomCount
          ++ (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).openWires)
        (bottomCount + windowPosition)
      = bottomCount := by
  have hOpenWires :
      (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).openWires
        = natListInsertAt (List.range bottomCount) windowPosition [bottomCount, bottomCount + 1] := rfl
  have hWindowLeRangeLen : windowPosition ≤ (List.range bottomCount).length := by
    rw [rangeLength bottomCount]; exact windowFits
  have hIdxExclude : bottomCount + windowPosition = windowPosition + (List.range bottomCount).length := by
    rw [rangeLength bottomCount, Nat.add_comm windowPosition bottomCount]
  rw [hOpenWires, hIdxExclude,
    natListGetAt_append_pastBlock (List.range bottomCount)
      (natListInsertAt (List.range bottomCount) windowPosition [bottomCount, bottomCount + 1]) windowPosition]
  have hInner := natListGetAt_natListInsertAt_inside (List.range bottomCount) windowPosition
    [bottomCount, bottomCount + 1] 0 (Nat.succ_pos 1) hWindowLeRangeLen
  rw [Nat.add_zero] at hInner
  exact hInner

/-- The right-leg boundary read: at boundary index `bottomCount + windowPosition + 1` the seed's open-wire
block holds the fresh right leg `bottomCount + 1`. -/
private theorem seedRightLegRead (bottomCount windowPosition : Nat)
    (windowFits : windowPosition ≤ bottomCount) :
    natListGetAt
        (List.range bottomCount
          ++ (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).openWires)
        (bottomCount + windowPosition + 1)
      = bottomCount + 1 := by
  have hOpenWires :
      (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).openWires
        = natListInsertAt (List.range bottomCount) windowPosition [bottomCount, bottomCount + 1] := rfl
  have hWindowLeRangeLen : windowPosition ≤ (List.range bottomCount).length := by
    rw [rangeLength bottomCount]; exact windowFits
  have hIdxCandidate :
      bottomCount + windowPosition + 1 = (windowPosition + 1) + (List.range bottomCount).length := by
    rw [rangeLength bottomCount, Nat.add_comm (windowPosition + 1) bottomCount,
      Nat.add_assoc bottomCount windowPosition 1]
  rw [hOpenWires, hIdxCandidate,
    natListGetAt_append_pastBlock (List.range bottomCount)
      (natListInsertAt (List.range bottomCount) windowPosition [bottomCount, bottomCount + 1]) (windowPosition + 1)]
  exact natListGetAt_natListInsertAt_inside (List.range bottomCount) windowPosition
    [bottomCount, bottomCount + 1] 1 (Nat.lt_succ_self 1) hWindowLeRangeLen

/-- ★ **The head cup's raw internal cup-count at its LEFT leg port is one.**  The port-indexed form of
`arcCupHeadSeed_cupEventCount_leftLeg`: `internalEventCountAt` at boundary index `bottomCount + windowPosition`
first reads the left leg `bottomCount` off the spliced open-wire block, then the node-level count closes it. -/
theorem arcCupHeadSeed_internalCupCountAt_leftLegPort (bottomCount windowPosition : Nat)
    (windowFits : windowPosition ≤ bottomCount) :
    internalEventCountAt
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).links
        (List.range bottomCount
          ++ (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).openWires)
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).cupEventNodes
        (bottomCount + windowPosition)
      = 1 := by
  show countEventsInRoot
      (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).links
      (unionFindRootOf
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).links
        (natListGetAt
          (List.range bottomCount
            ++ (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).openWires)
          (bottomCount + windowPosition)))
      (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).cupEventNodes
    = 1
  rw [seedLeftLegRead bottomCount windowPosition windowFits]
  exact arcCupHeadSeed_cupEventCount_leftLeg bottomCount windowPosition

/-- ★ **The head cup's raw internal cup-count at its RIGHT leg port is one.**  The right-leg sibling: reads
`bottomCount + 1` off the block, then `arcCupHeadSeed_cupEventCount_rightLeg`. -/
theorem arcCupHeadSeed_internalCupCountAt_rightLegPort (bottomCount windowPosition : Nat)
    (windowFits : windowPosition ≤ bottomCount) :
    internalEventCountAt
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).links
        (List.range bottomCount
          ++ (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).openWires)
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).cupEventNodes
        (bottomCount + windowPosition + 1)
      = 1 := by
  show countEventsInRoot
      (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).links
      (unionFindRootOf
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).links
        (natListGetAt
          (List.range bottomCount
            ++ (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).openWires)
          (bottomCount + windowPosition + 1)))
      (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).cupEventNodes
    = 1
  rw [seedRightLegRead bottomCount windowPosition windowFits]
  exact arcCupHeadSeed_cupEventCount_rightLeg bottomCount windowPosition

/-! ## The field-level readoff: the `internalCupCounts` list reads one at both leg ports -/

/-- The single-cup stepped state's open-wire count is `bottomCount + 2` (the two fresh legs inserted). -/
private theorem seedCupOpenLen (bottomCount windowPosition : Nat) :
    (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).openWires.length
      = bottomCount + 2 :=
  (natListInsertAt_length (List.range bottomCount) windowPosition [bottomCount, bottomCount + 1]).trans
    (congrArg (fun measured => measured + [bottomCount, bottomCount + 1].length) (rangeLength bottomCount))

/-- Read the `internalCupCounts` list of the single-cup extract at an in-range boundary index — the field
scan commutes with the range read (`natListGetAt_map_inRange` / `rangeGetAt_below`) down to the raw
`internalEventCountAt` there. -/
private theorem seedInternalCupCountsGetAt (bottomCount windowPosition index : Nat)
    (indexInRange : index < bottomCount
      + (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).openWires.length) :
    natListGetAt
        (extractArc bottomCount
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition)).internalCupCounts
        index
      = internalEventCountAt
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).links
          (List.range bottomCount
            ++ (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).openWires)
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).cupEventNodes
          index := by
  show natListGetAt
      ((List.range
          (bottomCount
            + (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).openWires.length)).map
        (internalEventCountAt
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).links
          (List.range bottomCount
            ++ (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).openWires)
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).cupEventNodes))
      index
    = _
  rw [natListGetAt_map_inRange _ (List.range _) index
      (by rw [rangeLength _]; exact indexInRange),
    rangeGetAt_below _ index indexInRange]

/-- ★ **The head cup's `internalCupCounts` field reads one at its LEFT leg port.**  The `FullArcStructure`
field-level form: `(extractArc bottomCount (stepCupArc seed windowPosition)).internalCupCounts` reads `1` at
boundary index `bottomCount + windowPosition` — the field scan commutes with the range read down to the raw
port readoff `arcCupHeadSeed_internalCupCountAt_leftLegPort`. -/
theorem arcCupHeadSeed_internalCupCounts_leftLegField (bottomCount windowPosition : Nat)
    (windowFits : windowPosition ≤ bottomCount) :
    natListGetAt
        (extractArc bottomCount
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition)).internalCupCounts
        (bottomCount + windowPosition)
      = 1 := by
  have indexInRange : bottomCount + windowPosition
      < bottomCount
        + (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).openWires.length := by
    rw [seedCupOpenLen bottomCount windowPosition]
    exact Nat.add_lt_add_left
      (Nat.lt_of_le_of_lt windowFits
        (Nat.lt_of_lt_of_le (Nat.lt_succ_self bottomCount) (Nat.le_succ (bottomCount + 1)))) bottomCount
  rw [seedInternalCupCountsGetAt bottomCount windowPosition (bottomCount + windowPosition) indexInRange]
  exact arcCupHeadSeed_internalCupCountAt_leftLegPort bottomCount windowPosition windowFits

/-- ★ **The head cup's `internalCupCounts` field reads one at its RIGHT leg port.**  The right-leg sibling,
at boundary index `bottomCount + windowPosition + 1`. -/
theorem arcCupHeadSeed_internalCupCounts_rightLegField (bottomCount windowPosition : Nat)
    (windowFits : windowPosition ≤ bottomCount) :
    natListGetAt
        (extractArc bottomCount
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition)).internalCupCounts
        (bottomCount + windowPosition + 1)
      = 1 := by
  have indexInRange : bottomCount + windowPosition + 1
      < bottomCount
        + (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition).openWires.length := by
    rw [seedCupOpenLen bottomCount windowPosition, Nat.add_assoc bottomCount windowPosition 1]
    exact Nat.add_lt_add_left
      (Nat.lt_of_le_of_lt (Nat.succ_le_succ windowFits) (Nat.lt_succ_self (bottomCount + 1))) bottomCount
  rw [seedInternalCupCountsGetAt bottomCount windowPosition (bottomCount + windowPosition + 1) indexInRange]
  exact arcCupHeadSeed_internalCupCountAt_rightLegPort bottomCount windowPosition windowFits

/-! ## Honesty marker -/

/-- **Honesty marker — the head cup's `internalCupCounts` contribution is EXACTLY one (R1a).**  On the fresh
seed a single cup at window `windowPosition ≤ bottomCount` contributes exactly one cup event to its two leg
ports' strand: node-level (`arcCupHeadSeed_cupEventCount_leftLeg` / `…_rightLeg`), port-indexed
(`arcCupHeadSeed_internalCupCountAt_leftLegPort` / `…_rightLegPort`), and field-level on the
`FullArcStructure.internalCupCounts` list (`arcCupHeadSeed_internalCupCounts_leftLegField` / `…_rightLegField`).
The mechanism is `stepCupArc`'s singleton cup-event list `[bottomCount + 2]` and its two nested joins that put
that event on the merged leg strand (the shipped `arcCupEventNode_sameComponent_leftLeg` / `…_rightLeg`).  This
is the foundational quantitative increment R1's window function must invert.  What this marker does NOT claim:
the head cup's contribution UNDER A PROCESSED TAIL (the tail lifts each strand's count by the merged fresh
census — `arcCupHeadFolded_internalCupCountsCorr`, unconditional), the window PIN itself, nor the universal
`internalCupCounts → window` function (R1).  `= true`. -/
def fxMode_hasArcCupHeadSeedInternalCount : Bool := true

end FX1Poly.Polygraph
