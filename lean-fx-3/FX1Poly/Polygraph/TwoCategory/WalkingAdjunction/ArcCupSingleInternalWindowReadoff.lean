import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupSingleWindowReadoff
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWindowLocality
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingComponentAlgebra
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFoldSupport

/-! # ArcCupSingleInternalWindowReadoff — the R1 base case: `internalCupCounts` PINS a single cup's window

The head-cup window read-off residual (the R1 theorem) asks: is a cup head's window a FUNCTION of the arc
structure — and if so, of which field?  `ArcCupHeadWindowSeparation` settled the negative half with a witness:
the boundary matching (`diagram.partner`) is BLIND to the head window, while `internalCupCounts` SEPARATES two
concrete windows.  But the separation is existential (windows `0` vs `2`); the universal function was left owed.

This brick closes the **base case** (single cup, empty tail — `tailList = []`) of the universal R1 read-off, and
it is a clean GREEN pin: for a lone cup folded onto the fresh seed of `bottomCount` bottom ports at window
`windowPosition ≤ bottomCount`, the whole `internalCupCounts` list is `0` everywhere EXCEPT the two adjacent
entries at boundary indices `bottomCount + windowPosition` and `bottomCount + windowPosition + 1`, which read
`1` — the cup's single event node rides the merged leg strand, and only the two leg ports touch it.

Because the pattern of two adjacent `1`s sits at `bottomCount + windowPosition`, the window is a TOTAL FUNCTION
of `internalCupCounts` for the single cup: two single cups with equal `internalCupCounts` have equal windows.
This is exactly the R1 read-off restricted to `tailList = []`.

  * `singleCupInternalCupCount_atLeftLeg` — the count reads `1` at the left leg port `bottomCount + windowPosition`
    (the cup event node is same-component with the left leg via `isSameComponent_unionFindJoin_joined`);
  * `singleCupInternalCupCount_belowWindow` — the count reads `0` at every port strictly below the window
    (the boundary node there sits below `bottomCount`, an untouched singleton disjoint from the leg strand, via
    `nodesEqual_ofConnectedToUntouched`);
  * ★ `singleCupWindowPinnedByInternalCupCounts` — the state-level injectivity: equal single-cup
    `internalCupCounts` force equal windows;
  * ★ `singleCupHeadWindowPinned` — the same pin phrased on `arcStructureOfSpineList bottomCount [cupHead]`, the
    faithful R1 base case: `arcStructureOfSpineList n [A] = arcStructureOfSpineList n [B] ⟹
    A.leftContext.length = B.leftContext.length` for cup atoms `A`, `B`.

Raw Lean 4 + Init; structural recursion / union-find kit only, no `omega` / `simp`-AC / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The fresh seed abbreviation -/

/-- The canonical fresh arc seed over `bottomCount` bottom ports (the initial state of `arcStructureOfSpineList`). -/
private def freshArcSeed (bottomCount : Nat) : ArcWireState :=
  ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []

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

/-- Reading `(List.range total).map mappedFunction` at an in-range index is `mappedFunction index`. -/
private theorem natRangeMapGetAt (total : Nat) (mappedFunction : Nat → Nat) (index : Nat)
    (indexInRange : index < total) :
    natListGetAt ((List.range total).map mappedFunction) index = mappedFunction index := by
  rw [natListGetAt_map_inRange mappedFunction (List.range total) index
      (by rw [rangeLength total]; exact indexInRange),
    rangeGetAt_below total index indexInRange]

/-! ## The single-cup arc-state field forms -/

/-- The single-cup stepped state's open-wire count is `bottomCount + 2` (the two spliced legs). -/
private theorem singleCupOpenWiresLength (bottomCount windowPosition : Nat) :
    (stepCupArc (freshArcSeed bottomCount) windowPosition).openWires.length = bottomCount + 2 := by
  show (natListInsertAt (List.range bottomCount) windowPosition [bottomCount, bottomCount + 1]).length
    = bottomCount + 2
  rw [natListInsertAt_length]
  show (List.range bottomCount).length + 2 = bottomCount + 2
  rw [rangeLength]

/-- **The single-cup internal-count read collapses to one same-component test.**  With exactly one cup event
node (`bottomCount + 2`), the per-port count is `1` when that event node shares the port's component and `0`
otherwise. -/
private theorem singleCupInternalCupCount_asIf (bottomCount windowPosition index : Nat) :
    internalEventCountAt
        (stepCupArc (freshArcSeed bottomCount) windowPosition).links
        (List.range bottomCount ++ (stepCupArc (freshArcSeed bottomCount) windowPosition).openWires)
        (stepCupArc (freshArcSeed bottomCount) windowPosition).cupEventNodes
        index
      = (if isSameComponent
            (unionFindJoin (unionFindJoin [] bottomCount (bottomCount + 1)) (bottomCount + 2) bottomCount)
            (bottomCount + 2)
            (natListGetAt
              (List.range bottomCount
                ++ natListInsertAt (List.range bottomCount) windowPosition [bottomCount, bottomCount + 1])
              index)
          then 1 else 0) := rfl

/-! ## The two zone read-offs -/

/-- ★ **The single-cup internal cup-count reads `1` at the left leg port** `bottomCount + windowPosition`.  The
boundary node there is the left leg `bottomCount`, and the cup event node `bottomCount + 2` is same-component
with it (the outer `unionFindJoin` relates them directly). -/
theorem singleCupInternalCupCount_atLeftLeg (bottomCount windowPosition : Nat)
    (windowFits : windowPosition ≤ bottomCount) :
    internalEventCountAt
        (stepCupArc (freshArcSeed bottomCount) windowPosition).links
        (List.range bottomCount ++ (stepCupArc (freshArcSeed bottomCount) windowPosition).openWires)
        (stepCupArc (freshArcSeed bottomCount) windowPosition).cupEventNodes
        (bottomCount + windowPosition)
      = 1 := by
  rw [singleCupInternalCupCount_asIf]
  have legRead : natListGetAt
      (List.range bottomCount
        ++ natListInsertAt (List.range bottomCount) windowPosition [bottomCount, bottomCount + 1])
      (bottomCount + windowPosition) = bottomCount := by
    have hIdx : bottomCount + windowPosition = windowPosition + (List.range bottomCount).length := by
      rw [rangeLength, Nat.add_comm windowPosition bottomCount]
    rw [hIdx, natListGetAt_append_pastBlock (List.range bottomCount)
        (natListInsertAt (List.range bottomCount) windowPosition [bottomCount, bottomCount + 1]) windowPosition]
    have hInner := natListGetAt_natListInsertAt_inside (List.range bottomCount) windowPosition
      [bottomCount, bottomCount + 1] 0 (Nat.succ_pos 1)
      (by rw [rangeLength]; exact windowFits)
    rw [Nat.add_zero] at hInner
    exact hInner
  rw [legRead]
  have joined : isSameComponent
      (unionFindJoin (unionFindJoin [] bottomCount (bottomCount + 1)) (bottomCount + 2) bottomCount)
      (bottomCount + 2) bottomCount = true :=
    isSameComponent_unionFindJoin_joined (unionFindJoin [] bottomCount (bottomCount + 1))
      (isUnionFindForest_unionFindJoin [] bottomCount (bottomCount + 1) isUnionFindForest_nil)
      (bottomCount + 2) bottomCount
  exact if_pos joined

/-- The boundary read strictly below the window sits below `bottomCount` — either a bottom port (read as
itself) or an open wire copied from the below-window prefix of the seed range (also below `bottomCount`). -/
private theorem singleCupBoundaryRead_belowWindow (bottomCount windowPosition index : Nat)
    (windowFits : windowPosition ≤ bottomCount) (indexBelow : index < bottomCount + windowPosition) :
    natListGetAt
        (List.range bottomCount
          ++ natListInsertAt (List.range bottomCount) windowPosition [bottomCount, bottomCount + 1])
        index < bottomCount := by
  cases Nat.lt_or_ge index bottomCount with
  | inl indexInPrefix =>
      rw [natListGetAt_append_inside (List.range bottomCount)
          (natListInsertAt (List.range bottomCount) windowPosition [bottomCount, bottomCount + 1]) index
          (by rw [rangeLength]; exact indexInPrefix),
        rangeGetAt_below bottomCount index indexInPrefix]
      exact indexInPrefix
  | inr indexAtLeast =>
      obtain ⟨offset, offsetEq⟩ := Nat.le.dest indexAtLeast
      have offsetLtWindow : offset < windowPosition :=
        Nat.lt_of_add_lt_add_left
          (show bottomCount + offset < bottomCount + windowPosition by rw [offsetEq]; exact indexBelow)
      have hIdx : bottomCount + offset = offset + (List.range bottomCount).length := by
        rw [rangeLength, Nat.add_comm]
      have readVal : natListGetAt
          (List.range bottomCount
            ++ natListInsertAt (List.range bottomCount) windowPosition [bottomCount, bottomCount + 1])
          (bottomCount + offset) = offset := by
        rw [hIdx, natListGetAt_append_pastBlock (List.range bottomCount)
            (natListInsertAt (List.range bottomCount) windowPosition [bottomCount, bottomCount + 1])
            offset,
          natListGetAt_natListInsertAt_below (List.range bottomCount) windowPosition
            [bottomCount, bottomCount + 1] offset offsetLtWindow
            (by rw [rangeLength]; exact Nat.lt_of_lt_of_le offsetLtWindow windowFits),
          rangeGetAt_below bottomCount offset (Nat.lt_of_lt_of_le offsetLtWindow windowFits)]
      rw [offsetEq] at readVal
      rw [readVal]
      exact Nat.lt_of_lt_of_le offsetLtWindow windowFits

/-- ★ **The single-cup internal cup-count reads `0` at every port strictly below the window.**  There the
boundary node sits below `bottomCount` — an untouched singleton, disjoint from the leg-strand component the
cup event node rides — so the same-component test fails. -/
theorem singleCupInternalCupCount_belowWindow (bottomCount windowPosition index : Nat)
    (windowFits : windowPosition ≤ bottomCount) (indexBelow : index < bottomCount + windowPosition) :
    internalEventCountAt
        (stepCupArc (freshArcSeed bottomCount) windowPosition).links
        (List.range bottomCount ++ (stepCupArc (freshArcSeed bottomCount) windowPosition).openWires)
        (stepCupArc (freshArcSeed bottomCount) windowPosition).cupEventNodes
        index
      = 0 := by
  rw [singleCupInternalCupCount_asIf]
  have boundBelow := singleCupBoundaryRead_belowWindow bottomCount windowPosition index windowFits indexBelow
  have linksClosed : ∀ edge ∈ unionFindJoin (unionFindJoin [] bottomCount (bottomCount + 1))
        (bottomCount + 2) bottomCount, bottomCount ≤ edge.1 ∧ bottomCount ≤ edge.2 :=
    unionFindJoin_preservesNodeClosure (fun value => bottomCount ≤ value)
      (unionFindJoin [] bottomCount (bottomCount + 1)) (bottomCount + 2) bottomCount
      (unionFindJoin_preservesNodeClosure (fun value => bottomCount ≤ value) [] bottomCount
        (bottomCount + 1) (fun _ edgeInNil => nomatch edgeInNil)
        (Nat.le_refl bottomCount) (Nat.le_succ bottomCount))
      (Nat.le_add_right bottomCount 2) (Nat.le_refl bottomCount)
  have notSame : isSameComponent
      (unionFindJoin (unionFindJoin [] bottomCount (bottomCount + 1)) (bottomCount + 2) bottomCount)
      (bottomCount + 2)
      (natListGetAt
        (List.range bottomCount
          ++ natListInsertAt (List.range bottomCount) windowPosition [bottomCount, bottomCount + 1])
        index) = false := by
    cases hsame : isSameComponent
        (unionFindJoin (unionFindJoin [] bottomCount (bottomCount + 1)) (bottomCount + 2) bottomCount)
        (bottomCount + 2)
        (natListGetAt
          (List.range bottomCount
            ++ natListInsertAt (List.range bottomCount) windowPosition [bottomCount, bottomCount + 1])
          index) with
    | true =>
        have notInSet : ¬ bottomCount ≤ natListGetAt
            (List.range bottomCount
              ++ natListInsertAt (List.range bottomCount) windowPosition [bottomCount, bottomCount + 1])
            index :=
          fun boundaryLarge => Nat.lt_irrefl bottomCount (Nat.lt_of_le_of_lt boundaryLarge boundBelow)
        have nodesEq := nodesEqual_ofConnectedToUntouched (fun value => bottomCount ≤ value)
          (unionFindJoin (unionFindJoin [] bottomCount (bottomCount + 1)) (bottomCount + 2) bottomCount)
          linksClosed (bottomCount + 2)
          (natListGetAt
            (List.range bottomCount
              ++ natListInsertAt (List.range bottomCount) windowPosition [bottomCount, bottomCount + 1])
            index)
          notInSet hsame
        exact absurd (nodesEq ▸ Nat.le_add_right bottomCount 2) notInSet
    | false => rfl
  refine if_neg ?_
  rw [notSame]
  exact fun heq => Bool.noConfusion heq

/-! ## The state-level window pin -/

/-- The `internalCupCounts` field entry at an in-range boundary index is the per-port count. -/
private theorem singleCupInternalCupCountsGetAt (bottomCount windowPosition index : Nat)
    (indexInRange : index < bottomCount + (stepCupArc (freshArcSeed bottomCount) windowPosition).openWires.length) :
    natListGetAt (extractArc bottomCount (stepCupArc (freshArcSeed bottomCount) windowPosition)).internalCupCounts
        index
      = internalEventCountAt
          (stepCupArc (freshArcSeed bottomCount) windowPosition).links
          (List.range bottomCount ++ (stepCupArc (freshArcSeed bottomCount) windowPosition).openWires)
          (stepCupArc (freshArcSeed bottomCount) windowPosition).cupEventNodes
          index := by
  have fieldUnfold : (extractArc bottomCount
        (stepCupArc (freshArcSeed bottomCount) windowPosition)).internalCupCounts
      = (List.range (bottomCount + (stepCupArc (freshArcSeed bottomCount) windowPosition).openWires.length)).map
          (internalEventCountAt
            (stepCupArc (freshArcSeed bottomCount) windowPosition).links
            (List.range bottomCount ++ (stepCupArc (freshArcSeed bottomCount) windowPosition).openWires)
            (stepCupArc (freshArcSeed bottomCount) windowPosition).cupEventNodes) := rfl
  rw [fieldUnfold]
  exact natRangeMapGetAt _ _ index indexInRange

/-- `bottomCount + w < bottomCount + (bottomCount + 2)` for any window `w ≤ bottomCount` — the probe index sits
inside both single-cup boundaries. -/
private theorem probeIndexInRange (bottomCount windowLeft windowProbe : Nat)
    (probeFits : windowProbe ≤ bottomCount) :
    bottomCount + windowProbe
      < bottomCount + (stepCupArc (freshArcSeed bottomCount) windowLeft).openWires.length := by
  rw [singleCupOpenWiresLength bottomCount windowLeft]
  refine Nat.add_lt_add_left ?_ bottomCount
  exact Nat.lt_of_le_of_lt probeFits
    (Nat.lt_of_lt_of_le (Nat.lt_succ_self bottomCount) (Nat.le_succ (bottomCount + 1)))

/-- One direction of the window pin: a strictly smaller window cannot share the larger window's
`internalCupCounts` — the smaller window's left-leg port reads `1` on one side but sits strictly below the
larger window, hence reads `0` on the other. -/
private theorem singleCupWindowPin_notLt (bottomCount windowSmall windowLarge : Nat)
    (smallFits : windowSmall ≤ bottomCount) (largeFits : windowLarge ≤ bottomCount)
    (countsEqual :
      (extractArc bottomCount (stepCupArc (freshArcSeed bottomCount) windowSmall)).internalCupCounts
        = (extractArc bottomCount (stepCupArc (freshArcSeed bottomCount) windowLarge)).internalCupCounts)
    (strict : windowSmall < windowLarge) : False := by
  have smallRead : natListGetAt
      (extractArc bottomCount (stepCupArc (freshArcSeed bottomCount) windowSmall)).internalCupCounts
      (bottomCount + windowSmall) = 1 := by
    rw [singleCupInternalCupCountsGetAt bottomCount windowSmall (bottomCount + windowSmall)
        (probeIndexInRange bottomCount windowSmall windowSmall smallFits)]
    exact singleCupInternalCupCount_atLeftLeg bottomCount windowSmall smallFits
  have largeRead : natListGetAt
      (extractArc bottomCount (stepCupArc (freshArcSeed bottomCount) windowLarge)).internalCupCounts
      (bottomCount + windowSmall) = 0 := by
    rw [singleCupInternalCupCountsGetAt bottomCount windowLarge (bottomCount + windowSmall)
        (probeIndexInRange bottomCount windowLarge windowSmall smallFits)]
    exact singleCupInternalCupCount_belowWindow bottomCount windowLarge (bottomCount + windowSmall) largeFits
      (Nat.add_lt_add_left strict bottomCount)
  have clash : (1 : Nat) = 0 := by
    rw [← smallRead, countsEqual, largeRead]
  exact Nat.noConfusion clash

/-- ★ **`internalCupCounts` pins the single cup's window (state level).**  Two lone cups folded onto the fresh
seed at windows `windowLeft`, `windowRight ≤ bottomCount` with EQUAL `internalCupCounts` have equal windows —
the window is a total function of `internalCupCounts` for the single cup.  This is the R1 head-cup window
read-off restricted to the empty tail. -/
theorem singleCupWindowPinnedByInternalCupCounts (bottomCount windowLeft windowRight : Nat)
    (leftFits : windowLeft ≤ bottomCount) (rightFits : windowRight ≤ bottomCount)
    (countsEqual :
      (extractArc bottomCount (stepCupArc (freshArcSeed bottomCount) windowLeft)).internalCupCounts
        = (extractArc bottomCount (stepCupArc (freshArcSeed bottomCount) windowRight)).internalCupCounts) :
    windowLeft = windowRight := by
  cases Nat.lt_trichotomy windowLeft windowRight with
  | inl leftLt =>
      exact (singleCupWindowPin_notLt bottomCount windowLeft windowRight leftFits rightFits
        countsEqual leftLt).elim
  | inr rest =>
      cases rest with
      | inl windowsEq => exact windowsEq
      | inr rightLt =>
          exact (singleCupWindowPin_notLt bottomCount windowRight windowLeft rightFits leftFits
            countsEqual.symm rightLt).elim

/-! ## The R1 base case on the spine list -/

/-- A cup-arity atom's arc step is the cup step at its window (the two arity equalities pick the cup branch of
`stepArcAtom`'s arity match). -/
private theorem stepArcAtom_cupBranch {signature : ModeSignature} {sourceMode targetMode : signature.graph.Mode}
    (state : ArcWireState) (atom : SpineAtom signature sourceMode targetMode)
    (hasCupDom : atom.generatorDom.length = 0) (hasCupCod : atom.generatorCod.length = 2) :
    stepArcAtom state atom = stepCupArc state atom.leftContext.length := by
  dsimp only [stepArcAtom]
  rw [hasCupDom, hasCupCod]

/-- A single cup head's spine-list arc structure is the folded cup state's extract. -/
private theorem singleCupHead_arcStructure {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount : Nat) (cupHead : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (hasCupDom : cupHead.generatorDom.length = 0) (hasCupCod : cupHead.generatorCod.length = 2) :
    arcStructureOfSpineList bottomCount [cupHead]
      = extractArc bottomCount (stepCupArc (freshArcSeed bottomCount) cupHead.leftContext.length) := by
  show extractArc bottomCount (stepArcAtom (freshArcSeed bottomCount) cupHead)
    = extractArc bottomCount (stepCupArc (freshArcSeed bottomCount) cupHead.leftContext.length)
  rw [stepArcAtom_cupBranch (freshArcSeed bottomCount) cupHead hasCupDom hasCupCod]

/-- ★ **The R1 head-cup window read-off, base case (empty tail).**  For two single cup-headed spines over the
same bottom boundary — a lone cup atom each — equal arc structure forces equal head windows.  The window is
recovered from `internalCupCounts` (the field the boundary matching cannot see), settling the universal R1
read-off at `tailList = []`. -/
theorem singleCupHeadWindowPinned
    {overallSourceLeft overallTargetLeft overallSourceRight overallTargetRight : adjunctionGraph.Mode}
    (bottomCount : Nat)
    (cupHeadLeft : SpineAtom adjunctionModeSignature overallSourceLeft overallTargetLeft)
    (cupHeadRight : SpineAtom adjunctionModeSignature overallSourceRight overallTargetRight)
    (leftDom : cupHeadLeft.generatorDom.length = 0) (leftCod : cupHeadLeft.generatorCod.length = 2)
    (rightDom : cupHeadRight.generatorDom.length = 0) (rightCod : cupHeadRight.generatorCod.length = 2)
    (leftFits : cupHeadLeft.leftContext.length ≤ bottomCount)
    (rightFits : cupHeadRight.leftContext.length ≤ bottomCount)
    (arcEqual : arcStructureOfSpineList bottomCount [cupHeadLeft]
        = arcStructureOfSpineList bottomCount [cupHeadRight]) :
    cupHeadLeft.leftContext.length = cupHeadRight.leftContext.length := by
  refine singleCupWindowPinnedByInternalCupCounts bottomCount
    cupHeadLeft.leftContext.length cupHeadRight.leftContext.length leftFits rightFits ?_
  have countsEqual := congrArg FullArcStructure.internalCupCounts arcEqual
  rw [singleCupHead_arcStructure bottomCount cupHeadLeft leftDom leftCod,
    singleCupHead_arcStructure bottomCount cupHeadRight rightDom rightCod] at countsEqual
  exact countsEqual

/-! ## Honesty marker -/

/-- **Honesty marker — the R1 head-cup window read-off is PROVED for the base case (empty tail).**  For a lone
cup folded onto the fresh seed at window `windowPosition ≤ bottomCount`, `internalCupCounts` reads `1` exactly
at the two leg ports `bottomCount + windowPosition`, `bottomCount + windowPosition + 1`
(`singleCupInternalCupCount_atLeftLeg`) and `0` at every port strictly below the window
(`singleCupInternalCupCount_belowWindow`).  Hence `internalCupCounts` PINS the window: two single cups with
equal `internalCupCounts` have equal windows (`singleCupWindowPinnedByInternalCupCounts`), equivalently equal
`arcStructureOfSpineList bottomCount [cupHead]` forces equal head windows (`singleCupHeadWindowPinned`) — the R1
read-off restricted to `tailList = []`.  This ANSWERS the base-case question the separation witness
(`ArcCupHeadWindowSeparation`) left owed: yes, the head window is a total function of `internalCupCounts` for
the single cup, and the boundary matching is provably not needed.  What this marker does NOT claim: the
non-empty-tail R1 read-off (a processed tail can move the leg strand, so the `1`s no longer sit at
`bottomCount + windowPosition` — that is the general reconstruction residual, `arcCupReselection_exists`), nor
`windowPin` for the through-the-head orbit.  `= true`. -/
def fxMode_hasArcCupSingleInternalWindowReadoff : Bool := true

end FX1Poly.Polygraph
