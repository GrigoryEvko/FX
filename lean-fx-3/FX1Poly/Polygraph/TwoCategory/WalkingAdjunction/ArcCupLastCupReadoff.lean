import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupSingleWindowReadoff
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusFold
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPureCupTransfer
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupTailsCountLegs
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcBoundaryTracking
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcFreshDecision
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcTouchConnectivity

/-! # ArcCupLastCupReadoff — the last cup of a pure-cup spine reads off as a short chord (S1 foundations)

The last cup of a boundary-chained pure-cup spine fires LAST, so nothing splits its two legs: its window is
still adjacent in the open-wire list when it fires.  This file assembles the raw-index adjacent-matched-pair
fact `pureCupSpine_lastCup_isShortChord` — at raw top-port index `bottomCount + w` (with
`w = lastCup.leftContext.length`) the extracted-arc partner reads `bottomCount + w + 1` — from four
foundation bricks:

  * `processArcSpine_openWires_length_ofChainedAppend` / `..._prefix_openWires_eq_lastDomBoundary` — the fold's
    open-wire count tracks the boundary chain, so after the prefix it equals the last cup's dom boundary width
    (lifted from the inline `tracksEntry` of the census / perfect-matching folds).  This gives the window bound.
  * `seedBottomCount_le_processArcSpine_nextFresh` — `nextFresh` monotonicity from the canonical seed
    (`bottomCount = seed.nextFresh`).  This gives the `seedBelowFresh` premise.
  * `generalStateCupForwardPartner` — the general-state analogue of the shipped `singleCupForwardPartner`: for a
    cup stepped from an ARBITRARY incoming state carrying the shipped invariants, `partnerIndexOf` reads the
    left leg `state.nextFresh -> state.nextFresh + 1`, via the two `unionFindJoin`s + `partnerIndexOf_uniqueSameComponent`.
  * `pureCupSpine_lastCup_isShortChord` — the assembly, combining the above with `processArcSpine_append`
    (`processArcSpine seed (prefix ++ [cup]) = stepCupArc (processArcSpine seed prefix) w`) and the
    `.diagram.partner -> partnerIndexOf` read reduction.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private range / map plumbing (per-file copy — the sibling kits are file-private) -/

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

private theorem natListMapLength (mapFunction : Nat → Nat) :
    (list : List Nat) → (list.map mapFunction).length = list.length
  | [] => rfl
  | _ :: rest => congrArg Nat.succ (natListMapLength mapFunction rest)

private theorem natListGetAt_map_below (mapFunction : Nat → Nat) :
    (list : List Nat) → (index : Nat) → index < list.length →
    natListGetAt (list.map mapFunction) index = mapFunction (natListGetAt list index)
  | [], _, below => absurd below (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: rest, index + 1, below =>
      natListGetAt_map_below mapFunction rest index (Nat.lt_of_succ_lt_succ below)

private theorem natListGetAt_map_range (mapFunction : Nat → Nat) (total index : Nat)
    (inRange : index < total) :
    natListGetAt ((List.range total).map mapFunction) index = mapFunction index := by
  have inRangeList : index < (List.range total).length := by rw [rangeLength]; exact inRange
  rw [natListGetAt_map_below mapFunction (List.range total) index inRangeList,
    rangeGetAt_below total index inRange]

/-! ## Brick (a) — the fold's open-wire count tracks the boundary chain -/

/-- ★ **The prefix fold's open-wire count is the running boundary, and the suffix stays chained there.**
Folding a boundary-chained adjunction spine `prefixAtoms ++ suffixAtoms` from a state whose open-wire count
tracks the entry boundary lands, after the prefix, at some `midBoundary` where the open-wire count sits and
the suffix is chained — the window-bound substrate the last-cup readoff needs, lifted from the inline
`tracksEntry` of the census / perfect-matching folds. -/
theorem processArcSpine_openWires_length_ofChainedAppend
    {overallSource overallTarget : adjunctionGraph.Mode} :
    (prefixAtoms suffixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) →
    (state : ArcWireState) → (boundaryLength : Nat) →
    state.openWires.length = boundaryLength →
    SpineBoundaryChained boundaryLength (prefixAtoms ++ suffixAtoms) →
    ∃ midBoundary : Nat,
      (processArcSpine state prefixAtoms).openWires.length = midBoundary
        ∧ SpineBoundaryChained midBoundary suffixAtoms
  | [], _, _, boundaryLength, tracks, chained => ⟨boundaryLength, tracks, chained⟩
  | headAtom :: restPrefix, suffixAtoms, state, _, tracks, chained => by
      obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
      have headArity := adjunctionSpineAtom_hasCupOrCapArity headAtom
      have tracksEntry : state.openWires.length = headAtom.domBoundaryLength :=
        tracks.trans headFires.symm
      show ∃ midBoundary,
        (processArcSpine (stepArcAtom state headAtom) restPrefix).openWires.length = midBoundary
          ∧ SpineBoundaryChained midBoundary suffixAtoms
      exact processArcSpine_openWires_length_ofChainedAppend restPrefix suffixAtoms
        (stepArcAtom state headAtom) headAtom.codBoundaryLength
        (stepArcAtom_openWires_tracksBoundary state headAtom headArity tracksEntry)
        tailChained

/-- ★ **After the prefix, the open-wire count equals the last cup's dom boundary width.**  Specialising the
append tracker to the canonical seed and a single trailing atom: the prefix's processed open-wire count is
exactly the boundary at which the last atom fires (`lastCup.domBoundaryLength`).  For a cup this bounds the
window from above (dom width = `leftContext + rightContext`), the window-fit premise the readoff consumes. -/
theorem processArcSpine_prefix_openWires_eq_lastDomBoundary
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (prefixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (chained : SpineBoundaryChained bottomCount (prefixAtoms ++ [lastCup])) :
    (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        prefixAtoms).openWires.length
      = lastCup.domBoundaryLength := by
  obtain ⟨midBoundary, lenEq, chainedSuffix⟩ :=
    processArcSpine_openWires_length_ofChainedAppend prefixAtoms [lastCup]
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) bottomCount
      (rangeLength bottomCount) chained
  have lastFires : lastCup.domBoundaryLength = midBoundary := (spineBoundaryChained_tail chainedSuffix).1
  rw [lenEq]; exact lastFires.symm

/-! ## The chain-prefix inversion (peels the trailing atoms off a chain) -/

/-- Peeling the suffix off a boundary-chained concatenation leaves the prefix chained at the same entry
boundary — the census fold's chain premise for the prefix run. -/
theorem spineBoundaryChained_prefix_ofAppend {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    (prefixAtoms suffixAtoms : List (SpineAtom signature sourceMode targetMode)) → (boundaryLength : Nat) →
    SpineBoundaryChained boundaryLength (prefixAtoms ++ suffixAtoms) →
    SpineBoundaryChained boundaryLength prefixAtoms
  | [], _, boundaryLength, _ => SpineBoundaryChained.nil boundaryLength
  | headAtom :: restPrefix, suffixAtoms, _, chained => by
      obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
      exact SpineBoundaryChained.cons headAtom headFires
        (spineBoundaryChained_prefix_ofAppend restPrefix suffixAtoms headAtom.codBoundaryLength tailChained)

/-! ## Brick (b) — `nextFresh` is above the seed bottom count after any prefix -/

/-- ★ **The seed's bottom count is below the prefix fold's `nextFresh`.**  `nextFresh` never decreases
(`processArcSpine_nextFresh_le`), and the canonical seed starts at `nextFresh = bottomCount` — the
`seedBelowFresh` premise every census / partner brick needs at the prefix state. -/
theorem seedBottomCount_le_processArcSpine_nextFresh
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (prefixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) :
    bottomCount
      ≤ (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          prefixAtoms).nextFresh :=
  processArcSpine_nextFresh_le prefixAtoms (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])

/-! ## Brick (c) — the general-state cup forward partner -/

/-- ★ **The general-state cup forward-partner readoff.**  Fold a single cup at window `windowPosition ≤
state.openWires.length` onto an ARBITRARY incoming state carrying the shipped invariants (fresh, forest,
seed-bound, census).  The cup inserts its two fresh legs (`state.nextFresh`, `state.nextFresh + 1`) at
`windowPosition` in the open-wire list, so in the boundary index space `List.range seedBoundary ++ openWires`
they sit at indices `seedBoundary + windowPosition` and `seedBoundary + windowPosition + 1`.  `stepCupArc`
joins those two legs (and an event node) into one component, so `partnerIndexOf` returns
`seedBoundary + windowPosition + 1` as the partner of `seedBoundary + windowPosition`.  This is the general-state
analogue of the shipped `singleCupForwardPartner` (which is the special case `state = the fresh seed`,
`seedBoundary = state.openWires.length = state.nextFresh = bottomCount`). -/
theorem generalStateCupForwardPartner (seedBoundary : Nat) (state : ArcWireState) (windowPosition : Nat)
    (forest : isUnionFindForest state.links) (fresh : ArcStateFresh state)
    (seedBelowFresh : seedBoundary ≤ state.nextFresh)
    (census : ArcBoundaryCensus seedBoundary state)
    (windowFits : windowPosition ≤ state.openWires.length) :
    partnerIndexOf (stepCupArc state windowPosition).links
        (List.range seedBoundary ++ (stepCupArc state windowPosition).openWires)
        (seedBoundary + (stepCupArc state windowPosition).openWires.length)
        (seedBoundary + windowPosition)
      = seedBoundary + windowPosition + 1 := by
  -- structural reductions of the stepped state's fields (rfl through the stepCupArc def)
  have hOpenWires :
      (stepCupArc state windowPosition).openWires
        = natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1] := rfl
  have hLinks :
      (stepCupArc state windowPosition).links
        = unionFindJoin (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
            (state.nextFresh + 2) state.nextFresh := rfl
  have hRangeLen : (List.range seedBoundary).length = seedBoundary := rangeLength seedBoundary
  have hOpenLen :
      (stepCupArc state windowPosition).openWires.length = state.openWires.length + 2 :=
    natListInsertAt_length state.openWires windowPosition [state.nextFresh, state.nextFresh + 1]
  -- boundary-index bridges (leg indices reshaped into `offset + prefixLength` form)
  have hIdxExclude : seedBoundary + windowPosition = windowPosition + (List.range seedBoundary).length := by
    rw [hRangeLen, Nat.add_comm windowPosition seedBoundary]
  have hIdxCandidate :
      seedBoundary + windowPosition + 1 = (windowPosition + 1) + (List.range seedBoundary).length := by
    rw [hRangeLen, Nat.add_comm (windowPosition + 1) seedBoundary, Nat.add_assoc seedBoundary windowPosition 1]
  -- the two boundary reads resolve to the leg values
  have hExcludeRead :
      natListGetAt
          (List.range seedBoundary ++ (stepCupArc state windowPosition).openWires)
          (seedBoundary + windowPosition)
        = state.nextFresh := by
    rw [hOpenWires, hIdxExclude,
      natListGetAt_append_pastBlock (List.range seedBoundary)
        (natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1]) windowPosition]
    have hInner := natListGetAt_natListInsertAt_inside state.openWires windowPosition
      [state.nextFresh, state.nextFresh + 1] 0 (Nat.succ_pos 1) windowFits
    rw [Nat.add_zero] at hInner
    exact hInner
  have hCandidateRead :
      natListGetAt
          (List.range seedBoundary ++ (stepCupArc state windowPosition).openWires)
          (seedBoundary + windowPosition + 1)
        = state.nextFresh + 1 := by
    rw [hOpenWires, hIdxCandidate,
      natListGetAt_append_pastBlock (List.range seedBoundary)
        (natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1]) (windowPosition + 1)]
    exact natListGetAt_natListInsertAt_inside state.openWires windowPosition
      [state.nextFresh, state.nextFresh + 1] 1 (Nat.lt_succ_self 1) windowFits
  -- the two legs are same-component in the stepped links
  have hInnerSame :
      isSameComponent (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
          state.nextFresh (state.nextFresh + 1) = true :=
    isSameComponent_unionFindJoin_joined state.links forest state.nextFresh (state.nextFresh + 1)
  have hForestInner : isUnionFindForest (unionFindJoin state.links state.nextFresh (state.nextFresh + 1)) :=
    isUnionFindForest_unionFindJoin state.links state.nextFresh (state.nextFresh + 1) forest
  have hOuter :
      isSameComponent (unionFindJoin (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
          (state.nextFresh + 2) state.nextFresh) state.nextFresh (state.nextFresh + 1) = true :=
    isSameComponent_unionFindJoin_ofBase (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
      hForestInner (state.nextFresh + 2) state.nextFresh state.nextFresh (state.nextFresh + 1) hInnerSame
  -- range bounds for the two boundary indices
  have hWinLt : windowPosition < state.openWires.length + 2 :=
    Nat.lt_of_le_of_lt windowFits
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self state.openWires.length) (Nat.le_succ (state.openWires.length + 1)))
  have hWin1Lt : windowPosition + 1 < state.openWires.length + 2 :=
    Nat.lt_of_le_of_lt (Nat.succ_le_succ windowFits) (Nat.lt_succ_self (state.openWires.length + 1))
  -- assemble via the uniqueness finisher
  refine partnerIndexOf_uniqueSameComponent seedBoundary (stepCupArc state windowPosition)
    ?census (seedBoundary + windowPosition) (seedBoundary + windowPosition + 1)
    ?excludeInRange ?candidateInRange ?candidateNeExclude ?sameReads
  case census =>
    exact arcBoundaryCensus_stepCupArc seedBoundary state windowPosition fresh forest
      seedBelowFresh windowFits census
  case excludeInRange =>
    rw [hOpenLen]; exact Nat.add_lt_add_left hWinLt seedBoundary
  case candidateInRange =>
    rw [hOpenLen, Nat.add_assoc seedBoundary windowPosition 1]
    exact Nat.add_lt_add_left hWin1Lt seedBoundary
  case candidateNeExclude =>
    intro hEq
    have hLt : seedBoundary + windowPosition < seedBoundary + windowPosition + 1 :=
      Nat.lt_succ_self (seedBoundary + windowPosition)
    rw [hEq] at hLt
    exact Nat.lt_irrefl (seedBoundary + windowPosition) hLt
  case sameReads =>
    rw [hExcludeRead, hCandidateRead, hLinks]; exact hOuter

/-! ## Brick (d) — the assembly: the last cup reads off as a short chord -/

/-- The right summand of a `Nat` sum that vanishes is itself zero — a `noConfusion` peel, staying
`propext`-free where `Nat.le_zero` / `Nat.eq_zero_of_add_eq_zero_left` would route through simp lemmas. -/
private theorem addRightVanish : {leftSummand rightSummand : Nat} →
    leftSummand + rightSummand = 0 → rightSummand = 0
  | _, 0, _ => rfl
  | leftSummand, rightSummand + 1, sumZero => by
      rw [Nat.add_succ] at sumZero
      exact Nat.noConfusion sumZero

/-- **A cap-tally-free singleton atom is a cup.**  At the walking adjunction every atom is a cup or a cap
(`adjunctionSpineAtom_isCupOrCap`); a cap singleton would tally one, refuting `capAtomCount [atom] = 0`.
Routed through the cap count rather than an indexed `cases` on `AllCupArity`, so it stays `propext`-free. -/
private theorem singletonCupArity {overallSource overallTarget : adjunctionGraph.Mode}
    (atom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (capZero : capAtomCount [atom] = 0) :
    atom.generatorDom.length = 0 ∧ atom.generatorCod.length = 2 := by
  cases adjunctionSpineAtom_isCupOrCap atom with
  | inl cupArity => exact cupArity
  | inr capArity =>
      exfalso
      have guardTrue :
          (atom.generatorDom.length == 2 && atom.generatorCod.length == 0) = true := by
        rw [capArity.1, capArity.2]; rfl
      dsimp only [capAtomCount] at capZero
      rw [if_pos guardTrue] at capZero
      exact Nat.noConfusion capZero

/-- ★ **The last cup of a pure-cup spine reads off as a short chord (raw-index adjacent matched pair).**
The last atom of a boundary-chained pure-cup spine fires LAST, so nothing has split its two legs by the time
it fires: its window `w = lastCup.leftContext.length` is still adjacent in the open-wire list.  In the
extracted arc structure's boundary matching, then, the raw top-port index `bottomCount + w` is matched to
`bottomCount + w + 1` — the innermost cup on the boundary, the D3 spine-readback seed for the last cup.

The prefix state carries every shipped invariant (fresh / forest / census / seed-bound) through the census
fold, and its open-wire count is the last cup's dom boundary width (`processArcSpine_prefix_openWires_eq_lastDomBoundary`),
bounding the window; the last atom's cup arity is read off `pureCup` through the cap count
(`singletonCupArity`); and `generalStateCupForwardPartner` reads the two fresh legs off the two `unionFindJoin`s.
The `.diagram.partner` list is the boundary-index map, so the raw read reduces to the `partnerIndexOf` value. -/
theorem pureCupSpine_lastCup_isShortChord
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (prefixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (chained : SpineBoundaryChained bottomCount (prefixAtoms ++ [lastCup]))
    (bottomPositive : 0 < bottomCount)
    (pureCup : AllCupArity (prefixAtoms ++ [lastCup])) :
    natListGetAt (arcStructureOfSpineList bottomCount (prefixAtoms ++ [lastCup])).diagram.partner
        (bottomCount + lastCup.leftContext.length)
      = bottomCount + lastCup.leftContext.length + 1 := by
  -- the last atom is a cup (read off the cap tally, no indexed inversion)
  have lastCapZero : capAtomCount (prefixAtoms ++ [lastCup]) = 0 :=
    capAtomCount_ofAllCupArity (prefixAtoms ++ [lastCup]) pureCup
  have sumZero : capAtomCount prefixAtoms + capAtomCount [lastCup] = 0 :=
    (capAtomCount_append prefixAtoms [lastCup]).symm.trans lastCapZero
  obtain ⟨lastDom, lastCod⟩ := singletonCupArity lastCup (addRightVanish sumZero)
  -- the prefix run's shipped invariants
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
    exact Nat.le_trans
      (Nat.le_add_right lastCup.leftContext.length lastCup.generatorDom.length)
      (Nat.le_add_right (lastCup.leftContext.length + lastCup.generatorDom.length)
        lastCup.rightContext.length)
  -- the general-state cup forward partner at the prefix state
  have partnerEq := generalStateCupForwardPartner bottomCount
    (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) prefixAtoms)
    lastCup.leftContext.length forestS freshS seedBelowS censusS windowFitsS
  -- fold the last cup onto the prefix state and reduce the boundary read
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
  rw [structEq]
  have hStepLen :
      (stepCupArc (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          prefixAtoms) lastCup.leftContext.length).openWires.length
        = (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            prefixAtoms).openWires.length + 2 :=
    natListInsertAt_length
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) prefixAtoms).openWires
      lastCup.leftContext.length
      [(processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) prefixAtoms).nextFresh,
        (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          prefixAtoms).nextFresh + 1]
  have rangeBound : bottomCount + lastCup.leftContext.length
      < bottomCount
        + (stepCupArc (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            prefixAtoms) lastCup.leftContext.length).openWires.length := by
    rw [hStepLen]
    exact Nat.add_lt_add_left
      (Nat.lt_of_le_of_lt windowFitsS
        (Nat.lt_of_lt_of_le
          (Nat.lt_succ_self
            (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              prefixAtoms).openWires.length)
          (Nat.le_succ
            ((processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              prefixAtoms).openWires.length + 1))))
      bottomCount
  have partnerListEq :
      (extractArc bottomCount
          (stepCupArc (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            prefixAtoms) lastCup.leftContext.length)).diagram.partner
        = (List.range (bottomCount
            + (stepCupArc (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                prefixAtoms) lastCup.leftContext.length).openWires.length)).map
            (partnerIndexOf
              (stepCupArc (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                prefixAtoms) lastCup.leftContext.length).links
              (List.range bottomCount
                ++ (stepCupArc (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                    prefixAtoms) lastCup.leftContext.length).openWires)
              (bottomCount
                + (stepCupArc (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                    prefixAtoms) lastCup.leftContext.length).openWires.length)) := rfl
  rw [partnerListEq, natListGetAt_map_range _
    (bottomCount
      + (stepCupArc (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          prefixAtoms) lastCup.leftContext.length).openWires.length)
    (bottomCount + lastCup.leftContext.length) rangeBound]
  exact partnerEq

end FX1Poly.Polygraph
