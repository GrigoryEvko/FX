import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupLastCupReadoff
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapRenameable
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingSwapRenameable
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingVcompLeftCongruence
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFoldCongruence
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingPartnerScan
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineArityDiscipline

/-! # MatchingLastCupShortChord — the width-0 LOCATE port (Track B route 1, brick 1)

The shipped arc-carrier readoff `pureCupSpine_lastCup_isShortChord` reads the last cup of a
boundary-chained pure-cup spine off the ARC structure `arcStructureOfSpineList`, positive-width
gated (its census fold is threaded through the arc↔wire simulation `arcDiagram_eq_matching`,
whose `0 < bottomCount` is genuinely needed).  The width-0 pure-cup determinacy consumer
(`WidthZeroPureCupDeterminacy`) reads the matching off `matchingOfSpineList 0` at `bottomCount =
0`, where that bridge is DEAD.

This file PORTS the readoff to the plain `WireState` / `processSpine` union-find directly at
`bottomCount = 0`, driving location by the width-0 MATCHING links, NOT the arc structure.  The
key structural simplification the port rides (the CAP-door finding): the plain cup step
`stepCup` performs a SINGLE `unionFindJoin state.links nextFresh (nextFresh + 1)` of two FRESH
legs — no cap read, no `nfPos` sentinel — so the whole route runs from the width-`0` seed
`⟨[], [], 0, 0⟩` positivity-free.  The forward-partner uniqueness is a DIRECT freshness argument
(the fresh cup component is exactly the two-element set `{nextFresh, nextFresh+1}`; every other
boundary node is old, `< nextFresh`, with root `< nextFresh`, so it never tests into the fresh
component), NOT the general three-token boundary census.

Ships, all zero-axiom, all positivity-free (no `0 < bottomCount`, no `nfPos`):

  * ★ `stepCupMatching_forwardPartner` — the general-state cup forward-partner readoff on the
    plain matching carrier: folding a single cup at window `w ≤ openWires.length` onto any
    fresh/forest state, the matching partner of boundary index `w` is `w + 1`.  The plain
    analogue of `generalStateCupForwardPartner`, positivity-free by the direct freshness census.
  * ★ `matchingLastCup_isShortChord` — the assembly at `bottomCount = 0`: the last cup of a
    boundary-chained pure-cup spine over the width-`0` bottom boundary reads off
    `matchingOfSpineList 0`'s partner at index `w = lastCup.leftContext.length` as `w + 1`.  The
    plain-carrier, positivity-free analogue of `pureCupSpine_lastCup_isShortChord`.

Raw Lean 4 + Init; structural / fuel recursion, no `omega` / `simp`-AC / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private list / range plumbing (per-file copies, following the codebase pattern) -/

/-- An in-range positional read is a member of the list (structural on the list then the index). -/
private theorem natListGetAt_mem_inRange :
    (wires : List Nat) → (index : Nat) → index < wires.length → natListGetAt wires index ∈ wires
  | [], _, indexInRange => absurd indexInRange (Nat.not_lt_zero _)
  | _ :: _, 0, _ => List.Mem.head _
  | _ :: rest, index + 1, indexInRange =>
      List.Mem.tail _ (natListGetAt_mem_inRange rest index (Nat.lt_of_succ_lt_succ indexInRange))

/-- The scan returns either the exclude fallback or a member of the scanned list (local copy of the
per-file `findPartnerScan_memOrExclude`). -/
private theorem findPartnerScan_memOrExclude (links : List (Nat × Nat))
    (boundaryNodes : List Nat) (rootHere excludeIndex : Nat) : (scanned : List Nat) →
    findPartnerScan links boundaryNodes rootHere excludeIndex scanned = excludeIndex
      ∨ findPartnerScan links boundaryNodes rootHere excludeIndex scanned ∈ scanned
  | [] => Or.inl rfl
  | candidate :: rest => by
      rw [findPartnerScan_cons]
      cases headTest : (candidate != excludeIndex
          && unionFindRootOf links (natListGetAt boundaryNodes candidate) == rootHere) with
      | true => exact Or.inr (List.Mem.head rest)
      | false =>
          cases findPartnerScan_memOrExclude links boundaryNodes rootHere excludeIndex rest with
          | inl isExclude => exact Or.inl isExclude
          | inr isMember => exact Or.inr (List.Mem.tail candidate isMember)

private theorem rangeLoopMem_ofAccumulated : (count : Nat) → (accumulated : List Nat) →
    (target : Nat) → target ∈ accumulated → target ∈ List.range.loop count accumulated
  | 0, _, _, targetMem => targetMem
  | count + 1, accumulated, target, targetMem =>
      rangeLoopMem_ofAccumulated count (count :: accumulated) target (List.Mem.tail count targetMem)

private theorem rangeLoopMem_ofLt : (count : Nat) → (accumulated : List Nat) →
    (target : Nat) → target < count → target ∈ List.range.loop count accumulated
  | 0, _, target, targetBelow => absurd targetBelow (Nat.not_lt_zero target)
  | count + 1, accumulated, target, targetBelow => by
      cases Nat.lt_or_ge target count with
      | inl below => exact rangeLoopMem_ofLt count (count :: accumulated) target below
      | inr atLeast =>
          have targetEq : target = count := Nat.le_antisymm (Nat.le_of_succ_le_succ targetBelow) atLeast
          rw [targetEq]
          exact rangeLoopMem_ofAccumulated count (count :: accumulated) count (List.Mem.head accumulated)

private theorem rangeMem_ofLt (count target : Nat) (targetBelow : target < count) :
    target ∈ List.range count :=
  rangeLoopMem_ofLt count [] target targetBelow

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
  rw [rangeLoopLength count []]; exact Nat.add_zero count

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

private theorem natListGetAt_map_below (mapFunction : Nat → Nat) :
    (list : List Nat) → (index : Nat) → index < list.length →
    natListGetAt (list.map mapFunction) index = mapFunction (natListGetAt list index)
  | [], _, below => absurd below (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: rest, index + 1, below => natListGetAt_map_below mapFunction rest index (Nat.lt_of_succ_lt_succ below)

private theorem natListGetAt_map_range (mapFunction : Nat → Nat) (total index : Nat)
    (inRange : index < total) :
    natListGetAt ((List.range total).map mapFunction) index = mapFunction index := by
  have inRangeList : index < (List.range total).length := by rw [rangeLength]; exact inRange
  rw [natListGetAt_map_below mapFunction (List.range total) index inRangeList,
    rangeGetAt_below total index inRange]

/-! ## The general-state cup forward partner on the plain matching carrier -/

/-- ★ **The plain-matching general-state cup forward-partner readoff (positivity-free).**  Fold a
single cup at window `windowPosition ≤ state.openWires.length` onto ANY fresh/forest state.  The
cup inserts its two fresh legs `state.nextFresh`, `state.nextFresh + 1` at `windowPosition` in the
open-wire list and joins them into one component; every OTHER open wire is old (`< nextFresh`),
so it never tests into that component.  Hence `partnerIndexOf` reads the partner of boundary index
`windowPosition` as `windowPosition + 1`.

The plain analogue of `generalStateCupForwardPartner` (arc carrier), with the arc's outer
event-node join dropped, and with uniqueness discharged by a DIRECT freshness argument (the fresh
cup component is exactly `{nextFresh, nextFresh+1}`) instead of the three-token boundary census —
so NO `0 < nextFresh`, NO `0 < bottomCount`. -/
theorem stepCupMatching_forwardPartner (state : WireState) (windowPosition : Nat)
    (forest : isUnionFindForest state.links) (fresh : WireStateFresh state)
    (windowFits : windowPosition ≤ state.openWires.length) :
    partnerIndexOf (stepCup state windowPosition).links
        (stepCup state windowPosition).openWires
        (stepCup state windowPosition).openWires.length
        windowPosition
      = windowPosition + 1 := by
  obtain ⟨openBelow, linkBelow⟩ := fresh
  -- Abbreviations: the stepped state's links and open wires (both `rfl`).
  have childrenBelow : ∀ edge ∈ state.links, edge.1 < state.nextFresh :=
    fun edge edgeMem => (linkBelow edge edgeMem).1
  have parentsBelow : ∀ edge ∈ state.links, edge.2 < state.nextFresh :=
    fun edge edgeMem => (linkBelow edge edgeMem).2
  -- The two fresh legs are their own roots in the pre-step links.
  have rootLegLeft : unionFindRootOf state.links state.nextFresh = state.nextFresh :=
    unionFindRootOf_eq_self_ofFresh state.nextFresh state.links childrenBelow state.nextFresh
      (Nat.le_refl state.nextFresh)
  have rootLegRight : unionFindRootOf state.links (state.nextFresh + 1) = state.nextFresh + 1 :=
    unionFindRootOf_eq_self_ofFresh state.nextFresh state.links childrenBelow (state.nextFresh + 1)
      (Nat.le_succ state.nextFresh)
  -- Root of the joined component: rootHere = nextFresh + 1.
  have rootHereEq : unionFindRootOf (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
      state.nextFresh = state.nextFresh + 1 := by
    rw [unionFindRootOf_unionFindJoin state.links state.nextFresh (state.nextFresh + 1)
      state.nextFresh forest, rootLegLeft]
    have selfBeq : (state.nextFresh == state.nextFresh) = true := decide_eq_true rfl
    rw [selfBeq]; exact rootLegRight
  -- Root of the right leg in the joined links is also rootHere.
  have rootRightJoin : unionFindRootOf (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
      (state.nextFresh + 1) = state.nextFresh + 1 := by
    rw [unionFindRootOf_unionFindJoin state.links state.nextFresh (state.nextFresh + 1)
      (state.nextFresh + 1) forest, rootLegLeft, rootLegRight]
    split <;> rfl
  -- The stepped open-wire count.
  have hLen : (stepCup state windowPosition).openWires.length = state.openWires.length + 2 :=
    natListInsertAt_length state.openWires windowPosition [state.nextFresh, state.nextFresh + 1]
  -- The two boundary reads at the window resolve to the legs.
  have nodeAtW : natListGetAt (stepCup state windowPosition).openWires windowPosition = state.nextFresh := by
    show natListGetAt (natListInsertAt state.openWires windowPosition [state.nextFresh, state.nextFresh + 1])
        windowPosition = state.nextFresh
    have inside := natListGetAt_natListInsertAt_inside state.openWires windowPosition
      [state.nextFresh, state.nextFresh + 1] 0 (Nat.succ_pos 1) windowFits
    rw [Nat.add_zero] at inside; exact inside
  have nodeAtW1 : natListGetAt (stepCup state windowPosition).openWires (windowPosition + 1)
      = state.nextFresh + 1 :=
    natListGetAt_natListInsertAt_inside state.openWires windowPosition
      [state.nextFresh, state.nextFresh + 1] 1 (Nat.lt_succ_self 1) windowFits
  -- Old boundary nodes (away from the two leg slots) read below `nextFresh`.
  have oldReadBelow : ∀ index, index < state.openWires.length + 2 → index ≠ windowPosition →
      index ≠ windowPosition + 1 →
      natListGetAt (stepCup state windowPosition).openWires index < state.nextFresh := by
    intro index indexLt indexNeW indexNeW1
    show natListGetAt (natListInsertAt state.openWires windowPosition
      [state.nextFresh, state.nextFresh + 1]) index < state.nextFresh
    cases Nat.lt_or_ge index windowPosition with
    | inl below =>
        have indexLtLen : index < state.openWires.length := Nat.lt_of_lt_of_le below windowFits
        rw [natListGetAt_natListInsertAt_below state.openWires windowPosition
          [state.nextFresh, state.nextFresh + 1] index below indexLtLen]
        exact openBelow _ (natListGetAt_mem_inRange state.openWires index indexLtLen)
    | inr atLeast =>
        cases Nat.lt_or_ge index (windowPosition + 1) with
        | inl belowSucc =>
            exact absurd (Nat.le_antisymm (Nat.le_of_lt_succ belowSucc) atLeast) indexNeW
        | inr atLeastSucc =>
            have indexGeW2 : windowPosition + 2 ≤ index := by
              cases Nat.lt_or_ge index (windowPosition + 2) with
              | inl ltTwo => exact absurd (Nat.le_antisymm (Nat.le_of_lt_succ ltTwo) atLeastSucc) indexNeW1
              | inr geTwo => exact geTwo
            obtain ⟨offset, offsetEq⟩ := Nat.le.dest indexGeW2
            have idxForm : index = windowPosition + offset + 2 := by
              rw [← offsetEq, Nat.add_right_comm windowPosition 2 offset]
            have pastRead : natListGetAt (natListInsertAt state.openWires windowPosition
                  [state.nextFresh, state.nextFresh + 1]) index
                = natListGetAt state.openWires (windowPosition + offset) := by
              rw [idxForm]
              exact natListGetAt_natListInsertAt_pastBlock state.openWires windowPosition
                [state.nextFresh, state.nextFresh + 1] offset windowFits
            have windowOffsetLt : windowPosition + offset < state.openWires.length := by
              have shifted : windowPosition + offset + 2 < state.openWires.length + 2 := by
                rw [← idxForm]; exact indexLt
              exact Nat.lt_of_add_lt_add_right shifted
            rw [pastRead]
            exact openBelow _ (natListGetAt_mem_inRange state.openWires (windowPosition + offset)
              windowOffsetLt)
  -- The excluded index reads the left leg; its root in the joined links is `nextFresh + 1`.
  have rootAtExclude : unionFindRootOf (stepCup state windowPosition).links
      (natListGetAt (stepCup state windowPosition).openWires windowPosition) = state.nextFresh + 1 := by
    rw [nodeAtW]; exact rootHereEq
  -- The candidate `windowPosition + 1` shares that root.
  have rootAtCandidate : unionFindRootOf (stepCup state windowPosition).links
      (natListGetAt (stepCup state windowPosition).openWires (windowPosition + 1)) = state.nextFresh + 1 := by
    rw [nodeAtW1]; exact rootRightJoin
  -- Any old node's root is below `nextFresh`, hence not the joined root.
  have rootOldBelow : ∀ node, node < state.nextFresh →
      unionFindRootOf (stepCup state windowPosition).links node < state.nextFresh := by
    intro node nodeBelow
    show unionFindRootOf (unionFindJoin state.links state.nextFresh (state.nextFresh + 1)) node
      < state.nextFresh
    rw [unionFindRootOf_unionFindJoin state.links state.nextFresh (state.nextFresh + 1) node forest,
      rootLegLeft]
    have rootNodeBelow : unionFindRootOf state.links node < state.nextFresh :=
      unionFindRootOf_lt state.nextFresh state.links parentsBelow node nodeBelow
    have guardFalse : (state.nextFresh == unionFindRootOf state.links node) = false :=
      beq_false_of_lt rootNodeBelow
    rw [guardFalse]; exact rootNodeBelow
  -- Assemble the scan uniqueness.
  have candidateLtTotal : windowPosition + 1 < (stepCup state windowPosition).openWires.length := by
    rw [hLen]; exact Nat.succ_lt_succ (Nat.lt_succ_of_le windowFits)
  have candidateMem : windowPosition + 1 ∈ List.range (stepCup state windowPosition).openWires.length :=
    rangeMem_ofLt _ (windowPosition + 1) candidateLtTotal
  have candidateNeExclude : windowPosition + 1 ≠ windowPosition :=
    fun eq => Nat.lt_irrefl windowPosition
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self windowPosition) (Nat.le_of_eq eq))
  -- The partner scan (unfold `partnerIndexOf` at the excluded index).
  show findPartnerScan (stepCup state windowPosition).links (stepCup state windowPosition).openWires
      (unionFindRootOf (stepCup state windowPosition).links
        (natListGetAt (stepCup state windowPosition).openWires windowPosition))
      windowPosition (List.range (stepCup state windowPosition).openWires.length)
    = windowPosition + 1
  rw [rootAtExclude]
  have resultNeExclude := findPartnerScan_neExclude_ofTarget (stepCup state windowPosition).links
    (stepCup state windowPosition).openWires (state.nextFresh + 1) windowPosition
    (List.range (stepCup state windowPosition).openWires.length) (windowPosition + 1)
    candidateMem candidateNeExclude rootAtCandidate
  have resultRoot := findPartnerScan_root_ofFound (stepCup state windowPosition).links
    (stepCup state windowPosition).openWires (state.nextFresh + 1) windowPosition
    (List.range (stepCup state windowPosition).openWires.length) resultNeExclude
  have resultMem : findPartnerScan (stepCup state windowPosition).links
      (stepCup state windowPosition).openWires (state.nextFresh + 1) windowPosition
      (List.range (stepCup state windowPosition).openWires.length)
      ∈ List.range (stepCup state windowPosition).openWires.length := by
    cases findPartnerScan_memOrExclude (stepCup state windowPosition).links
        (stepCup state windowPosition).openWires (state.nextFresh + 1) windowPosition
        (List.range (stepCup state windowPosition).openWires.length) with
    | inl isExclude => exact absurd isExclude resultNeExclude
    | inr isMember => exact isMember
  have resultLtTotal : findPartnerScan (stepCup state windowPosition).links
      (stepCup state windowPosition).openWires (state.nextFresh + 1) windowPosition
      (List.range (stepCup state windowPosition).openWires.length)
      < (stepCup state windowPosition).openWires.length := mem_range_imp_lt resultMem
  -- Decide whether the scan result is the candidate; the "no" branch contradicts the freshness census.
  cases Nat.decEq (findPartnerScan (stepCup state windowPosition).links
      (stepCup state windowPosition).openWires (state.nextFresh + 1) windowPosition
      (List.range (stepCup state windowPosition).openWires.length)) (windowPosition + 1) with
  | isTrue resultEq => exact resultEq
  | isFalse resultNe =>
      exfalso
      have resultLt2 : findPartnerScan (stepCup state windowPosition).links
          (stepCup state windowPosition).openWires (state.nextFresh + 1) windowPosition
          (List.range (stepCup state windowPosition).openWires.length)
          < state.openWires.length + 2 := by rw [← hLen]; exact resultLtTotal
      have nodeBelow := oldReadBelow _ resultLt2 resultNeExclude resultNe
      have rootBelow := rootOldBelow _ nodeBelow
      rw [resultRoot] at rootBelow
      exact Nat.lt_irrefl state.nextFresh (Nat.lt_trans (Nat.lt_succ_self state.nextFresh) rootBelow)

/-! ## Cup-only freshness fold (positivity-free — the cap sentinel never fires) -/

/-- ★ **A pure-cup fold preserves freshness with NO `0 < nextFresh`.**  Each cup step is `stepCup`
(`stepAtom_ofCupArity`), whose freshness preservation `stepCup_wireStateFresh` needs no sentinel;
so the whole pure-cup fold runs from the width-`0` seed `⟨[], [], 0, 0⟩` positivity-free — the
sentinel gate that kills the generic `processSpine_wireStateFresh` at width `0` never fires. -/
theorem wireStateFresh_processSpine_ofAllCup
    {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} :
    (atoms : List (SpineAtom signature overallSource overallTarget)) →
    AllCupArity atoms → (state : WireState) → WireStateFresh state →
    WireStateFresh (processSpine state atoms)
  | [], _, _, fresh => fresh
  | headAtom :: rest, pureCup, state, fresh => by
      cases pureCup with
      | cons headDom headCod restPure =>
          show WireStateFresh (processSpine (stepAtom state headAtom) rest)
          rw [stepAtom_ofCupArity state headAtom headDom headCod]
          exact wireStateFresh_processSpine_ofAllCup rest restPure
            (stepCup state headAtom.leftContext.length)
            (stepCup_wireStateFresh state headAtom.leftContext.length fresh)

/-! ## The prefix fold's open-wire count tracks the boundary chain -/

/-- The prefix fold's open-wire count is the running boundary, and the suffix stays chained there
— the plain-matching analogue of `processArcSpine_openWires_length_ofChainedAppend`. -/
theorem processSpine_openWires_length_ofChainedAppend
    {overallSource overallTarget : adjunctionGraph.Mode} :
    (prefixAtoms suffixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) →
    (state : WireState) → (boundaryLength : Nat) →
    state.openWires.length = boundaryLength →
    SpineBoundaryChained boundaryLength (prefixAtoms ++ suffixAtoms) →
    ∃ midBoundary : Nat,
      (processSpine state prefixAtoms).openWires.length = midBoundary
        ∧ SpineBoundaryChained midBoundary suffixAtoms
  | [], _, _, boundaryLength, tracks, chained => ⟨boundaryLength, tracks, chained⟩
  | headAtom :: restPrefix, suffixAtoms, state, _, tracks, chained => by
      obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
      have headArity := adjunctionSpineAtom_hasCupOrCapArity headAtom
      have tracksEntry : state.openWires.length = headAtom.domBoundaryLength := tracks.trans headFires.symm
      show ∃ midBoundary,
        (processSpine (stepAtom state headAtom) restPrefix).openWires.length = midBoundary
          ∧ SpineBoundaryChained midBoundary suffixAtoms
      exact processSpine_openWires_length_ofChainedAppend restPrefix suffixAtoms
        (stepAtom state headAtom) headAtom.codBoundaryLength
        (stepAtom_openWires_tracksBoundary state headAtom headArity tracksEntry) tailChained

/-- After the prefix, the open-wire count equals the last cup's dom boundary width — plain analogue
of `processArcSpine_prefix_openWires_eq_lastDomBoundary` at the width-`0` seed. -/
theorem processSpine_prefix_openWires_eq_lastDomBoundary
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (prefixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (chained : SpineBoundaryChained bottomCount (prefixAtoms ++ [lastCup])) :
    (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ prefixAtoms).openWires.length
      = lastCup.domBoundaryLength := by
  obtain ⟨midBoundary, lenEq, chainedSuffix⟩ :=
    processSpine_openWires_length_ofChainedAppend prefixAtoms [lastCup]
      ⟨List.range bottomCount, [], bottomCount, 0⟩ bottomCount (rangeLength bottomCount) chained
  have lastFires : lastCup.domBoundaryLength = midBoundary := (spineBoundaryChained_tail chainedSuffix).1
  rw [lenEq]; exact lastFires.symm

/-! ## The chain-prefix inversion (peels the trailing atoms off a chain) -/

/-- Peeling the suffix off a boundary-chained concatenation leaves the prefix chained at the same
entry boundary. -/
theorem spineBoundaryChained_prefix_ofAppend' {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode} :
    (prefixAtoms suffixAtoms : List (SpineAtom signature sourceMode targetMode)) → (boundaryLength : Nat) →
    SpineBoundaryChained boundaryLength (prefixAtoms ++ suffixAtoms) →
    SpineBoundaryChained boundaryLength prefixAtoms
  | [], _, boundaryLength, _ => SpineBoundaryChained.nil boundaryLength
  | headAtom :: restPrefix, suffixAtoms, _, chained => by
      obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
      exact SpineBoundaryChained.cons headAtom headFires
        (spineBoundaryChained_prefix_ofAppend' restPrefix suffixAtoms headAtom.codBoundaryLength tailChained)

/-! ## The assembly: the last cup reads off as a short chord on the width-0 matching -/

/-- The right summand of a `Nat` sum that vanishes is itself zero — a `noConfusion` peel. -/
private theorem addRightVanish : {leftSummand rightSummand : Nat} →
    leftSummand + rightSummand = 0 → rightSummand = 0
  | _, 0, _ => rfl
  | _, _ + 1, sumZero => by rw [Nat.add_succ] at sumZero; exact Nat.noConfusion sumZero

/-- The left summand of a `Nat` sum that vanishes is itself zero — a `noConfusion` peel. -/
private theorem addLeftVanish : {leftSummand rightSummand : Nat} →
    leftSummand + rightSummand = 0 → leftSummand = 0
  | _, 0, sumZero => sumZero
  | _, _ + 1, sumZero => by rw [Nat.add_succ] at sumZero; exact Nat.noConfusion sumZero

/-- A cap-tally-free singleton atom is a cup (routed through the cap count, `propext`-free). -/
private theorem singletonCupArity {overallSource overallTarget : adjunctionGraph.Mode}
    (atom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (capZero : capAtomCount [atom] = 0) :
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

/-- ★ **The last cup of a pure-cup spine reads off as a short chord on the width-`0` matching
(positivity-free).**  The last atom of a boundary-chained pure-cup spine over the width-`0` bottom
boundary fires LAST, so nothing has split its two legs by the time it fires: its window
`w = lastCup.leftContext.length` is still adjacent.  In `matchingOfSpineList 0`'s partner list,
then, index `w` is matched to `w + 1` — the innermost cup on the boundary.

The plain-carrier, positivity-free analogue of `pureCupSpine_lastCup_isShortChord`: the prefix
state carries freshness (`wireStateFresh_processSpine_ofAllCup`, no sentinel) and forest
(`isUnionFindForest_processSpine`), its open-wire count is the last cup's dom boundary width
(`processSpine_prefix_openWires_eq_lastDomBoundary`) bounding the window, and
`stepCupMatching_forwardPartner` reads the two fresh legs off the single `unionFindJoin`.  The
`.partner` list is the boundary-index map, so the raw read reduces to the forward-partner value —
with NO `arcDiagram_eq_matching` bridge and NO `0 < bottomCount`. -/
theorem matchingLastCup_isShortChord
    {overallSource overallTarget : adjunctionGraph.Mode}
    (prefixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (lastCup : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (chained : SpineBoundaryChained 0 (prefixAtoms ++ [lastCup]))
    (pureCup : AllCupArity (prefixAtoms ++ [lastCup])) :
    natListGetAt (matchingOfSpineList 0 (prefixAtoms ++ [lastCup])).partner
        lastCup.leftContext.length
      = lastCup.leftContext.length + 1 := by
  -- the last atom is a cup (read off the cap tally)
  have lastCapZero : capAtomCount (prefixAtoms ++ [lastCup]) = 0 :=
    capAtomCount_ofAllCupArity (prefixAtoms ++ [lastCup]) pureCup
  have sumZero : capAtomCount prefixAtoms + capAtomCount [lastCup] = 0 :=
    (capAtomCount_append prefixAtoms [lastCup]).symm.trans lastCapZero
  obtain ⟨lastDom, lastCod⟩ := singletonCupArity lastCup (addRightVanish sumZero)
  -- the prefix run's invariants (freshness with no sentinel, forest)
  have prefixChained : SpineBoundaryChained 0 prefixAtoms :=
    spineBoundaryChained_prefix_ofAppend' prefixAtoms [lastCup] 0 chained
  have prefixPure : AllCupArity prefixAtoms := by
    -- prefix purity: cap tally of the prefix is zero
    exact allCupArity_ofCapAtomCountZero prefixAtoms (addLeftVanish sumZero)
  have freshS : WireStateFresh (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms) :=
    wireStateFresh_processSpine_ofAllCup prefixAtoms prefixPure ⟨List.range 0, [], 0, 0⟩
      (wireStateFresh_initial 0)
  have forestS : isUnionFindForest (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms).links :=
    isUnionFindForest_processSpine prefixAtoms ⟨List.range 0, [], 0, 0⟩ isUnionFindForest_nil
  have domLen := processSpine_prefix_openWires_eq_lastDomBoundary 0 prefixAtoms lastCup chained
  have windowFitsS : lastCup.leftContext.length
      ≤ (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms).openWires.length := by
    rw [domLen]
    show lastCup.leftContext.length
      ≤ lastCup.leftContext.length + lastCup.generatorDom.length + lastCup.rightContext.length
    exact Nat.le_trans (Nat.le_add_right lastCup.leftContext.length lastCup.generatorDom.length)
      (Nat.le_add_right (lastCup.leftContext.length + lastCup.generatorDom.length)
        lastCup.rightContext.length)
  -- the forward partner at the prefix state
  have partnerEq := stepCupMatching_forwardPartner
    (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms) lastCup.leftContext.length forestS freshS
    windowFitsS
  -- fold the last cup onto the prefix state and reduce the boundary read
  have structEq : matchingOfSpineList 0 (prefixAtoms ++ [lastCup])
      = extractDiagram 0
          (stepCup (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms) lastCup.leftContext.length) := by
    show extractDiagram 0 (processSpine ⟨List.range 0, [], 0, 0⟩ (prefixAtoms ++ [lastCup]))
      = extractDiagram 0
          (stepCup (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms) lastCup.leftContext.length)
    rw [processSpine_append prefixAtoms [lastCup] ⟨List.range 0, [], 0, 0⟩]
    show extractDiagram 0 (stepAtom (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms) lastCup)
      = extractDiagram 0
          (stepCup (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms) lastCup.leftContext.length)
    rw [stepAtom_ofCupArity (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms) lastCup lastDom lastCod]
  rw [structEq]
  -- read the partner list at the window index via the `map`-of-range read-off
  have hStepLen : (stepCup (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms)
        lastCup.leftContext.length).openWires.length
      = (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms).openWires.length + 2 :=
    natListInsertAt_length (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms).openWires
      lastCup.leftContext.length
      [(processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms).nextFresh,
        (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms).nextFresh + 1]
  have windowLtTotal : lastCup.leftContext.length
      < (stepCup (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms)
          lastCup.leftContext.length).openWires.length := by
    rw [hStepLen]
    exact Nat.lt_of_le_of_lt windowFitsS
      (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_succ _))
  have partnerListEq : (extractDiagram 0
        (stepCup (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms) lastCup.leftContext.length)).partner
      = (List.range (0 + (stepCup (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms)
            lastCup.leftContext.length).openWires.length)).map
          (partnerIndexOf (stepCup (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms)
              lastCup.leftContext.length).links
            (List.range 0 ++ (stepCup (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms)
                lastCup.leftContext.length).openWires)
            (0 + (stepCup (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms)
                lastCup.leftContext.length).openWires.length)) := rfl
  rw [partnerListEq]
  rw [natListGetAt_map_range _
    (0 + (stepCup (processSpine ⟨List.range 0, [], 0, 0⟩ prefixAtoms)
        lastCup.leftContext.length).openWires.length)
    lastCup.leftContext.length (by rw [Nat.zero_add]; exact windowLtTotal)]
  -- collapse `0 + · = ·` (`List.range 0 ++ · = ·` is definitional), then apply the forward partner
  rw [Nat.zero_add]
  exact partnerEq

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the width-`0` LOCATE readoff is ported to the plain matching carrier,
positivity-free (Track B route 1, brick 1).**  `stepCupMatching_forwardPartner` reads a folded
cup's forward partner off the plain `stepCup` single `unionFindJoin` by a DIRECT freshness census
(the fresh cup component is exactly `{nextFresh, nextFresh+1}`), with NO `0 < nextFresh`; and
`matchingLastCup_isShortChord` assembles it into the last-cup short-chord readoff on
`matchingOfSpineList 0` for boundary-chained pure-cup spines over the width-`0` bottom boundary,
with NO `arcDiagram_eq_matching` bridge and NO `0 < bottomCount`.  This discharges the LOCATE
brick the general `WidthZeroPureCupDeterminacy` needs, on the plain-`WireState` union-find the
route-1 sort requires.

  What this marker does NOT claim (the residual bricks — no gate flag is flipped):
  * `dropLastCup_matching_injective` — dropping both located last cups is matching-injective
    (brick 3).
  * the width-`0` `locateAux` bubble + the `pureCupSpine_sort`-style assembly closing
    `WidthZeroPureCupDeterminacy` (bricks 2, 4).

  So this file lands the readoff engine; the sort assembly closing the determinacy stays open.
  `convOfMapEq` and the fib-3 gate flags stay `false`.  `= true`. -/
def fxMode_hasMatchingLastCupShortChord : Bool := true

end FX1Poly.Polygraph
