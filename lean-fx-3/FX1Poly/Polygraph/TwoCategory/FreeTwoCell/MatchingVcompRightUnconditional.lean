import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingVcompRightCongruence
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingCountRestricted
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingCountRename

/-! # mode-3 — the unconditional vcomp-RIGHT matching congruence (MODE3-D, SAT-D6 closes)

The empty-MID-boundary leg and the unconditional headline.  When the shared mid boundary is
empty the canonical β-runs start at the DEGENERATE seed `⟨[], [], 0, 0⟩`, where the loop
read-off's positivity guard fails — the leg routes around it:

  * **the proxy detour**: the relative-run read-off at the counter-shift PROXY `⟨[], [], 1, 0⟩`
    (whose conditions package holds) exposes the proxy run's loops as the count of the
    DEGENERATE trace renamed by the proxy wire map; the rename invariance strips the map, so
    the counter-shifted extract equality yields the degenerate traces' loop-count equality;
  * **the fresh-zone collapse**: with no open wires every renamed trace node lands in the
    fresh zone while the mid-state links live strictly below it, so the restricted count
    congruence (`countJoinEventLoops_congrOnNodeSet` at the at-or-above-base node set)
    trades the mid links for the empty base — fresh-zone nodes are parentless on both;
  * the VIEW leg (`compositeBoundaryView_agrees_ofExtractEq`) and the reconstruction
    (`matchingConnectivityViewSim_ofExtractEq`) never needed positivity — they run verbatim.

  * ★ `processSpine_extract_eq_ofCanonicalExtractEq_emptyBoundary` — the D5 statement at an
    empty boundary;
  * `extractAfterProcessing_vcompRight_ofSeed_emptyMid` — the seed-generic core, empty-mid leg;
  * ★ `matchingOf_vcompRight_congruence` — the UNCONDITIONAL walking-adjunction headline:
    mid-boundary dispatch onto the shipped positive-mid inhabitant or this leg, with the
    positive-source / empty-source dispatch inside each.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Nat + range + lookup plumbing (hand-rolled private copies; core equivalents leak
propext) -/

private theorem natAddRightCancel : (cancelled : Nat) → {leftSum rightSum : Nat} →
    leftSum + cancelled = rightSum + cancelled → leftSum = rightSum
  | 0, _, _, sumsEq => sumsEq
  | cancelled + 1, _, _, sumsEq => natAddRightCancel cancelled (Nat.succ.inj sumsEq)

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

/-- Every member of a pairwise-renamed event list has a preimage event in the original. -/
private theorem pairPreimage_ofMapMember (sigma : Nat → Nat) :
    (events : List (Nat × Nat)) → (pair : Nat × Nat) →
    pair ∈ events.map (fun event => (sigma event.1, sigma event.2)) →
    ∃ sourceEvent, sourceEvent ∈ events
      ∧ pair = (sigma sourceEvent.1, sigma sourceEvent.2)
  | [], _, membership => nomatch membership
  | headEvent :: restEvents, pair, membership => by
      cases membership with
      | head => exact ⟨headEvent, List.Mem.head restEvents, rfl⟩
      | tail _ innerMembership =>
          have ⟨sourceEvent, sourceMembership, pairEq⟩ :=
            pairPreimage_ofMapMember sigma restEvents pair innerMembership
          exact ⟨sourceEvent, List.Mem.tail headEvent sourceMembership, pairEq⟩

/-- A node at or above a bound that dominates every stored edge has no parent entry. -/
private theorem unionFindParent_none_ofBound (bound : Nat) :
    (links : List (Nat × Nat)) →
    (∀ edge ∈ links, edge.1 < bound ∧ edge.2 < bound) →
    (node : Nat) → bound ≤ node →
    unionFindParent links node = none
  | [], _, _, _ => rfl
  | (childNode, parentNode) :: restLinks, edgesBounded, node, boundLeNode => by
      have childBelow : childNode < bound :=
        (edgesBounded (childNode, parentNode) (List.Mem.head restLinks)).1
      have childLtNode : childNode < node := Nat.lt_of_lt_of_le childBelow boundLeNode
      have beqFalse : (childNode == node) = false := by
        cases headTest : childNode == node with
        | false => rfl
        | true =>
            exact absurd (of_decide_eq_true headTest ▸ childLtNode) (Nat.lt_irrefl node)
      show (if childNode == node then some parentNode
        else unionFindParent restLinks node) = none
      rw [beqFalse]
      exact unionFindParent_none_ofBound bound restLinks
        (fun edge edgeMembership =>
          edgesBounded edge (List.Mem.tail (childNode, parentNode) edgeMembership))
        node boundLeNode

/-- A parentless node is its own root — one fuel unfold plus the lookup rewrite. -/
private theorem unionFindRootOf_ofParentless (links : List (Nat × Nat)) (node : Nat)
    (parentless : unionFindParent links node = none) :
    unionFindRootOf links node = node := by
  show (match unionFindParent links node with
    | none => node
    | some parent => unionFindRoot links.length links parent) = node
  rw [parentless]

/-! ## The empty-boundary relative extract agreement -/

/-- ★ **Equal canonical extracts transfer to any disciplined mid-state, EMPTY boundary.**
The VIEW leg and the reconstruction run verbatim (they never needed positivity); the LOOP
leg replaces the D5 gluing with the proxy detour (the degenerate traces' loop counts read
off through the counter-shift proxy's relative run) and the fresh-zone collapse (with no
open wires every renamed node is fresh-zone, and fresh-zone nodes are parentless over the
below-base mid links, so the mid links count as the empty base). -/
theorem processSpine_extract_eq_ofCanonicalExtractEq_emptyBoundary {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (baseCount : Nat) (midState : WireState)
    (atomsAlpha atomsBeta : List (SpineAtom signature sourceMode targetMode))
    (chainedAlpha : SpineBoundaryChained 0 atomsAlpha)
    (arityAlpha : SpineHasCupCapAtoms atomsAlpha)
    (chainedBeta : SpineBoundaryChained 0 atomsBeta)
    (arityBeta : SpineHasCupCapAtoms atomsBeta)
    (midTracks : midState.openWires.length = 0)
    (fresh : WireStateFresh midState) (nfPos : 0 < midState.nextFresh)
    (forest : isUnionFindForest midState.links)
    (discipline : RelativeWireZoneDiscipline midState.openWires midState.nextFresh)
    (baseBelow : baseCount ≤ midState.nextFresh)
    (extractsEqual :
      extractDiagram 0 (processSpine (canonicalMatchingSeed 0) atomsAlpha)
        = extractDiagram 0 (processSpine (canonicalMatchingSeed 0) atomsBeta)) :
    extractDiagram baseCount (processSpine midState atomsAlpha)
      = extractDiagram baseCount (processSpine midState atomsBeta) := by
  have linksAlpha : (processSpine (canonicalMatchingSeed 0) atomsAlpha).links
      = applyJoinEvents (spineJoinEvents atomsAlpha (canonicalMatchingSeed 0)) [] :=
    processSpine_links_eq_applyJoinEvents atomsAlpha (canonicalMatchingSeed 0)
  have linksBeta : (processSpine (canonicalMatchingSeed 0) atomsBeta).links
      = applyJoinEvents (spineJoinEvents atomsBeta (canonicalMatchingSeed 0)) [] :=
    processSpine_links_eq_applyJoinEvents atomsBeta (canonicalMatchingSeed 0)
  have viewSim : MatchingConnectivityViewSim 0
      (processSpine (canonicalMatchingSeed 0) atomsAlpha)
      (processSpine (canonicalMatchingSeed 0) atomsBeta) :=
    matchingConnectivityViewSim_ofExtractEq 0
      (processSpine (canonicalMatchingSeed 0) atomsAlpha)
      (processSpine (canonicalMatchingSeed 0) atomsBeta) extractsEqual
  have baseBounded : ∀ leftNode rightNode : Nat, (leftNode, rightNode) ∈ midState.links →
      leftNode < midState.nextFresh ∧ rightNode < midState.nextFresh :=
    fun leftNode rightNode membership => fresh.2 (leftNode, rightNode) membership
  -- the proxy detour: degenerate traces' loop counts through the counter-shift proxy
  have shiftAlpha : extractDiagram 0
      (processSpine { openWires := [], links := [], nextFresh := 0, loops := 0 } atomsAlpha)
    = extractDiagram 0
        (processSpine { openWires := [], links := [], nextFresh := 1, loops := 0 }
          atomsAlpha) :=
    extractAfterProcessing_emptyBoundary_counterShift atomsAlpha chainedAlpha arityAlpha
  have shiftBeta : extractDiagram 0
      (processSpine { openWires := [], links := [], nextFresh := 0, loops := 0 } atomsBeta)
    = extractDiagram 0
        (processSpine { openWires := [], links := [], nextFresh := 1, loops := 0 }
          atomsBeta) :=
    extractAfterProcessing_emptyBoundary_counterShift atomsBeta chainedBeta arityBeta
  have proxyExtractsEqual : extractDiagram 0
      (processSpine { openWires := [], links := [], nextFresh := 1, loops := 0 } atomsAlpha)
    = extractDiagram 0
        (processSpine { openWires := [], links := [], nextFresh := 1, loops := 0 }
          atomsBeta) :=
    (shiftAlpha.symm.trans extractsEqual).trans shiftBeta
  have proxyViewSim : MatchingConnectivityViewSim 0
      (processSpine { openWires := [], links := [], nextFresh := 1, loops := 0 } atomsAlpha)
      (processSpine { openWires := [], links := [], nextFresh := 1, loops := 0 }
        atomsBeta) :=
    matchingConnectivityViewSim_ofExtractEq 0
      (processSpine { openWires := [], links := [], nextFresh := 1, loops := 0 } atomsAlpha)
      (processSpine { openWires := [], links := [], nextFresh := 1, loops := 0 } atomsBeta)
      proxyExtractsEqual
  have proxyFresh : WireStateFresh
      { openWires := [], links := [], nextFresh := 1, loops := 0 } :=
    ⟨fun _ absurdMem => (by cases absurdMem), fun _ absurdMem => (by cases absurdMem)⟩
  have proxyDistinct : WireListDistinct ([] : List Nat) :=
    fun _ _ _ twoInRange => nomatch twoInRange
  have proxyDiscipline : RelativeWireZoneDiscipline ([] : List Nat) 1 :=
    relativeWireZoneDiscipline_ofState
      { openWires := [], links := [], nextFresh := 1, loops := 0 } proxyFresh proxyDistinct
  have proxyLoopsAlpha : (processSpine
      { openWires := [], links := [], nextFresh := 1, loops := 0 } atomsAlpha).loops
      = countJoinEventLoops (spineJoinEvents atomsAlpha (canonicalMatchingSeed 0)) [] := by
    rw [processSpine_loops_ofMidState
      { openWires := [], links := [], nextFresh := 1, loops := 0 } 0 atomsAlpha
      chainedAlpha arityAlpha rfl proxyFresh (Nat.lt_succ_self 0)]
    show 0 + countJoinEventLoops
        ((spineJoinEvents atomsAlpha (canonicalMatchingSeed 0)).map
          (fun event => (relativeWireMap [] 1 event.1, relativeWireMap [] 1 event.2))) []
      = countJoinEventLoops (spineJoinEvents atomsAlpha (canonicalMatchingSeed 0)) []
    rw [Nat.zero_add, countJoinEventLoops_ofRename (relativeWireMap [] 1)
      proxyDiscipline.isInjective (spineJoinEvents atomsAlpha (canonicalMatchingSeed 0))]
  have proxyLoopsBeta : (processSpine
      { openWires := [], links := [], nextFresh := 1, loops := 0 } atomsBeta).loops
      = countJoinEventLoops (spineJoinEvents atomsBeta (canonicalMatchingSeed 0)) [] := by
    rw [processSpine_loops_ofMidState
      { openWires := [], links := [], nextFresh := 1, loops := 0 } 0 atomsBeta
      chainedBeta arityBeta rfl proxyFresh (Nat.lt_succ_self 0)]
    show 0 + countJoinEventLoops
        ((spineJoinEvents atomsBeta (canonicalMatchingSeed 0)).map
          (fun event => (relativeWireMap [] 1 event.1, relativeWireMap [] 1 event.2))) []
      = countJoinEventLoops (spineJoinEvents atomsBeta (canonicalMatchingSeed 0)) []
    rw [Nat.zero_add, countJoinEventLoops_ofRename (relativeWireMap [] 1)
      proxyDiscipline.isInjective (spineJoinEvents atomsBeta (canonicalMatchingSeed 0))]
  have canonicalCountsEqual :
      countJoinEventLoops (spineJoinEvents atomsAlpha (canonicalMatchingSeed 0)) []
      = countJoinEventLoops (spineJoinEvents atomsBeta (canonicalMatchingSeed 0)) [] :=
    (proxyLoopsAlpha.symm.trans proxyViewSim.loopsEq).trans proxyLoopsBeta
  -- the fresh-zone collapse: mid links count as the empty base
  have parentNoneAtOrAbove : ∀ probe : Nat, midState.nextFresh ≤ probe →
      unionFindParent midState.links probe = none :=
    fun probe atOrAbove =>
      unionFindParent_none_ofBound midState.nextFresh midState.links fresh.2 probe atOrAbove
  have belowViewsAgree : ∀ probeOne probeTwo : Nat,
      midState.nextFresh ≤ probeOne → midState.nextFresh ≤ probeTwo →
      isSameComponent midState.links probeOne probeTwo
        = isSameComponent [] probeOne probeTwo := by
    intro probeOne probeTwo oneAtOrAbove twoAtOrAbove
    show (unionFindRootOf midState.links probeOne
        == unionFindRootOf midState.links probeTwo)
      = (probeOne == probeTwo)
    rw [unionFindRootOf_ofParentless midState.links probeOne
        (parentNoneAtOrAbove probeOne oneAtOrAbove),
      unionFindRootOf_ofParentless midState.links probeTwo
        (parentNoneAtOrAbove probeTwo twoAtOrAbove)]
  have renamedClosedAlpha : ∀ pair ∈ (spineJoinEvents atomsAlpha
      (canonicalMatchingSeed 0)).map
        (fun event => (relativeWireMap midState.openWires midState.nextFresh event.1,
          relativeWireMap midState.openWires midState.nextFresh event.2)),
      midState.nextFresh ≤ pair.1 ∧ midState.nextFresh ≤ pair.2 := by
    intro pair membership
    have ⟨sourceEvent, _, pairEq⟩ := pairPreimage_ofMapMember
      (relativeWireMap midState.openWires midState.nextFresh)
      (spineJoinEvents atomsAlpha (canonicalMatchingSeed 0)) pair membership
    rw [pairEq]
    exact ⟨discipline.freshImageAtOrAbove sourceEvent.1
        (Nat.le_trans (Nat.le_of_eq midTracks) (Nat.zero_le sourceEvent.1)),
      discipline.freshImageAtOrAbove sourceEvent.2
        (Nat.le_trans (Nat.le_of_eq midTracks) (Nat.zero_le sourceEvent.2))⟩
  have renamedClosedBeta : ∀ pair ∈ (spineJoinEvents atomsBeta
      (canonicalMatchingSeed 0)).map
        (fun event => (relativeWireMap midState.openWires midState.nextFresh event.1,
          relativeWireMap midState.openWires midState.nextFresh event.2)),
      midState.nextFresh ≤ pair.1 ∧ midState.nextFresh ≤ pair.2 := by
    intro pair membership
    have ⟨sourceEvent, _, pairEq⟩ := pairPreimage_ofMapMember
      (relativeWireMap midState.openWires midState.nextFresh)
      (spineJoinEvents atomsBeta (canonicalMatchingSeed 0)) pair membership
    rw [pairEq]
    exact ⟨discipline.freshImageAtOrAbove sourceEvent.1
        (Nat.le_trans (Nat.le_of_eq midTracks) (Nat.zero_le sourceEvent.1)),
      discipline.freshImageAtOrAbove sourceEvent.2
        (Nat.le_trans (Nat.le_of_eq midTracks) (Nat.zero_le sourceEvent.2))⟩
  have restrictedAlpha : countJoinEventLoops
      ((spineJoinEvents atomsAlpha (canonicalMatchingSeed 0)).map
        (fun event => (relativeWireMap midState.openWires midState.nextFresh event.1,
          relativeWireMap midState.openWires midState.nextFresh event.2)))
      midState.links
      = countJoinEventLoops
          ((spineJoinEvents atomsAlpha (canonicalMatchingSeed 0)).map
            (fun event => (relativeWireMap midState.openWires midState.nextFresh event.1,
              relativeWireMap midState.openWires midState.nextFresh event.2))) [] :=
    countJoinEventLoops_congrOnNodeSet (fun node => midState.nextFresh ≤ node)
      ((spineJoinEvents atomsAlpha (canonicalMatchingSeed 0)).map
        (fun event => (relativeWireMap midState.openWires midState.nextFresh event.1,
          relativeWireMap midState.openWires midState.nextFresh event.2)))
      midState.links [] forest True.intro renamedClosedAlpha belowViewsAgree
  have restrictedBeta : countJoinEventLoops
      ((spineJoinEvents atomsBeta (canonicalMatchingSeed 0)).map
        (fun event => (relativeWireMap midState.openWires midState.nextFresh event.1,
          relativeWireMap midState.openWires midState.nextFresh event.2)))
      midState.links
      = countJoinEventLoops
          ((spineJoinEvents atomsBeta (canonicalMatchingSeed 0)).map
            (fun event => (relativeWireMap midState.openWires midState.nextFresh event.1,
              relativeWireMap midState.openWires midState.nextFresh event.2))) [] :=
    countJoinEventLoops_congrOnNodeSet (fun node => midState.nextFresh ≤ node)
      ((spineJoinEvents atomsBeta (canonicalMatchingSeed 0)).map
        (fun event => (relativeWireMap midState.openWires midState.nextFresh event.1,
          relativeWireMap midState.openWires midState.nextFresh event.2)))
      midState.links [] forest True.intro renamedClosedBeta belowViewsAgree
  have renameAlpha : countJoinEventLoops
      ((spineJoinEvents atomsAlpha (canonicalMatchingSeed 0)).map
        (fun event => (relativeWireMap midState.openWires midState.nextFresh event.1,
          relativeWireMap midState.openWires midState.nextFresh event.2))) []
      = countJoinEventLoops (spineJoinEvents atomsAlpha (canonicalMatchingSeed 0)) [] :=
    countJoinEventLoops_ofRename
      (relativeWireMap midState.openWires midState.nextFresh)
      discipline.isInjective (spineJoinEvents atomsAlpha (canonicalMatchingSeed 0))
  have renameBeta : countJoinEventLoops
      ((spineJoinEvents atomsBeta (canonicalMatchingSeed 0)).map
        (fun event => (relativeWireMap midState.openWires midState.nextFresh event.1,
          relativeWireMap midState.openWires midState.nextFresh event.2))) []
      = countJoinEventLoops (spineJoinEvents atomsBeta (canonicalMatchingSeed 0)) [] :=
    countJoinEventLoops_ofRename
      (relativeWireMap midState.openWires midState.nextFresh)
      discipline.isInjective (spineJoinEvents atomsBeta (canonicalMatchingSeed 0))
  have compositeLengthAlpha : (processSpine midState atomsAlpha).openWires.length
      = (processSpine (canonicalMatchingSeed 0) atomsAlpha).openWires.length := by
    rw [processSpine_openWires_ofMidState midState 0 atomsAlpha arityAlpha midTracks]
    exact mapLength (relativeWireMap midState.openWires midState.nextFresh) _
  have compositeLengthBeta : (processSpine midState atomsBeta).openWires.length
      = (processSpine (canonicalMatchingSeed 0) atomsBeta).openWires.length := by
    rw [processSpine_openWires_ofMidState midState 0 atomsBeta arityBeta midTracks]
    exact mapLength (relativeWireMap midState.openWires midState.nextFresh) _
  apply extractDiagram_eq_of_connectivityView
  · rw [compositeLengthAlpha, compositeLengthBeta]
    exact viewSim.lengthEq
  · rw [processSpine_loops_ofMidState midState 0 atomsAlpha chainedAlpha arityAlpha
        midTracks fresh nfPos,
      processSpine_loops_ofMidState midState 0 atomsBeta chainedBeta arityBeta
        midTracks fresh nfPos,
      restrictedAlpha, renameAlpha, canonicalCountsEqual, ← renameBeta, ← restrictedBeta]
  · intro firstIndex secondIndex firstBound secondBound
    have firstBoundCanonical : firstIndex < baseCount
        + (processSpine (canonicalMatchingSeed 0) atomsAlpha).openWires.length := by
      rw [← compositeLengthAlpha]
      exact firstBound
    have secondBoundCanonical : secondIndex < baseCount
        + (processSpine (canonicalMatchingSeed 0) atomsAlpha).openWires.length := by
      rw [← compositeLengthAlpha]
      exact secondBound
    show isSameComponent (processSpine midState atomsAlpha).links
        (natListGetAt (List.range baseCount ++ (processSpine midState atomsAlpha).openWires)
          firstIndex)
        (natListGetAt (List.range baseCount ++ (processSpine midState atomsAlpha).openWires)
          secondIndex)
      = isSameComponent (processSpine midState atomsBeta).links
        (natListGetAt (List.range baseCount ++ (processSpine midState atomsBeta).openWires)
          firstIndex)
        (natListGetAt (List.range baseCount ++ (processSpine midState atomsBeta).openWires)
          secondIndex)
    rw [processSpine_links_ofMidState midState 0 atomsAlpha chainedAlpha arityAlpha
        midTracks,
      processSpine_openWires_ofMidState midState 0 atomsAlpha arityAlpha midTracks,
      processSpine_links_ofMidState midState 0 atomsBeta chainedBeta arityBeta midTracks,
      processSpine_openWires_ofMidState midState 0 atomsBeta arityBeta midTracks]
    exact compositeBoundaryView_agrees_ofExtractEq midState.openWires midState.nextFresh
      discipline 0 midTracks baseCount baseBelow
      (processSpine (canonicalMatchingSeed 0) atomsAlpha)
      (processSpine (canonicalMatchingSeed 0) atomsBeta)
      (spineJoinEvents atomsAlpha (canonicalMatchingSeed 0))
      (spineJoinEvents atomsBeta (canonicalMatchingSeed 0))
      midState.links linksAlpha linksBeta extractsEqual forest baseBounded
      firstIndex secondIndex firstBoundCanonical secondBoundCanonical

/-! ## The seed-generic core, empty-mid leg -/

/-- **The seed-generic vcomp-RIGHT extract congruence, EMPTY mid boundary.**  The same
mid-state plumbing as the positive-mid core (conditions package + distinctness + zone
discipline + the window-suffix width read-off), landing in the empty-boundary relative
extract agreement. -/
theorem extractAfterProcessing_vcompRight_ofSeed_emptyMid {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {oneCellF oneCellG oneCellH : ModalityPath signature.graph sourceMode targetMode}
    (cellAlpha : RawTwoCellExpr signature oneCellF oneCellG)
    {cellBetaFirst cellBetaSecond : RawTwoCellExpr signature oneCellG oneCellH}
    (bottomCount : Nat) (seed : WireState)
    (seedConditions : MatchingSwapStateConditions bottomCount seed)
    (seedTracks : seed.openWires.length = oneCellF.length)
    (seedDistinct : WireListDistinct seed.openWires)
    (alphaCupCap : CellHasCupCapGenerators cellAlpha)
    (betaFirstCupCap : CellHasCupCapGenerators cellBetaFirst)
    (betaSecondCupCap : CellHasCupCapGenerators cellBetaSecond)
    (midBoundaryZero : oneCellG.length = 0)
    (extractsEqual : extractDiagram oneCellG.length
        (processSpine (canonicalMatchingSeed oneCellG.length) cellBetaFirst.spine)
      = extractDiagram oneCellG.length
          (processSpine (canonicalMatchingSeed oneCellG.length) cellBetaSecond.spine)) :
    extractDiagram bottomCount
        (processSpine seed (RawTwoCellExpr.vcomp cellAlpha cellBetaFirst).spine)
      = extractDiagram bottomCount
          (processSpine seed (RawTwoCellExpr.vcomp cellAlpha cellBetaSecond).spine) := by
  rw [RawTwoCellExpr.spine_vcomp cellAlpha cellBetaFirst,
    RawTwoCellExpr.spine_vcomp cellAlpha cellBetaSecond,
    processSpine_append cellAlpha.spine cellBetaFirst.spine seed,
    processSpine_append cellAlpha.spine cellBetaSecond.spine seed]
  have midConditions : MatchingSwapStateConditions bottomCount
      (processSpine seed cellAlpha.spine) :=
    matchingSwapStateConditions_processSpine bottomCount cellAlpha.spine seed seedConditions
  have midDistinct : WireListDistinct (processSpine seed cellAlpha.spine).openWires :=
    processSpine_wireListDistinct cellAlpha.spine seed seedConditions.fresh
      seedConditions.nfPos seedDistinct
  have midDiscipline : RelativeWireZoneDiscipline
      (processSpine seed cellAlpha.spine).openWires
      (processSpine seed cellAlpha.spine).nextFresh :=
    relativeWireZoneDiscipline_ofState (processSpine seed cellAlpha.spine)
      midConditions.fresh midDistinct
  have windowInRange : (identityPath sourceMode).length + oneCellF.length
      ≤ seed.openWires.length := by
    show 0 + oneCellF.length ≤ seed.openWires.length
    rw [Nat.zero_add]
    exact Nat.le_of_eq seedTracks.symm
  have suffixInvariant := (runMatchingCell_openWiresSuffix_invariant
    (identityPath sourceMode) (identityPath targetMode) cellAlpha seed
    alphaCupCap windowInRange).2
  have midTracks : (processSpine seed cellAlpha.spine).openWires.length
      = oneCellG.length := by
    have lengthBalance : (processSpine seed cellAlpha.spine).openWires.length
        + oneCellF.length = seed.openWires.length + oneCellG.length := suffixInvariant
    rw [seedTracks, Nat.add_comm oneCellF.length oneCellG.length] at lengthBalance
    exact natAddRightCancel oneCellF.length lengthBalance
  exact processSpine_extract_eq_ofCanonicalExtractEq_emptyBoundary bottomCount
    (processSpine seed cellAlpha.spine) cellBetaFirst.spine cellBetaSecond.spine
    (midBoundaryZero ▸ cellBetaFirst.spineBoundaryChained_spine)
    (cellBetaFirst.spineHasCupCapAtoms_spine betaFirstCupCap)
    (midBoundaryZero ▸ cellBetaSecond.spineBoundaryChained_spine)
    (cellBetaSecond.spineHasCupCapAtoms_spine betaSecondCupCap)
    (midTracks.trans midBoundaryZero) midConditions.fresh midConditions.nfPos
    midConditions.forest midDiscipline midConditions.bottomLe
    (midBoundaryZero ▸ extractsEqual)

/-! ## The unconditional headline -/

/-- ★ **The vcomp-RIGHT matching congruence at the walking adjunction — UNCONDITIONAL.**
Mid-boundary dispatch: an inhabited mid boundary routes to the shipped positive-mid
inhabitant; an empty mid boundary routes through this file's leg, with the source boundary
dispatched between the canonical seed and the counter-shift proxy exactly as before. -/
theorem matchingOf_vcompRight_congruence {sourceMode targetMode : AdjunctionMode}
    {oneCellF oneCellG oneCellH : ModalityPath adjunctionGraph sourceMode targetMode}
    (cellAlpha : RawTwoCellExpr adjunctionModeSignature oneCellF oneCellG)
    {cellBetaFirst cellBetaSecond : RawTwoCellExpr adjunctionModeSignature oneCellG oneCellH}
    (matchingsEqual : matchingOf cellBetaFirst = matchingOf cellBetaSecond) :
    matchingOf (RawTwoCellExpr.vcomp cellAlpha cellBetaFirst)
      = matchingOf (RawTwoCellExpr.vcomp cellAlpha cellBetaSecond) := by
  cases Nat.lt_or_ge 0 oneCellG.length with
  | inl midInhabited =>
      exact matchingOf_vcompRight_congruence_ofMidBoundaryPos cellAlpha midInhabited
        matchingsEqual
  | inr midAtMostZero =>
      have midBoundaryZero : oneCellG.length = 0 :=
        Nat.le_antisymm midAtMostZero (Nat.zero_le oneCellG.length)
      show extractDiagram oneCellF.length
          (processSpine (canonicalMatchingSeed oneCellF.length)
            (RawTwoCellExpr.vcomp cellAlpha cellBetaFirst).spine)
        = extractDiagram oneCellF.length
            (processSpine (canonicalMatchingSeed oneCellF.length)
              (RawTwoCellExpr.vcomp cellAlpha cellBetaSecond).spine)
      have extractsEqual : extractDiagram oneCellG.length
          (processSpine (canonicalMatchingSeed oneCellG.length) cellBetaFirst.spine)
        = extractDiagram oneCellG.length
            (processSpine (canonicalMatchingSeed oneCellG.length) cellBetaSecond.spine) :=
        matchingsEqual
      cases Nat.lt_or_ge 0 oneCellF.length with
      | inl sourceInhabited =>
          exact extractAfterProcessing_vcompRight_ofSeed_emptyMid cellAlpha
            oneCellF.length (canonicalMatchingSeed oneCellF.length)
            (matchingSwapStateConditions_initial oneCellF.length sourceInhabited)
            (rangeLength oneCellF.length)
            (canonicalMatchingSeed_wireListDistinct oneCellF.length)
            (cellHasCupCapGenerators_ofAdjunctionSignature cellAlpha)
            (cellHasCupCapGenerators_ofAdjunctionSignature cellBetaFirst)
            (cellHasCupCapGenerators_ofAdjunctionSignature cellBetaSecond)
            midBoundaryZero extractsEqual
      | inr sourceAtMostZero =>
          have zeroLength : oneCellF.length = 0 :=
            Nat.le_antisymm sourceAtMostZero (Nat.zero_le oneCellF.length)
          rw [zeroLength]
          have shiftCompositeFirst : extractDiagram 0
              (processSpine
                { openWires := List.range 0, links := [], nextFresh := 0, loops := 0 }
                (RawTwoCellExpr.vcomp cellAlpha cellBetaFirst).spine)
            = extractDiagram 0
                (processSpine { openWires := [], links := [], nextFresh := 1, loops := 0 }
                  (RawTwoCellExpr.vcomp cellAlpha cellBetaFirst).spine) :=
            extractAfterProcessing_emptyBoundary_counterShift
              (RawTwoCellExpr.vcomp cellAlpha cellBetaFirst).spine
              (zeroLength
                ▸ (RawTwoCellExpr.vcomp cellAlpha cellBetaFirst).spineBoundaryChained_spine)
              ((RawTwoCellExpr.vcomp cellAlpha cellBetaFirst).spineHasCupCapAtoms_spine
                (cellHasCupCapGenerators_ofAdjunctionSignature
                  (RawTwoCellExpr.vcomp cellAlpha cellBetaFirst)))
          have shiftCompositeSecond : extractDiagram 0
              (processSpine
                { openWires := List.range 0, links := [], nextFresh := 0, loops := 0 }
                (RawTwoCellExpr.vcomp cellAlpha cellBetaSecond).spine)
            = extractDiagram 0
                (processSpine { openWires := [], links := [], nextFresh := 1, loops := 0 }
                  (RawTwoCellExpr.vcomp cellAlpha cellBetaSecond).spine) :=
            extractAfterProcessing_emptyBoundary_counterShift
              (RawTwoCellExpr.vcomp cellAlpha cellBetaSecond).spine
              (zeroLength
                ▸ (RawTwoCellExpr.vcomp cellAlpha cellBetaSecond).spineBoundaryChained_spine)
              ((RawTwoCellExpr.vcomp cellAlpha cellBetaSecond).spineHasCupCapAtoms_spine
                (cellHasCupCapGenerators_ofAdjunctionSignature
                  (RawTwoCellExpr.vcomp cellAlpha cellBetaSecond)))
          have proxyConditions : MatchingSwapStateConditions 0
              { openWires := [], links := [], nextFresh := 1, loops := 0 } :=
            { bottomLe := Nat.zero_le 1
              forest := by exact True.intro
              nfPos := Nat.lt_succ_self 0
              fresh := ⟨fun _ absurdMem => (by cases absurdMem),
                fun _ absurdMem => (by cases absurdMem)⟩ }
          have proxyDistinct : WireListDistinct ([] : List Nat) :=
            fun _ _ _ twoInRange => nomatch twoInRange
          have proxyComposite := extractAfterProcessing_vcompRight_ofSeed_emptyMid cellAlpha
            0 { openWires := [], links := [], nextFresh := 1, loops := 0 }
            proxyConditions zeroLength.symm proxyDistinct
            (cellHasCupCapGenerators_ofAdjunctionSignature cellAlpha)
            (cellHasCupCapGenerators_ofAdjunctionSignature cellBetaFirst)
            (cellHasCupCapGenerators_ofAdjunctionSignature cellBetaSecond)
            midBoundaryZero extractsEqual
          exact (shiftCompositeFirst.trans proxyComposite).trans shiftCompositeSecond.symm

/-! ## Honesty marker -/

/-- **Honesty marker — the vcomp-RIGHT matching congruence is SHIPPED UNCONDITIONALLY.**
Both mid-boundary legs (the positive-mid gluing and the empty-mid proxy-detour /
fresh-zone collapse) and both source-boundary legs inside each.  NOT yet shipped: the
`MatchingSaturatedCongruence` bundle collecting the four compositionality fields — the next
brick.  `= true`. -/
def fxMode_hasMatchingVcompRightCongruence : Bool := true

end FX1Poly.Polygraph
