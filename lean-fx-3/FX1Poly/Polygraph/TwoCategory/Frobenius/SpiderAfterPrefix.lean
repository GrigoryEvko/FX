import FX1Poly.Polygraph.TwoCategory.Frobenius.SpiderConv
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescFunctoriality
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingCompositeView

/-! # WP-FROB r4 (FROB-4) — the spider PREFIX BRIDGE, loops-free re-homing of the two-word functoriality

`SpiderConv` (`Frobenius/SpiderConv.lean`) already carries the prefix-generic congruence as its `whisker`
constructor: two words fired after ANY prefix are convertible once, at the two post-prefix states, they preserve the
boundary PARTITION view (equal open-wire count + agreeing `matchingSameComponent` on the in-range indices).  The
`whisker` move gates on those two SEMANTIC obligations directly.  This file SUPPLIES them functorially — from the
CANONICAL (post-prefix width) seed facts alone — so a relation whiskered after an arbitrary prefix becomes a
`SpiderConv` theorem without re-deciding the concrete post-prefix states.

## Why a LOOPS-FREE re-homing (the special row forces it)

The Brauer lane already ships `brauerConv_whisker_ofCanonicalExtractEq` (`Brauer/WiringDescFunctoriality.lean`),
which discharges the Brauer `whisker` from a canonical `extractDiagram` equality.  That route is LOOPS-BEARING: it
reconstructs a full `MatchingConnectivityViewSim` (which BUNDLES `loopsEq`) from the extract equality.  The spider's
special row `μδ = 1` carries UNEQUAL loop counts on its canonical runs (the μ-after-δ bubble reads `loops = 1`
against the identity strand's `loops = 0`, `specialBubble_uncounted`), so no `MatchingConnectivityViewSim` between
its two sides exists — the loops-bearing route is structurally blocked, exactly as the loops-based pad payoff was
(`fxFrob_hasSpiderPadCongruence` had to be loops-free).

So this file re-homes the two-word functoriality to the boundary PARTITION VIEW only.  The engine-agnostic view leg
(`compositeBoundaryView_agrees_ofExtractEq`, `MatchingCompositeView.lean`) consumes the extract equality ONLY to
build the two view sims; every downstream brick (`compositeConnectivity_transfersAcrossInterface`,
`canonicalTransfers_ofViewSim`) reads only `.lengthEq` / `.viewAgrees`, never `.loopsEq`.  We clone that stack with
the extract equality replaced by (canonical open-wire length agreement + canonical `matchingSameComponent`
agreement) — loops never enter — and land `processBrauer_forgetView_eq_ofCanonicalViewParts`: the two whisker legs
(length + boundary view) at ANY shared disciplined mid-state, computed from the canonical (post-prefix width) view
parts.  `spiderConv_relation_afterPrefix` feeds those two legs straight into `SpiderConv.whisker`.

## What DROPS versus the Brauer headline

`processBrauer_extract_eq_ofCanonicalExtractEq` assembles THREE legs through `extractDiagram_eq_of_connectivityView`:
length, loop, and boundary view.  This port DROPS the loop leg (so no `brauerWordInternalLoops = 0` premise is
needed) and outputs the length + view pair rather than a reassembled `DiagramType` equality — precisely the shape
`SpiderConv.whisker` consumes.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `native_decide` / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private plumbing -/

/-- Bool equality from mutual implication (local copy — the shipped one is file-private). -/
private theorem boolEqOfImpliesBothLocal : (leftBool rightBool : Bool) →
    (leftBool = true → rightBool = true) → (rightBool = true → leftBool = true) →
    leftBool = rightBool
  | true, _, forward, _ => (forward rfl).symm
  | false, true, _, backward => backward rfl
  | false, false, _, _ => rfl

/-! ## The loops-free transfer clones (extract equality replaced by length + view parts)

The three bricks `compositeBoundaryView_agrees_ofExtractEq` factors through, re-stated so the CANONICAL boundary
agreement is supplied as (open-wire length equality + `matchingSameComponent` view agreement) directly instead of
being reconstructed from a full extract equality.  None of the three reads `loops`, so the special row's unequal
loop counts never obstruct. -/

/-- ★ **The view-simulation canonical transfer, from view PARTS.**  The port of `canonicalTransfers_ofViewSim` with
the `MatchingConnectivityViewSim` argument split into its two loops-free fields (`lengthEq` / `viewAgrees`).  Same
proof: the boundary reads pin the positions, the view agreement rewrites the same-component read, the links read-offs
close it. -/
theorem canonicalTransfers_ofViewParts (bottomCount : Nat) (stateA stateB : WireState)
    (eventsA eventsB : List (Nat × Nat))
    (linksA : stateA.links = applyJoinEvents eventsA [])
    (linksB : stateB.links = applyJoinEvents eventsB [])
    (lengthEq : stateA.openWires.length = stateB.openWires.length)
    (viewAgrees : ∀ firstIndex secondIndex,
        firstIndex < bottomCount + stateB.openWires.length →
        secondIndex < bottomCount + stateB.openWires.length →
        matchingSameComponent bottomCount stateA firstIndex secondIndex
          = matchingSameComponent bottomCount stateB firstIndex secondIndex)
    (pivotCanonicalA pivotCanonicalB probeCanonicalA probeCanonicalB : Nat)
    (pivotPair : CanonicalBoundaryPair bottomCount stateA stateB pivotCanonicalA pivotCanonicalB)
    (probePair : CanonicalBoundaryPair bottomCount stateA stateB probeCanonicalA probeCanonicalB)
    (connectedA : isSameComponent (applyJoinEvents eventsA [])
      pivotCanonicalA probeCanonicalA = true) :
    isSameComponent (applyJoinEvents eventsB [])
      pivotCanonicalB probeCanonicalB = true := by
  obtain ⟨pivotPosition, pivotBound, pivotReadA, pivotReadB⟩ := pivotPair
  obtain ⟨probePosition, probeBound, probeReadA, probeReadB⟩ := probePair
  have pivotBoundB : pivotPosition < bottomCount + stateB.openWires.length := by
    rw [← lengthEq]; exact pivotBound
  have probeBoundB : probePosition < bottomCount + stateB.openWires.length := by
    rw [← lengthEq]; exact probeBound
  have viewShaped : isSameComponent stateA.links
        (natListGetAt (matchingBoundaryNodes bottomCount stateA) pivotPosition)
        (natListGetAt (matchingBoundaryNodes bottomCount stateA) probePosition)
      = isSameComponent stateB.links
        (natListGetAt (matchingBoundaryNodes bottomCount stateB) pivotPosition)
        (natListGetAt (matchingBoundaryNodes bottomCount stateB) probePosition) :=
    viewAgrees pivotPosition probePosition pivotBoundB probeBoundB
  rw [pivotReadA, probeReadA, pivotReadB, probeReadB, linksA, linksB] at viewShaped
  rw [← viewShaped]
  exact connectedA

/-- ★ **The fully discharged composite transfer, from view PARTS.**  The port of
`compositeConnectivity_transfersAcrossInterface` feeding `canonicalTransfers_ofViewParts` instead of the sim. -/
theorem compositeConnectivity_transfersAcrossInterface_ofViewParts (wires : List Nat) (freshBase : Nat)
    (discipline : RelativeWireZoneDiscipline wires freshBase)
    (bottomCount : Nat) (midTracks : wires.length = bottomCount)
    (stateA stateB : WireState) (eventsA eventsB midLinks : List (Nat × Nat))
    (linksA : stateA.links = applyJoinEvents eventsA [])
    (linksB : stateB.links = applyJoinEvents eventsB [])
    (lengthEq : stateA.openWires.length = stateB.openWires.length)
    (viewAgrees : ∀ firstIndex secondIndex,
        firstIndex < bottomCount + stateB.openWires.length →
        secondIndex < bottomCount + stateB.openWires.length →
        matchingSameComponent bottomCount stateA firstIndex secondIndex
          = matchingSameComponent bottomCount stateB firstIndex secondIndex)
    (forest : isUnionFindForest midLinks)
    (baseBounded : ∀ leftNode rightNode : Nat, (leftNode, rightNode) ∈ midLinks →
      leftNode < freshBase ∧ rightNode < freshBase)
    (startNode lastNode startImage lastImage : Nat)
    (startCorresponds : InterfaceCorresponds (relativeWireMap wires freshBase) freshBase
      (CanonicalBoundaryPair bottomCount stateA stateB) startNode startImage)
    (lastCorresponds : InterfaceCorresponds (relativeWireMap wires freshBase) freshBase
      (CanonicalBoundaryPair bottomCount stateA stateB) lastNode lastImage)
    (foldConnected : isSameComponent
      (applyJoinEvents (eventsA.map (fun event =>
        (relativeWireMap wires freshBase event.1, relativeWireMap wires freshBase event.2)))
        midLinks)
      startNode lastNode = true) :
    isSameComponent
      (applyJoinEvents (eventsB.map (fun event =>
        (relativeWireMap wires freshBase event.1, relativeWireMap wires freshBase event.2)))
        midLinks)
      startImage lastImage = true :=
  isSameComponent_applyJoinEvents_transferAcrossInterface_ofCanonicalPairs
    (relativeWireMap wires freshBase) discipline.isInjective freshBase
    (CanonicalBoundaryPair bottomCount stateA stateB) eventsA eventsB midLinks
    forest baseBounded
    (canonicalBoundaryPair_selfOfPortImage wires freshBase discipline bottomCount midTracks
      stateA stateB)
    (canonicalTransfers_ofViewParts bottomCount stateA stateB eventsA eventsB linksA linksB
      lengthEq viewAgrees)
    startNode lastNode startImage lastImage startCorresponds lastCorresponds foldConnected

/-- ★ **The composite boundary view agreement, from view PARTS.**  The port of
`compositeBoundaryView_agrees_ofExtractEq` with the extract equality replaced by the canonical open-wire length
agreement + the canonical `matchingSameComponent` view agreement.  Both directions of the composite transfer run at
the corresponding boundary reads, with the backward direction using the symmetric view parts. -/
theorem compositeBoundaryView_agrees_ofViewParts (wires : List Nat) (freshBase : Nat)
    (discipline : RelativeWireZoneDiscipline wires freshBase)
    (midCount : Nat) (midTracks : wires.length = midCount)
    (baseCount : Nat) (baseBelow : baseCount ≤ freshBase)
    (stateA stateB : WireState) (eventsA eventsB midLinks : List (Nat × Nat))
    (linksA : stateA.links = applyJoinEvents eventsA [])
    (linksB : stateB.links = applyJoinEvents eventsB [])
    (canonLengthEq : stateA.openWires.length = stateB.openWires.length)
    (canonViewAgrees : ∀ firstIndex secondIndex,
        firstIndex < midCount + stateA.openWires.length →
        secondIndex < midCount + stateA.openWires.length →
        matchingSameComponent midCount stateA firstIndex secondIndex
          = matchingSameComponent midCount stateB firstIndex secondIndex)
    (forest : isUnionFindForest midLinks)
    (baseBounded : ∀ leftNode rightNode : Nat, (leftNode, rightNode) ∈ midLinks →
      leftNode < freshBase ∧ rightNode < freshBase)
    (positionOne positionTwo : Nat)
    (oneInRange : positionOne < baseCount + stateA.openWires.length)
    (twoInRange : positionTwo < baseCount + stateA.openWires.length) :
    isSameComponent
        (applyJoinEvents (eventsA.map (fun event =>
          (relativeWireMap wires freshBase event.1, relativeWireMap wires freshBase event.2)))
          midLinks)
        (natListGetAt (List.range baseCount
          ++ stateA.openWires.map (relativeWireMap wires freshBase)) positionOne)
        (natListGetAt (List.range baseCount
          ++ stateA.openWires.map (relativeWireMap wires freshBase)) positionTwo)
      = isSameComponent
        (applyJoinEvents (eventsB.map (fun event =>
          (relativeWireMap wires freshBase event.1, relativeWireMap wires freshBase event.2)))
          midLinks)
        (natListGetAt (List.range baseCount
          ++ stateB.openWires.map (relativeWireMap wires freshBase)) positionOne)
        (natListGetAt (List.range baseCount
          ++ stateB.openWires.map (relativeWireMap wires freshBase)) positionTwo) := by
  have oneInRangeB : positionOne < baseCount + stateB.openWires.length := by
    rw [← canonLengthEq]; exact oneInRange
  have twoInRangeB : positionTwo < baseCount + stateB.openWires.length := by
    rw [← canonLengthEq]; exact twoInRange
  exact boolEqOfImpliesBothLocal _ _
    (fun foldConnectedA =>
      compositeConnectivity_transfersAcrossInterface_ofViewParts wires freshBase discipline
        midCount midTracks stateA stateB eventsA eventsB midLinks linksA linksB canonLengthEq
        (fun firstIndex secondIndex firstBoundB secondBoundB =>
          canonViewAgrees firstIndex secondIndex
            (by rw [canonLengthEq]; exact firstBoundB) (by rw [canonLengthEq]; exact secondBoundB))
        forest baseBounded _ _ _ _
        (interfaceCorresponds_ofCompositeBoundaryPosition wires freshBase midCount baseCount
          baseBelow stateA stateB canonLengthEq positionOne oneInRange)
        (interfaceCorresponds_ofCompositeBoundaryPosition wires freshBase midCount baseCount
          baseBelow stateA stateB canonLengthEq positionTwo twoInRange)
        foldConnectedA)
    (fun foldConnectedB =>
      compositeConnectivity_transfersAcrossInterface_ofViewParts wires freshBase discipline
        midCount midTracks stateB stateA eventsB eventsA midLinks linksB linksA canonLengthEq.symm
        (fun firstIndex secondIndex firstBoundA secondBoundA =>
          (canonViewAgrees firstIndex secondIndex firstBoundA secondBoundA).symm)
        forest baseBounded _ _ _ _
        (interfaceCorresponds_ofCompositeBoundaryPosition wires freshBase midCount baseCount
          baseBelow stateB stateA canonLengthEq.symm positionOne oneInRangeB)
        (interfaceCorresponds_ofCompositeBoundaryPosition wires freshBase midCount baseCount
          baseBelow stateB stateA canonLengthEq.symm positionTwo twoInRangeB)
        foldConnectedB)

/-! ## The loops-free two-word functoriality headline (length + view, at any shared mid-state) -/

/-- ★ **KEYSTONE16 — the two-word functoriality re-homed to the PARTITION VIEW.**  Two Brauer words whose CANONICAL
runs (from the seed of width `boundaryLength`) agree on open-wire length and boundary `matchingSameComponent` view
produce, at ANY shared disciplined mid-state, mid-state runs that agree on BOTH (open-wire length + boundary view at
`baseCount`).  The loops-free port of `processBrauer_extract_eq_ofCanonicalExtractEq`: legs 1 (length) and 3 (view)
are kept, leg 2 (loops) is DROPPED, so no `brauerWordInternalLoops = 0` premise is needed and the special row's
unequal loop counts never obstruct.  The mid-state provenance (freshness / forest / zone discipline / base bound) is
exactly the reachable-state invariants the Brauer engine propagates. -/
theorem processBrauer_forgetView_eq_ofCanonicalViewParts
    (baseCount boundaryLength : Nat) (midState : WireState)
    (atomsAlpha atomsBeta : List BrauerAtom)
    (inRangeAlpha : BrauerWordInRange boundaryLength atomsAlpha)
    (inRangeBeta : BrauerWordInRange boundaryLength atomsBeta)
    (midTracks : midState.openWires.length = boundaryLength)
    (fresh : WiringDescStateFresh midState)
    (forest : isUnionFindForest midState.links)
    (discipline : RelativeWireZoneDiscipline midState.openWires midState.nextFresh)
    (baseBelow : baseCount ≤ midState.nextFresh)
    (canonLengthEq :
      (processBrauer (canonicalMatchingSeed boundaryLength) atomsAlpha).openWires.length
        = (processBrauer (canonicalMatchingSeed boundaryLength) atomsBeta).openWires.length)
    (canonViewAgrees : ∀ firstIndex secondIndex,
        firstIndex < boundaryLength
            + (processBrauer (canonicalMatchingSeed boundaryLength) atomsAlpha).openWires.length →
        secondIndex < boundaryLength
            + (processBrauer (canonicalMatchingSeed boundaryLength) atomsAlpha).openWires.length →
        matchingSameComponent boundaryLength
            (processBrauer (canonicalMatchingSeed boundaryLength) atomsAlpha) firstIndex secondIndex
          = matchingSameComponent boundaryLength
            (processBrauer (canonicalMatchingSeed boundaryLength) atomsBeta) firstIndex secondIndex) :
    (processBrauer midState atomsAlpha).openWires.length
        = (processBrauer midState atomsBeta).openWires.length
      ∧ (∀ firstIndex secondIndex,
          firstIndex < baseCount + (processBrauer midState atomsAlpha).openWires.length →
          secondIndex < baseCount + (processBrauer midState atomsAlpha).openWires.length →
          matchingSameComponent baseCount (processBrauer midState atomsAlpha) firstIndex secondIndex
            = matchingSameComponent baseCount (processBrauer midState atomsBeta) firstIndex secondIndex) := by
  have linksAlpha : (processBrauer (canonicalMatchingSeed boundaryLength) atomsAlpha).links
      = applyJoinEvents (brauerWordJoinEvents (canonicalMatchingSeed boundaryLength) atomsAlpha) [] :=
    processBrauer_links_eq_applyJoinEvents atomsAlpha (canonicalMatchingSeed boundaryLength)
  have linksBeta : (processBrauer (canonicalMatchingSeed boundaryLength) atomsBeta).links
      = applyJoinEvents (brauerWordJoinEvents (canonicalMatchingSeed boundaryLength) atomsBeta) [] :=
    processBrauer_links_eq_applyJoinEvents atomsBeta (canonicalMatchingSeed boundaryLength)
  have baseBounded : ∀ leftNode rightNode : Nat, (leftNode, rightNode) ∈ midState.links →
      leftNode < midState.nextFresh ∧ rightNode < midState.nextFresh :=
    fun leftNode rightNode membership => fresh.2 (leftNode, rightNode) membership
  have compositeLengthAlpha : (processBrauer midState atomsAlpha).openWires.length
      = (processBrauer (canonicalMatchingSeed boundaryLength) atomsAlpha).openWires.length := by
    rw [processBrauer_openWires_ofMidState midState boundaryLength atomsAlpha midTracks]
    exact mapLength (relativeWireMap midState.openWires midState.nextFresh) _
  have compositeLengthBeta : (processBrauer midState atomsBeta).openWires.length
      = (processBrauer (canonicalMatchingSeed boundaryLength) atomsBeta).openWires.length := by
    rw [processBrauer_openWires_ofMidState midState boundaryLength atomsBeta midTracks]
    exact mapLength (relativeWireMap midState.openWires midState.nextFresh) _
  refine ⟨?_, ?_⟩
  · rw [compositeLengthAlpha, compositeLengthBeta]
    exact canonLengthEq
  · intro firstIndex secondIndex firstBound secondBound
    have firstBoundCanonical : firstIndex < baseCount
        + (processBrauer (canonicalMatchingSeed boundaryLength) atomsAlpha).openWires.length := by
      rw [← compositeLengthAlpha]; exact firstBound
    have secondBoundCanonical : secondIndex < baseCount
        + (processBrauer (canonicalMatchingSeed boundaryLength) atomsAlpha).openWires.length := by
      rw [← compositeLengthAlpha]; exact secondBound
    show isSameComponent (processBrauer midState atomsAlpha).links
        (natListGetAt (List.range baseCount ++ (processBrauer midState atomsAlpha).openWires) firstIndex)
        (natListGetAt (List.range baseCount ++ (processBrauer midState atomsAlpha).openWires) secondIndex)
      = isSameComponent (processBrauer midState atomsBeta).links
        (natListGetAt (List.range baseCount ++ (processBrauer midState atomsBeta).openWires) firstIndex)
        (natListGetAt (List.range baseCount ++ (processBrauer midState atomsBeta).openWires) secondIndex)
    rw [processBrauer_links_ofMidState midState boundaryLength atomsAlpha inRangeAlpha midTracks,
      processBrauer_openWires_ofMidState midState boundaryLength atomsAlpha midTracks,
      processBrauer_links_ofMidState midState boundaryLength atomsBeta inRangeBeta midTracks,
      processBrauer_openWires_ofMidState midState boundaryLength atomsBeta midTracks]
    exact compositeBoundaryView_agrees_ofViewParts midState.openWires midState.nextFresh discipline
      boundaryLength midTracks baseCount baseBelow
      (processBrauer (canonicalMatchingSeed boundaryLength) atomsAlpha)
      (processBrauer (canonicalMatchingSeed boundaryLength) atomsBeta)
      (brauerWordJoinEvents (canonicalMatchingSeed boundaryLength) atomsAlpha)
      (brauerWordJoinEvents (canonicalMatchingSeed boundaryLength) atomsBeta)
      midState.links linksAlpha linksBeta canonLengthEq canonViewAgrees forest baseBounded
      firstIndex secondIndex firstBoundCanonical secondBoundCanonical

/-! ## The spider prefix bridge — feed the loops-free legs into `SpiderConv.whisker` -/

/-- ★ **KEYSTONE16 — the prefix bridge for the spider partition congruence.**  For any in-range prefix and two
in-range words whose CANONICAL runs (at the post-prefix boundary width) agree on open-wire length + boundary view,
the two words fired after the prefix are `SpiderConv`-convertible.  The two `whisker` legs come straight out of the
loops-free functoriality port `processBrauer_forgetView_eq_ofCanonicalViewParts`; the reachable-state provenance is
discharged from the shipped Brauer invariants (`brauerReachable_conditions`) plus the distinctness invariant
(`relativeWireZoneDiscipline_ofBrauerReachable`).  Unlike `SpiderConv.whisker`, whose two obligations live at the
CONCRETE post-prefix state, this bridge's obligations live at the CANONICAL seed of the post-prefix width — so a
boundary-preserving prefix reuses the relation's own seed facts, prefix-independently. -/
theorem spiderConv_relation_afterPrefix (bottomCount : Nat) (bottomPos : 0 < bottomCount)
    (prefixAtoms wordLeft wordRight : List BrauerAtom)
    (prefixInRange : BrauerWordInRange bottomCount prefixAtoms)
    (inRangeLeft :
      BrauerWordInRange (processBrauer (brauerSeed bottomCount) prefixAtoms).openWires.length wordLeft)
    (inRangeRight :
      BrauerWordInRange (processBrauer (brauerSeed bottomCount) prefixAtoms).openWires.length wordRight)
    (canonLengthEq :
      (processBrauer (canonicalMatchingSeed
          (processBrauer (brauerSeed bottomCount) prefixAtoms).openWires.length) wordLeft).openWires.length
        = (processBrauer (canonicalMatchingSeed
          (processBrauer (brauerSeed bottomCount) prefixAtoms).openWires.length) wordRight).openWires.length)
    (canonViewAgrees : ∀ firstIndex secondIndex,
        firstIndex < (processBrauer (brauerSeed bottomCount) prefixAtoms).openWires.length
            + (processBrauer (canonicalMatchingSeed
                (processBrauer (brauerSeed bottomCount) prefixAtoms).openWires.length) wordLeft).openWires.length →
        secondIndex < (processBrauer (brauerSeed bottomCount) prefixAtoms).openWires.length
            + (processBrauer (canonicalMatchingSeed
                (processBrauer (brauerSeed bottomCount) prefixAtoms).openWires.length) wordLeft).openWires.length →
        matchingSameComponent (processBrauer (brauerSeed bottomCount) prefixAtoms).openWires.length
            (processBrauer (canonicalMatchingSeed
              (processBrauer (brauerSeed bottomCount) prefixAtoms).openWires.length) wordLeft)
            firstIndex secondIndex
          = matchingSameComponent (processBrauer (brauerSeed bottomCount) prefixAtoms).openWires.length
            (processBrauer (canonicalMatchingSeed
              (processBrauer (brauerSeed bottomCount) prefixAtoms).openWires.length) wordRight)
            firstIndex secondIndex) :
    SpiderConv bottomCount (prefixAtoms ++ wordLeft) (prefixAtoms ++ wordRight) := by
  have conditions := brauerReachable_conditions bottomCount bottomPos prefixAtoms
  have parts := processBrauer_forgetView_eq_ofCanonicalViewParts bottomCount
    (processBrauer (brauerSeed bottomCount) prefixAtoms).openWires.length
    (processBrauer (brauerSeed bottomCount) prefixAtoms)
    wordLeft wordRight inRangeLeft inRangeRight rfl
    conditions.fresh conditions.forest
    (relativeWireZoneDiscipline_ofBrauerReachable bottomCount bottomPos prefixAtoms prefixInRange)
    conditions.bottomLe canonLengthEq canonViewAgrees
  exact SpiderConv.whisker bottomCount prefixAtoms wordLeft wordRight parts.1 parts.2

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the LOOPS-FREE two-word functoriality port is SHIPPED (the FROB-3 residual).**
`processBrauer_forgetView_eq_ofCanonicalViewParts`: two Brauer words whose canonical runs agree on open-wire length
+ boundary `matchingSameComponent` view produce mid-state runs that agree on both, at ANY shared disciplined
mid-state.  It is the loops-free re-homing of `processBrauer_extract_eq_ofCanonicalExtractEq` — legs 1 (length) + 3
(view) kept, leg 2 (loops) dropped — through the cloned transfer bricks
(`canonicalTransfers_ofViewParts`, `compositeConnectivity_transfersAcrossInterface_ofViewParts`,
`compositeBoundaryView_agrees_ofViewParts`), none of which reads `loops`.  This is exactly why the special row
`μδ = 1` (unequal canonical loop counts) is no longer an obstruction.  `= true`. -/
def fxFrob_hasSpiderForgetViewFunctoriality : Bool := true

/-- ★ **Honesty marker — the spider PREFIX BRIDGE is SHIPPED.**  `spiderConv_relation_afterPrefix` supplies the two
`SpiderConv.whisker` legs from the CANONICAL (post-prefix width) view parts alone, so a relation whiskered after an
arbitrary prefix is a `SpiderConv` theorem without re-deciding the concrete post-prefix state.  The obligations live
at the canonical seed of the post-prefix width — prefix-independent for a boundary-preserving prefix (the relation's
own seed facts).  `= true`. -/
def fxFrob_hasSpiderPrefixBridge : Bool := true

end FX1Poly.Polygraph
