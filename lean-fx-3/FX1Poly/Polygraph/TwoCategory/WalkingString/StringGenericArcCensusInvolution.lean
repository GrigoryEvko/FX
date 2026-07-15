import FX1Poly.Polygraph.TwoCategory.WalkingString.StringGenericWidthArityBridge
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringGenericMidCupReadoff
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringGenericMidDropInjective
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMatchingPartnerInvolution
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcMatchViewFold
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusPartnerInvolution
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPerfectMatchingIndexBridge
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingWidthZeroInvolution

/-! # WalkingString — the GENERIC arc census / perfect-matching fold + the ANY-WIDTH partner involution
(FC-4 r7, the involution tranche of the generic cup-sort driver)

The r6 tranche markers named the generic SNAKE EXCLUSION as the ONE remaining node of the sort chain that
consumes `0 < midWidth` — it rides the positive-boundary partner involution, whose shipped `k = 2` port
(`stringMatchingOf_partner_isInvolution`, `StringMatchingPartnerInvolution`) rests on the two r30 arc-engine
fold capstones (`stringArcBoundaryCensus_ofChainedSpineList` / `stringArcPerfectMatchingTokens_ofChainedSpineList`,
`StringArcBoundaryCensusPerfectMatchingFold`).  Those capstones have exactly ONE signature-keyed hook — the total
cup/cap arity classifier — and the r5 B3 class field `generatorFullArity` supplies it generically
(`genericSpineAtom_hasCupOrCapArity`).  So the whole census / perfect-matching / involution tower re-founds ONCE
over `AdjointStringConnectivity`, verbatim modulo that one hook:

  * `genericArcBoundaryCensus_stepArcAtom` / `_processArcSpine_ofChained` / `_ofChainedSpineList` — the
    two-endpoint boundary census threads the whole chained arc fold, over the class.
  * `genericArcPerfectMatchingTokens_stepArcAtom` / `_processArcSpine_ofChained` / `_ofChainedSpineList` — the
    token-frame perfect matching threads the fold (the census threaded alongside for the cap step), over the class.
  * ★ `genericArcDiagram_partner_isInvolution` — the censused boundary matching is a fixed-point-free involution on
    the arc structure's `.diagram`, over the class.
  * ★ `genericMatchingOf_partner_isInvolution` / `_neSelf` — the involution + no-fixed-point TRANSPORTED to the
    plain `matchingOf` carrier across the `{signature}`-generic `arcDiagram_eq_matching` bridge (`0 < bottomCount`).
  * ★★ `genericMatchingPartner_isInvolution_anyWidth` — THE UNIFICATION: the involution at EVERY `midWidth`, NO
    positivity premise.  `midWidth = 0` dispatches to the `{signature}`-generic positivity-free width-`0` involution
    `matchingOfSpineListZero_partner_isInvolution` (which needs only `AllCupArity`); `midWidth = succ _` dispatches
    to the positive transport above (`SpineHasCupCapAtoms` from `AllCupArity` via
    `spineHasCupCapAtoms_ofAllCupArity`).  This is what lets the r7 snake exclusion / LOCATE / SORT DRIVER drop the
    `0 < midWidth` premise entirely and subsume BOTH shipped `k = 2` drivers (width-`0` and positive-mid) as
    instances of ONE fueled fold.

## The HONESTY LAW — fired at `k = 2` AND `k = 3`

  * ★ `k = 2` recovery — the generic involution at `adjointStringConnectivityAtTwo` re-derives the NAMED shipped
    `stringMatchingOf_partner_isInvolution` (`stringPartnerInvolution_shippedInhabitant` /
    `..._viaGenericClassAtTwo`, the same statement inhabited both ways).
  * ★ `k = 3` fires — the ANY-WIDTH involution runs on genuine adjoint-quadruple cups through BOTH branches: the
    width-`0` branch on the singleton `[η1]` (partner `[1, 0]`, round-trip `0 ↦ 1 ↦ 0`) and the positive branch on
    the mid-`1` single-survivor cup `quadMidOneCupOverL1` (partner `[3, 2, 1, 0]`, round-trip `1 ↦ 2 ↦ 1`), each
    cross-checked against the `by decide`-computed partner list, with a no-fixed-point negative control.

## What this file does NOT do (the FLIP LAW, honest round boundary)

The census marker `fxString_hasNColourAtomPinReroute` (`StringKParameterizationCensus`) STAYS `false` here: this is
the involution tranche only.  The generic snake exclusion + fueled LOCATE and the fueled SORT DRIVER + the `k = 3`
decision are the sibling r7 tranches, landed in `StringGenericMidSnakeLocate` / `StringGenericMidPureCupSortDriver`,
and only the closure file (`StringNColourAtomPinRerouteClosure`) adjudicates the census bill.

ADDITIVE ONLY: no shipped WalkingString file is touched; the FROZEN k = 2 involution and the r5/r6 generic bricks
are CONSUMED, never edited.  Raw Lean 4 + Init; structural recursion on the atom list, no `WellFounded.fix`;
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration `#assert_no_axioms` gated
in the audit twin plus an INDEPENDENT `#print axioms` witness. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private range / map plumbing (per-file copy with a distinct `GACI` suffix, keeping the umbrella build's
global table duplicate-free against the shipped involution / fold copies) -/

private theorem rangeLoopLengthGACI : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLengthGACI count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1, Nat.add_right_comm count accumulated.length 1]

private theorem rangeLengthGACI (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLengthGACI count []]
  exact Nat.add_zero count

private theorem rangeLoopGetAtPastGACI : (count : Nat) → (accumulated : List Nat) → (offset : Nat) →
    natListGetAt (List.range.loop count accumulated) (offset + count) = natListGetAt accumulated offset
  | 0, _, _ => rfl
  | count + 1, accumulated, offset => by
      have inner := rangeLoopGetAtPastGACI count (count :: accumulated) (offset + 1)
      rw [Nat.add_assoc offset 1 count, Nat.add_comm 1 count] at inner
      exact inner

private theorem rangeLoopGetAtBelowGACI : (count : Nat) → (accumulated : List Nat) →
    (index : Nat) → index < count →
    natListGetAt (List.range.loop count accumulated) index = index
  | 0, _, _, indexBelow => absurd indexBelow (Nat.not_succ_le_zero _)
  | count + 1, accumulated, index, indexBelow => by
      cases Nat.lt_or_ge index count with
      | inl below => exact rangeLoopGetAtBelowGACI count (count :: accumulated) index below
      | inr atLeast =>
          have indexEq : index = count :=
            Nat.le_antisymm (Nat.le_of_succ_le_succ indexBelow) atLeast
          have pastRead := rangeLoopGetAtPastGACI count (count :: accumulated) 0
          rw [Nat.zero_add count] at pastRead
          rw [indexEq]
          exact pastRead

private theorem rangeGetAtBelowGACI (count index : Nat) (indexBelow : index < count) :
    natListGetAt (List.range count) index = index :=
  rangeLoopGetAtBelowGACI count [] index indexBelow

private theorem natListGetAtMapRangeGACI (mapFunction : Nat → Nat) (total index : Nat)
    (inRange : index < total) :
    natListGetAt ((List.range total).map mapFunction) index = mapFunction index := by
  rw [natListGetAt_map_inRange mapFunction (List.range total) index
      (by rw [rangeLengthGACI]; exact inRange),
    rangeGetAtBelowGACI total index inRange]

/-! ## The per-atom census step over the class -/

/-- One boundary-tracked atom preserves the census, over the class: a cup via the splice preservation, a cap via
the window preservation.  The arc engine dispatches on the GENERIC total cup/cap classifier
`genericSpineAtom_hasCupOrCapArity cls` — the class-field replacement for the shipped
`adjointTripleSpineAtom_hasCupOrCapArity` hook, the ONE signature-keyed node of the whole fold. -/
theorem genericArcBoundaryCensus_stepArcAtom (cls : AdjointStringConnectivity)
    {overallSource overallTarget : cls.signature.graph.Mode}
    (seedBoundary : Nat) (state : ArcWireState)
    (atom : SpineAtom cls.signature overallSource overallTarget)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (seedBelowFresh : seedBoundary ≤ state.nextFresh)
    (tracksEntry : state.openWires.length = atom.domBoundaryLength)
    (oldCensus : ArcBoundaryCensus seedBoundary state) :
    ArcBoundaryCensus seedBoundary (stepArcAtom state atom) := by
  have entryShape : state.openWires.length
      = atom.leftContext.length + atom.generatorDom.length + atom.rightContext.length :=
    tracksEntry
  cases genericSpineAtom_hasCupOrCapArity cls atom with
  | inl cupArity =>
      obtain ⟨hasCupDomArity, hasCupCodArity⟩ := cupArity
      have cupInRange : atom.leftContext.length ≤ state.openWires.length := by
        rw [entryShape, hasCupDomArity, Nat.add_zero]
        exact Nat.le_add_right atom.leftContext.length atom.rightContext.length
      rw [stepArcAtom_eq_stepCupArc state atom hasCupDomArity hasCupCodArity]
      exact arcBoundaryCensus_stepCupArc seedBoundary state atom.leftContext.length
        fresh forest seedBelowFresh cupInRange oldCensus
  | inr capArity =>
      obtain ⟨hasCapDomArity, hasCapCodArity⟩ := capArity
      have capInRange : atom.leftContext.length + 2 ≤ state.openWires.length := by
        rw [entryShape, hasCapDomArity]
        exact Nat.le_add_right (atom.leftContext.length + 2) atom.rightContext.length
      rw [stepArcAtom_eq_stepCapArc state atom hasCapDomArity hasCapCodArity]
      exact arcBoundaryCensus_stepCapArc seedBoundary state atom.leftContext.length
        fresh forest seedBelowFresh capInRange oldCensus

/-! ## The whole-fold census transport and the canonical-seed capstone -/

/-- ★ **A chained spine's arc fold preserves the boundary census end-to-end, over the class** — the freshness /
forestness / boundary-tracking / seed-bound companions thread through the fold exactly as in the shipped `k = 2`
port, each atom's arity read off the class field. -/
theorem genericArcBoundaryCensus_processArcSpine_ofChained (cls : AdjointStringConnectivity)
    {overallSource overallTarget : cls.signature.graph.Mode} :
    (atoms : List (SpineAtom cls.signature overallSource overallTarget)) →
    (state : ArcWireState) → (boundaryLength seedBoundary : Nat) →
    ArcStateFresh state → isUnionFindForest state.links →
    state.openWires.length = boundaryLength →
    SpineBoundaryChained boundaryLength atoms →
    seedBoundary ≤ state.nextFresh →
    ArcBoundaryCensus seedBoundary state →
    ArcBoundaryCensus seedBoundary (processArcSpine state atoms)
  | [], _, _, _, _, _, _, _, _, census => census
  | headAtom :: restAtoms, state, _, seedBoundary, fresh, forest, tracks, chained,
      seedBelowFresh, census => by
      obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
      have tracksEntry : state.openWires.length = headAtom.domBoundaryLength :=
        tracks.trans headFires.symm
      have headArity := genericSpineAtom_hasCupOrCapArity cls headAtom
      show ArcBoundaryCensus seedBoundary
        (processArcSpine (stepArcAtom state headAtom) restAtoms)
      exact genericArcBoundaryCensus_processArcSpine_ofChained cls restAtoms
        (stepArcAtom state headAtom) headAtom.codBoundaryLength seedBoundary
        (arcStateFresh_stepArcAtom state headAtom fresh)
        (isUnionFindForest_stepArcAtom_ofCupOrCap state headAtom headArity forest)
        (stepArcAtom_openWires_tracksBoundary state headAtom headArity tracksEntry)
        tailChained
        (Nat.le_trans seedBelowFresh (stepArcAtom_nextFresh_le state headAtom))
        (genericArcBoundaryCensus_stepArcAtom cls seedBoundary state headAtom fresh forest
          seedBelowFresh tracksEntry census)

/-- ★ **The census capstone at the canonical seed, over the class**: every boundary-chained spine folds from the
fresh initial state to a state whose every component touches at most two boundary endpoints. -/
theorem genericArcBoundaryCensus_ofChainedSpineList (cls : AdjointStringConnectivity)
    {overallSource overallTarget : cls.signature.graph.Mode}
    (bottomCount : Nat)
    (atoms : List (SpineAtom cls.signature overallSource overallTarget))
    (chained : SpineBoundaryChained bottomCount atoms) :
    ArcBoundaryCensus bottomCount
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        atoms) :=
  genericArcBoundaryCensus_processArcSpine_ofChained cls atoms
    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) bottomCount bottomCount
    (arcStateFresh_initial bottomCount) isUnionFindForest_nil (rangeLengthGACI bottomCount)
    chained (Nat.le_refl bottomCount) (arcBoundaryCensus_initial bottomCount)

/-! ## The per-atom perfect-matching step over the class -/

/-- One boundary-tracked atom preserves the token-frame perfect matching, over the class: a cup via the splice
preservation, a cap via the census-coupled merge preservation. -/
theorem genericArcPerfectMatchingTokens_stepArcAtom (cls : AdjointStringConnectivity)
    {overallSource overallTarget : cls.signature.graph.Mode}
    (seedBoundary : Nat) (state : ArcWireState)
    (atom : SpineAtom cls.signature overallSource overallTarget)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (seedBelowFresh : seedBoundary ≤ state.nextFresh)
    (tracksEntry : state.openWires.length = atom.domBoundaryLength)
    (census : ArcBoundaryCensus seedBoundary state)
    (oldPerfect : ArcPerfectMatchingTokens seedBoundary state) :
    ArcPerfectMatchingTokens seedBoundary (stepArcAtom state atom) := by
  have entryShape : state.openWires.length
      = atom.leftContext.length + atom.generatorDom.length + atom.rightContext.length :=
    tracksEntry
  cases genericSpineAtom_hasCupOrCapArity cls atom with
  | inl cupArity =>
      obtain ⟨hasCupDomArity, hasCupCodArity⟩ := cupArity
      have cupInRange : atom.leftContext.length ≤ state.openWires.length := by
        rw [entryShape, hasCupDomArity, Nat.add_zero]
        exact Nat.le_add_right atom.leftContext.length atom.rightContext.length
      rw [stepArcAtom_eq_stepCupArc state atom hasCupDomArity hasCupCodArity]
      exact arcPerfectMatchingTokens_stepCupArc seedBoundary state atom.leftContext.length
        fresh forest seedBelowFresh cupInRange oldPerfect
  | inr capArity =>
      obtain ⟨hasCapDomArity, hasCapCodArity⟩ := capArity
      have capInRange : atom.leftContext.length + 2 ≤ state.openWires.length := by
        rw [entryShape, hasCapDomArity]
        exact Nat.le_add_right (atom.leftContext.length + 2) atom.rightContext.length
      rw [stepArcAtom_eq_stepCapArc state atom hasCapDomArity hasCapCodArity]
      exact arcPerfectMatchingTokens_stepCapArc seedBoundary state atom.leftContext.length
        forest capInRange census oldPerfect

/-! ## The whole-fold perfect-matching transport and the canonical-seed capstone -/

/-- ★ **A chained spine's arc fold preserves the token-frame perfect matching end-to-end, over the class** —
threading the census alongside for the cap step. -/
theorem genericArcPerfectMatchingTokens_processArcSpine_ofChained (cls : AdjointStringConnectivity)
    {overallSource overallTarget : cls.signature.graph.Mode} :
    (atoms : List (SpineAtom cls.signature overallSource overallTarget)) →
    (state : ArcWireState) → (boundaryLength seedBoundary : Nat) →
    ArcStateFresh state → isUnionFindForest state.links →
    state.openWires.length = boundaryLength →
    SpineBoundaryChained boundaryLength atoms →
    seedBoundary ≤ state.nextFresh →
    ArcBoundaryCensus seedBoundary state →
    ArcPerfectMatchingTokens seedBoundary state →
    ArcPerfectMatchingTokens seedBoundary (processArcSpine state atoms)
  | [], _, _, _, _, _, _, _, _, _, perfect => perfect
  | headAtom :: restAtoms, state, _, seedBoundary, fresh, forest, tracks, chained,
      seedBelowFresh, census, perfect => by
      obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
      have tracksEntry : state.openWires.length = headAtom.domBoundaryLength :=
        tracks.trans headFires.symm
      have headArity := genericSpineAtom_hasCupOrCapArity cls headAtom
      show ArcPerfectMatchingTokens seedBoundary
        (processArcSpine (stepArcAtom state headAtom) restAtoms)
      exact genericArcPerfectMatchingTokens_processArcSpine_ofChained cls restAtoms
        (stepArcAtom state headAtom) headAtom.codBoundaryLength seedBoundary
        (arcStateFresh_stepArcAtom state headAtom fresh)
        (isUnionFindForest_stepArcAtom_ofCupOrCap state headAtom headArity forest)
        (stepArcAtom_openWires_tracksBoundary state headAtom headArity tracksEntry)
        tailChained
        (Nat.le_trans seedBelowFresh (stepArcAtom_nextFresh_le state headAtom))
        (genericArcBoundaryCensus_stepArcAtom cls seedBoundary state headAtom fresh forest
          seedBelowFresh tracksEntry census)
        (genericArcPerfectMatchingTokens_stepArcAtom cls seedBoundary state headAtom fresh forest
          seedBelowFresh tracksEntry census perfect)

/-- ★ **The perfect-matching capstone at the canonical seed, over the class**: every boundary token of the folded
state has a distinct same-component boundary token — the `noFixedPoint` fact. -/
theorem genericArcPerfectMatchingTokens_ofChainedSpineList (cls : AdjointStringConnectivity)
    {overallSource overallTarget : cls.signature.graph.Mode}
    (bottomCount : Nat)
    (atoms : List (SpineAtom cls.signature overallSource overallTarget))
    (chained : SpineBoundaryChained bottomCount atoms) :
    ArcPerfectMatchingTokens bottomCount
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        atoms) :=
  genericArcPerfectMatchingTokens_processArcSpine_ofChained cls atoms
    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) bottomCount bottomCount
    (arcStateFresh_initial bottomCount) isUnionFindForest_nil (rangeLengthGACI bottomCount)
    chained (Nat.le_refl bottomCount) (arcBoundaryCensus_initial bottomCount)
    (arcPerfectMatchingTokens_initial bottomCount)

/-! ## The diagram-partner read-off (`{signature}`-generic, private per-file copy) -/

/-- The arc structure's `diagram.partner`, read at an in-range boundary index, IS the canonical `partnerIndexOf`
on the processed arc state's boundary — a `map`-of-range read-off (`{signature}`-generic: no arity hook). -/
private theorem genericArcDiagramPartnerReadAtGACI {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} (bottomCount : Nat)
    (spine : List (SpineAtom signature overallSource overallTarget))
    (index : Nat)
    (inRange : index < bottomCount
      + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          spine).openWires.length) :
    natListGetAt (arcStructureOfSpineList bottomCount spine).diagram.partner index
      = partnerIndexOf
          (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            spine).links
          (List.range bottomCount
            ++ (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                spine).openWires)
          (bottomCount
            + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                spine).openWires.length)
          index := by
  have partnerListEq :
      (arcStructureOfSpineList bottomCount spine).diagram.partner
        = (List.range (bottomCount
            + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                spine).openWires.length)).map
            (partnerIndexOf
              (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                spine).links
              (List.range bottomCount
                ++ (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                    spine).openWires)
              (bottomCount
                + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                    spine).openWires.length)) := rfl
  rw [partnerListEq]
  exact natListGetAtMapRangeGACI _ _ index inRange

/-! ## No fixed point at the extracted state of any chained spine, over the class -/

/-- **No fixed point at the extracted state of any chained spine, over the class.**  Threaded through the generic
token-frame perfect matching; the token → range bridge and the range-frame no-fixed-point discharge are
signature-BLIND. -/
private theorem genericPartnerIndexOf_neSelf_ofChainedSpineGACI (cls : AdjointStringConnectivity)
    {overallSource overallTarget : cls.signature.graph.Mode}
    (bottomCount : Nat)
    (atoms : List (SpineAtom cls.signature overallSource overallTarget))
    (chained : SpineBoundaryChained bottomCount atoms)
    (index : Nat)
    (indexInRange : index < bottomCount
      + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) atoms).openWires.length) :
    partnerIndexOf
        (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) atoms).links
        (List.range bottomCount
          ++ (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) atoms).openWires)
        (bottomCount
          + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) atoms).openWires.length)
        index
      ≠ index :=
  partnerIndexOf_neSelf_ofPerfectMatching bottomCount
    (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) atoms)
    (arcPerfectMatching_ofTokens bottomCount
      (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) atoms)
      (genericArcPerfectMatchingTokens_ofChainedSpineList cls bottomCount atoms chained))
    index indexInRange

/-! ## The involution IN the arc structure, over the class -/

/-- ★ **The boundary matching is an involution IN the arc structure, over the class.**  A non-fixed partner read
on the arc structure's boundary `.diagram` maps back to the source, bridging the raw `partnerIndexOf_isInvolution`
through the diagram read-off at both the source index and its (in-range) partner. -/
theorem genericArcDiagram_partner_isInvolution (cls : AdjointStringConnectivity)
    {overallSource overallTarget : cls.signature.graph.Mode} (bottomCount : Nat)
    (spine : List (SpineAtom cls.signature overallSource overallTarget))
    (chained : SpineBoundaryChained bottomCount spine)
    (index : Nat)
    (inRange : index < bottomCount
      + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          spine).openWires.length)
    (notFixed : natListGetAt (arcStructureOfSpineList bottomCount spine).diagram.partner index
      ≠ index) :
    natListGetAt (arcStructureOfSpineList bottomCount spine).diagram.partner
        (natListGetAt (arcStructureOfSpineList bottomCount spine).diagram.partner index)
      = index := by
  have census := genericArcBoundaryCensus_ofChainedSpineList cls bottomCount spine chained
  have readIndex := genericArcDiagramPartnerReadAtGACI bottomCount spine index inRange
  have partnerBelow := partnerIndexOf_below
    (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) spine)
    bottomCount index inRange
  have notFixed' :
      partnerIndexOf
          (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            spine).links
          (List.range bottomCount
            ++ (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                spine).openWires)
          (bottomCount
            + (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
                spine).openWires.length)
          index
        ≠ index := fun partnerEqIndex => notFixed (readIndex.trans partnerEqIndex)
  rw [readIndex, genericArcDiagramPartnerReadAtGACI bottomCount spine _ partnerBelow]
  exact partnerIndexOf_isInvolution bottomCount
    (processArcSpine (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) spine)
    census index inRange notFixed'

/-! ## The transported involution on the plain `matchingOf` carrier, over the class -/

/-- ★ **The boundary matching is a fixed-point-free involution on `matchingOf`, over the class** (positive bottom
boundary).  Landed by transport across the `{signature}`-generic `arcDiagram_eq_matching` bridge. -/
theorem genericMatchingOf_partner_isInvolution (cls : AdjointStringConnectivity)
    {overallSource overallTarget : cls.signature.graph.Mode} (bottomCount : Nat)
    (bottomPos : 0 < bottomCount)
    (spine : List (SpineAtom cls.signature overallSource overallTarget))
    (arity : SpineHasCupCapAtoms spine) (chained : SpineBoundaryChained bottomCount spine)
    (index : Nat)
    (inRange : index < bottomCount + (matchingOfSpineList bottomCount spine).topCount)
    (notFixed : natListGetAt (matchingOfSpineList bottomCount spine).partner index ≠ index) :
    natListGetAt (matchingOfSpineList bottomCount spine).partner
        (natListGetAt (matchingOfSpineList bottomCount spine).partner index)
      = index := by
  have bridge : (arcStructureOfSpineList bottomCount spine).diagram
      = matchingOfSpineList bottomCount spine :=
    arcDiagram_eq_matching bottomCount spine arity chained bottomPos
  rw [← bridge] at inRange notFixed ⊢
  exact genericArcDiagram_partner_isInvolution cls bottomCount spine chained index inRange notFixed

/-- ★ **The boundary matching has NO fixed point on `matchingOf`, over the class** (positive bottom boundary).
Transported from the generic no-fixed-point through the diagram-partner read-off and the bridge. -/
theorem genericMatchingOf_partner_neSelf (cls : AdjointStringConnectivity)
    {overallSource overallTarget : cls.signature.graph.Mode} (bottomCount : Nat)
    (bottomPos : 0 < bottomCount)
    (spine : List (SpineAtom cls.signature overallSource overallTarget))
    (arity : SpineHasCupCapAtoms spine) (chained : SpineBoundaryChained bottomCount spine)
    (index : Nat)
    (inRange : index < bottomCount + (matchingOfSpineList bottomCount spine).topCount) :
    natListGetAt (matchingOfSpineList bottomCount spine).partner index ≠ index := by
  have bridge : (arcStructureOfSpineList bottomCount spine).diagram
      = matchingOfSpineList bottomCount spine :=
    arcDiagram_eq_matching bottomCount spine arity chained bottomPos
  rw [← bridge] at inRange ⊢
  rw [genericArcDiagramPartnerReadAtGACI bottomCount spine index inRange]
  exact genericPartnerIndexOf_neSelf_ofChainedSpineGACI cls bottomCount spine chained index inRange

/-! ## ★★ THE UNIFICATION — the partner involution at EVERY mid-width, NO positivity premise -/

/-- ★★ **The partner involution at EVERY `midWidth` — the positivity premise DISPATCHED AWAY.**  For a
boundary-chained PURE-CUP spine over ANY `midWidth` bottom boundary, a non-fixed boundary port's
partner-of-partner is the port again.  `midWidth = 0` routes through the `{signature}`-generic positivity-free
width-`0` involution `matchingOfSpineListZero_partner_isInvolution` (which needs only the `AllCupArity` witness);
`midWidth = succ _` routes through the positive-boundary transport `genericMatchingOf_partner_isInvolution`
(`SpineHasCupCapAtoms` from `AllCupArity` via `spineHasCupCapAtoms_ofAllCupArity`).  This is the node that lets
the r7 snake exclusion — and with it the fueled LOCATE and the fueled SORT DRIVER — run at EVERY `midWidth`,
subsuming BOTH shipped `k = 2` drivers (width-`0` and positive-mid) under ONE generic fueled fold. -/
theorem genericMatchingPartner_isInvolution_anyWidth (cls : AdjointStringConnectivity)
    {overallSource overallTarget : cls.signature.graph.Mode} (midWidth : Nat)
    (spine : List (SpineAtom cls.signature overallSource overallTarget))
    (chained : SpineBoundaryChained midWidth spine)
    (pureCup : AllCupArity spine)
    (index : Nat)
    (inRange : index < midWidth + (matchingOfSpineList midWidth spine).topCount)
    (notFixed : natListGetAt (matchingOfSpineList midWidth spine).partner index ≠ index) :
    natListGetAt (matchingOfSpineList midWidth spine).partner
        (natListGetAt (matchingOfSpineList midWidth spine).partner index)
      = index := by
  cases midWidth with
  | zero =>
      exact matchingOfSpineListZero_partner_isInvolution spine pureCup index inRange notFixed
  | succ midPred =>
      exact genericMatchingOf_partner_isInvolution cls (midPred + 1) (Nat.succ_pos midPred) spine
        (spineHasCupCapAtoms_ofAllCupArity spine pureCup) chained index inRange notFixed

/-! ## `k = 2` RECOVERY — the generic involution re-derives the NAMED shipped `k = 2` involution -/

/-- The statement of the shipped `k = 2` `matchingOf` partner involution, named as the recovery TARGET. -/
abbrev StringPartnerInvolutionStatement : Prop :=
  ∀ {overallSource overallTarget : adjointTripleGraph.Mode} (bottomCount : Nat),
    0 < bottomCount →
    ∀ (spine : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)),
    SpineHasCupCapAtoms spine → SpineBoundaryChained bottomCount spine →
    ∀ (index : Nat),
    index < bottomCount + (matchingOfSpineList bottomCount spine).topCount →
    natListGetAt (matchingOfSpineList bottomCount spine).partner index ≠ index →
    natListGetAt (matchingOfSpineList bottomCount spine).partner
        (natListGetAt (matchingOfSpineList bottomCount spine).partner index)
      = index

/-- ★ **The shipped `k = 2` involution inhabits the named statement** —
`stringMatchingOf_partner_isInvolution` IS the recovery target. -/
theorem stringPartnerInvolution_shippedInhabitant : StringPartnerInvolutionStatement :=
  fun bottomCount bottomPos spine arity chained index inRange notFixed =>
    stringMatchingOf_partner_isInvolution bottomCount bottomPos spine arity chained index inRange
      notFixed

/-- ★★ **The generic involution, at `k = 2`, RE-DERIVES the shipped involution** — the genuine consumption check
at `adjointStringConnectivityAtTwo` (whose `.signature` is defeq to `adjointTripleModeSignature`). -/
theorem stringPartnerInvolution_viaGenericClassAtTwo : StringPartnerInvolutionStatement :=
  fun bottomCount bottomPos spine arity chained index inRange notFixed =>
    genericMatchingOf_partner_isInvolution adjointStringConnectivityAtTwo bottomCount bottomPos
      spine arity chained index inRange notFixed

/-! ## `k = 3` FIRES — the ANY-WIDTH involution runs through BOTH branches on genuine quad cups -/

/-- The width-`0` quad singleton `[η1]` computes partner `[1, 0]` — the cup's two legs match each other. -/
theorem quadInvolutionWidthZero_matchingComputes :
    (matchingOfSpineList 0 [quadDropUnitOneW0]).partner = [1, 0] := by decide

/-- ★ **The ANY-WIDTH involution FIRES at `k = 3` through the width-`0` branch.**  On the quad singleton `[η1]`
(partner `[1, 0]`), the port `0` is non-fixed (`0 ↦ 1`) and the involution round-trips `0 ↦ 1 ↦ 0` — computed
through `adjointStringConnectivityAtThree` at `midWidth = 0`, the positivity-free dispatch arm. -/
theorem genericInvolutionAnyWidth_firesAtThreeWidthZero :
    natListGetAt (matchingOfSpineList 0 [quadDropUnitOneW0]).partner
        (natListGetAt (matchingOfSpineList 0 [quadDropUnitOneW0]).partner 0)
      = 0 :=
  genericMatchingPartner_isInvolution_anyWidth adjointStringConnectivityAtThree 0
    [quadDropUnitOneW0]
    (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.nil _))
    (AllCupArity.cons rfl rfl AllCupArity.nil)
    0 (by decide) (by decide)

/-- ★ **The ANY-WIDTH involution FIRES at `k = 3` through the POSITIVE branch.**  On the mid-`1` single-survivor
quad cup `quadMidOneCupOverL1` (partner `[3, 2, 1, 0]`), the port `1` is non-fixed (`1 ↦ 2`) and the involution
round-trips `1 ↦ 2 ↦ 1` — computed through `adjointStringConnectivityAtThree` at `midWidth = 1`, exercising the
positive-boundary census / perfect-matching / bridge tower at three colours. -/
theorem genericInvolutionAnyWidth_firesAtThreeMidOne :
    natListGetAt (matchingOfSpineList 1 [quadMidOneCupOverL1]).partner
        (natListGetAt (matchingOfSpineList 1 [quadMidOneCupOverL1]).partner 1)
      = 1 :=
  genericMatchingPartner_isInvolution_anyWidth adjointStringConnectivityAtThree 1
    [quadMidOneCupOverL1]
    (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.nil _))
    (AllCupArity.cons rfl rfl AllCupArity.nil)
    1 (by decide) (by decide)

/-- ★ **Negative control: the `k = 3` no-fixed-point is genuine.**  On the mid-`1` quad cup, the port `1`'s
partner is `2 ≠ 1` — derived through the generic transported no-fixed-point at
`adjointStringConnectivityAtThree` (positive branch), not read off the computed list. -/
theorem genericNeSelf_firesAtThreeMidOne :
    natListGetAt (matchingOfSpineList 1 [quadMidOneCupOverL1]).partner 1 ≠ 1 :=
  genericMatchingOf_partner_neSelf adjointStringConnectivityAtThree 1 (by decide)
    [quadMidOneCupOverL1]
    (spineHasCupCapAtoms_ofAllCupArity [quadMidOneCupOverL1]
      (AllCupArity.cons rfl rfl AllCupArity.nil))
    (SpineBoundaryChained.cons _ rfl (SpineBoundaryChained.nil _))
    1 (by decide)

/-! ## Road marker -/

/-- **★ ESTABLISHED — the generic arc census / perfect-matching fold + the ANY-WIDTH partner involution are
machine-checked (FC-4 r7, the involution tranche of the generic cup-sort driver).**  The whole shipped `k = 2`
census / perfect-matching / involution tower (`StringArcBoundaryCensusPerfectMatchingFold` +
`StringMatchingPartnerInvolution`) re-founded ONCE over `AdjointStringConnectivity`, verbatim modulo its ONE
signature-keyed hook — the total cup/cap classifier, supplied by the r5 B3 class field
(`genericSpineAtom_hasCupOrCapArity`).  Capstones: `genericArcBoundaryCensus_ofChainedSpineList` /
`genericArcPerfectMatchingTokens_ofChainedSpineList` / `genericArcDiagram_partner_isInvolution` /
`genericMatchingOf_partner_isInvolution` / `_neSelf`, and THE UNIFICATION
`genericMatchingPartner_isInvolution_anyWidth` — the involution at EVERY `midWidth` with NO positivity premise
(width-`0` dispatches to the `{signature}`-generic `matchingOfSpineListZero_partner_isInvolution`, positive
dispatches to the transported tower).  The HONESTY LAW discharged: the generic involution recovers the NAMED
shipped `stringMatchingOf_partner_isInvolution` at `k = 2` (`stringPartnerInvolution_shippedInhabitant` /
`..._viaGenericClassAtTwo`) AND the any-width form fires at `k = 3` through BOTH dispatch branches
(`genericInvolutionAnyWidth_firesAtThreeWidthZero` / `..._firesAtThreeMidOne`) with a no-fixed-point negative
control.

  What this marker does NOT close (THE FLIP LAW): the census marker `fxString_hasNColourAtomPinReroute`
  (`StringKParameterizationCensus`) STAYS `false` here — the generic snake exclusion + fueled LOCATE
  (`StringGenericMidSnakeLocate`) and the fueled SORT DRIVER + `k = 3` decision
  (`StringGenericMidPureCupSortDriver`) are the sibling r7 tranches; the closure adjudication lives in
  `StringNColourAtomPinRerouteClosure`.  `= true`. -/
def fxString_hasGenericArcCensusInvolution : Bool := true

end FX1Poly.Polygraph
