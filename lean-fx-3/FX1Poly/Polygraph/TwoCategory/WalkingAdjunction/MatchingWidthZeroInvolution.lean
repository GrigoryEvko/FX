import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingBoundaryIndexCensus
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingStepCupOldPartner
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingLastCupShortChord
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWireDistinct

/-! # MatchingWidthZeroInvolution — the width-0 pure-cup partner INVOLUTION, POSITIVITY-FREE (Track B b#1)

The make-or-break of the width-0 LOCATE stack: the boundary matching's partner map is a fixed-point-free
involution on `matchingOfSpineList 0` for a pure-cup spine.  The shipped `matchingOf_partner_isInvolution`
transports the arc-carrier involution across `arcDiagram_eq_matching` and hard-requires `0 < bottomCount`,
DEAD at the width-0 seed (identifier `0` is a real cup leg colliding with the extract's `0` sentinel).

This file discharges it DIRECTLY.  Two positivity-free fold invariants over the pure-cup `processSpine` run
from the width-`0` seed carry the census the carrier-free involution
(`partnerIndexOf_isInvolution_ofBoundaryIndexCensus`, `MatchingBoundaryIndexCensus`) needs:

  * ★ `NodeRootClassSmall` — every union-find component among nodes `< nextFresh` has AT MOST two members.
    Vacuous at the seed (`nextFresh = 0`); each cup adds exactly the size-2 fresh class `{nf, nf+1}` (root
    `nf + 1`) disjoint from every old class (`stepCup_freshComponentRoot` / `unionFindRootOf_stepCup_old`,
    old roots `< nf < nf + 1`), so it folds through the pure-cup block with NO sentinel.

  * width-0 open-wire distinctness — `stepCup_wireListDistinct` folds positivity-free (each cup splices two
    fresh legs into a distinct list).

Assembling the two (distinct positions ⇒ distinct reads, all reads `< nextFresh`, ≤ 2 per class) gives the
carrier-free `BoundaryIndexCensus` at the width-0 matching state; the carrier-free involution then lands the
partner involution on `matchingOfSpineList 0`, POSITIVITY-FREE — no `arcDiagram_eq_matching`, no
`0 < bottomCount`.

Raw Lean 4 + Init; structural recursion, no `omega` / `simp`-AC / `WellFounded.fix`.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private list plumbing (per-file copies) -/

private theorem natListGetAt_mem_inRange :
    (wires : List Nat) → (index : Nat) → index < wires.length → natListGetAt wires index ∈ wires
  | [], _, indexInRange => absurd indexInRange (Nat.not_lt_zero _)
  | _ :: _, 0, _ => List.Mem.head _
  | _ :: rest, index + 1, indexInRange =>
      List.Mem.tail _ (natListGetAt_mem_inRange rest index (Nat.lt_of_succ_lt_succ indexInRange))

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

private theorem distinctReadNe (wires : List Nat) (distinct : WireListDistinct wires)
    (firstPos secondPos : Nat) (firstLt : firstPos < wires.length)
    (secondLt : secondPos < wires.length) (posNeq : firstPos ≠ secondPos) :
    natListGetAt wires firstPos ≠ natListGetAt wires secondPos := by
  cases Nat.lt_or_ge firstPos secondPos with
  | inl firstLtSecond => exact distinct firstPos secondPos firstLtSecond secondLt
  | inr secondLeFirst =>
      have secondLtFirst : secondPos < firstPos :=
        Nat.lt_of_le_of_ne secondLeFirst (fun secondEqFirst => posNeq secondEqFirst.symm)
      exact fun readsEqual => distinct secondPos firstPos secondLtFirst firstLt readsEqual.symm

/-! ## The node-value root-class census invariant -/

/-- ★ **Every union-find component among nodes `< nextFresh` has at most two members.**  Three distinct
below-`nextFresh` nodes cannot pairwise share a component root.  The node-value (position-independent)
rendering of the two-endpoint census; vacuous at the width-`0` seed and preserved by every cup. -/
def NodeRootClassSmall (state : WireState) : Prop :=
  ∀ nodeOne nodeTwo nodeThree : Nat,
    nodeOne < state.nextFresh → nodeTwo < state.nextFresh → nodeThree < state.nextFresh →
    nodeOne ≠ nodeTwo → nodeOne ≠ nodeThree → nodeTwo ≠ nodeThree →
    unionFindRootOf state.links nodeOne = unionFindRootOf state.links nodeTwo →
    unionFindRootOf state.links nodeOne = unionFindRootOf state.links nodeThree →
    False

/-- A node below `nextFresh + 2` is either old (`< nextFresh`) or one of the two fresh legs. -/
private theorem nodeOldOrFresh (nextFresh node : Nat) (nodeLt : node < nextFresh + 2) :
    node < nextFresh ∨ node = nextFresh ∨ node = nextFresh + 1 := by
  cases Nat.lt_or_ge node nextFresh with
  | inl below => exact Or.inl below
  | inr atLeast =>
      obtain ⟨offset, offsetEq⟩ := Nat.le.dest atLeast
      cases offset with
      | zero => exact Or.inr (Or.inl (offsetEq.symm.trans (Nat.add_zero nextFresh)))
      | succ offsetPred =>
          cases offsetPred with
          | zero => exact Or.inr (Or.inr offsetEq.symm)
          | succ deeper =>
              have twoLe : 2 ≤ Nat.succ (Nat.succ deeper) :=
                Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le deeper))
              have bound : nextFresh + 2 ≤ node := offsetEq ▸ Nat.add_le_add_left twoLe nextFresh
              exact absurd nodeLt (Nat.not_lt.mpr bound)

/-- An OLD node (`< nextFresh`) keeps its root through a cup and that root stays below `nextFresh`. -/
private theorem oldNodeRoot (state : WireState) (position : Nat) (fresh : WireStateFresh state)
    (forest : isUnionFindForest state.links) (node : Nat) (nodeBelow : node < state.nextFresh) :
    unionFindRootOf (stepCup state position).links node = unionFindRootOf state.links node
      ∧ unionFindRootOf state.links node < state.nextFresh := by
  have parentsBelow : ∀ edge ∈ state.links, edge.2 < state.nextFresh :=
    fun edge edgeMem => (fresh.2 edge edgeMem).2
  have rootLow : unionFindRootOf state.links node < state.nextFresh :=
    unionFindRootOf_lt state.nextFresh state.links parentsBelow node nodeBelow
  exact ⟨unionFindRootOf_stepCup_old state position fresh forest node rootLow, rootLow⟩

/-- A FRESH leg (`nextFresh` or `nextFresh + 1`) roots to `nextFresh + 1` through a cup. -/
private theorem freshNodeRoot (state : WireState) (position : Nat) (fresh : WireStateFresh state)
    (forest : isUnionFindForest state.links) (node : Nat)
    (nodeFresh : node = state.nextFresh ∨ node = state.nextFresh + 1) :
    unionFindRootOf (stepCup state position).links node = state.nextFresh + 1 := by
  cases nodeFresh with
  | inl isLeft => rw [isLeft]; exact (stepCup_freshComponentRoot state position fresh forest).1
  | inr isRight => rw [isRight]; exact (stepCup_freshComponentRoot state position fresh forest).2

/-- Three distinct nodes cannot all lie in the two-element fresh leg set `{nextFresh, nextFresh + 1}`. -/
private theorem notThreeFresh (nextFresh nodeOne nodeTwo nodeThree : Nat)
    (oneFresh : nodeOne = nextFresh ∨ nodeOne = nextFresh + 1)
    (twoFresh : nodeTwo = nextFresh ∨ nodeTwo = nextFresh + 1)
    (threeFresh : nodeThree = nextFresh ∨ nodeThree = nextFresh + 1)
    (oneNeTwo : nodeOne ≠ nodeTwo) (oneNeThree : nodeOne ≠ nodeThree)
    (twoNeThree : nodeTwo ≠ nodeThree) : False := by
  cases oneFresh with
  | inl oneLeft =>
      have twoRight : nodeTwo = nextFresh + 1 := by
        cases twoFresh with
        | inl twoLeft => exact absurd (oneLeft.trans twoLeft.symm) oneNeTwo
        | inr twoRight => exact twoRight
      have threeRight : nodeThree = nextFresh + 1 := by
        cases threeFresh with
        | inl threeLeft => exact absurd (oneLeft.trans threeLeft.symm) oneNeThree
        | inr threeRight => exact threeRight
      exact twoNeThree (twoRight.trans threeRight.symm)
  | inr oneRight =>
      have twoLeft : nodeTwo = nextFresh := by
        cases twoFresh with
        | inl twoLeft => exact twoLeft
        | inr twoRight => exact absurd (oneRight.trans twoRight.symm) oneNeTwo
      have threeLeft : nodeThree = nextFresh := by
        cases threeFresh with
        | inl threeLeft => exact threeLeft
        | inr threeRight => exact absurd (oneRight.trans threeRight.symm) oneNeThree
      exact twoNeThree (twoLeft.trans threeLeft.symm)

/-- ★ **A cup preserves the node-value root-class census.**  Each node below `nextFresh + 2` roots either
below `nextFresh` (old, unchanged) or to `nextFresh + 1` (fresh leg).  Three distinct nodes with pairwise
equal cup-roots: an old/fresh mix forces `nextFresh + 1 = (root < nextFresh)`, impossible; all old reduces
to the base census; all fresh is three distinct nodes in a two-element set. -/
private theorem nodeRootClassSmall_stepCup (state : WireState) (position : Nat)
    (fresh : WireStateFresh state) (forest : isUnionFindForest state.links)
    (base : NodeRootClassSmall state) :
    NodeRootClassSmall (stepCup state position) := by
  intro nodeOne nodeTwo nodeThree oneLt twoLt threeLt oneNeTwo oneNeThree twoNeThree
    rootOneTwo rootOneThree
  rw [stepCup_nextFresh] at oneLt twoLt threeLt
  -- classify node one: old or fresh; each branch forces the other two into the same class
  cases nodeOldOrFresh state.nextFresh nodeOne oneLt with
  | inl oneOld =>
      -- node one is OLD: its cup-root is < nextFresh, forcing the others old too
      obtain ⟨oneRootEq, oneRootLow⟩ := oldNodeRoot state position fresh forest nodeOne oneOld
      have twoOld : nodeTwo < state.nextFresh := by
        cases nodeOldOrFresh state.nextFresh nodeTwo twoLt with
        | inl twoOld => exact twoOld
        | inr twoFresh =>
            exfalso
            have twoRootHigh := freshNodeRoot state position fresh forest nodeTwo twoFresh
            have clash : state.nextFresh + 1 = unionFindRootOf state.links nodeOne :=
              twoRootHigh.symm.trans (rootOneTwo.symm.trans oneRootEq)
            exact Nat.not_lt.mpr (Nat.le_of_eq clash) (Nat.lt_trans (Nat.lt_succ_self _)
              (Nat.succ_lt_succ oneRootLow))
      have threeOld : nodeThree < state.nextFresh := by
        cases nodeOldOrFresh state.nextFresh nodeThree threeLt with
        | inl threeOld => exact threeOld
        | inr threeFresh =>
            exfalso
            have threeRootHigh := freshNodeRoot state position fresh forest nodeThree threeFresh
            have clash : state.nextFresh + 1 = unionFindRootOf state.links nodeOne :=
              threeRootHigh.symm.trans (rootOneThree.symm.trans oneRootEq)
            exact Nat.not_lt.mpr (Nat.le_of_eq clash) (Nat.lt_trans (Nat.lt_succ_self _)
              (Nat.succ_lt_succ oneRootLow))
      obtain ⟨twoRootEq, _⟩ := oldNodeRoot state position fresh forest nodeTwo twoOld
      obtain ⟨threeRootEq, _⟩ := oldNodeRoot state position fresh forest nodeThree threeOld
      exact base nodeOne nodeTwo nodeThree oneOld twoOld threeOld oneNeTwo oneNeThree twoNeThree
        (oneRootEq.symm.trans (rootOneTwo.trans twoRootEq))
        (oneRootEq.symm.trans (rootOneThree.trans threeRootEq))
  | inr oneFresh =>
      -- node one is FRESH: its cup-root is nextFresh+1, forcing the others fresh too
      have oneRootHigh := freshNodeRoot state position fresh forest nodeOne oneFresh
      have twoFresh : nodeTwo = state.nextFresh ∨ nodeTwo = state.nextFresh + 1 := by
        cases nodeOldOrFresh state.nextFresh nodeTwo twoLt with
        | inr twoFresh => exact twoFresh
        | inl twoOld =>
            exfalso
            obtain ⟨twoRootEq, twoRootLow⟩ := oldNodeRoot state position fresh forest nodeTwo twoOld
            have clash : state.nextFresh + 1 = unionFindRootOf state.links nodeTwo :=
              oneRootHigh.symm.trans (rootOneTwo.trans twoRootEq)
            exact Nat.not_lt.mpr (Nat.le_of_eq clash) (Nat.lt_trans (Nat.lt_succ_self _)
              (Nat.succ_lt_succ twoRootLow))
      have threeFresh : nodeThree = state.nextFresh ∨ nodeThree = state.nextFresh + 1 := by
        cases nodeOldOrFresh state.nextFresh nodeThree threeLt with
        | inr threeFresh => exact threeFresh
        | inl threeOld =>
            exfalso
            obtain ⟨threeRootEq, threeRootLow⟩ := oldNodeRoot state position fresh forest nodeThree threeOld
            have clash : state.nextFresh + 1 = unionFindRootOf state.links nodeThree :=
              oneRootHigh.symm.trans (rootOneThree.trans threeRootEq)
            exact Nat.not_lt.mpr (Nat.le_of_eq clash) (Nat.lt_trans (Nat.lt_succ_self _)
              (Nat.succ_lt_succ threeRootLow))
      exact notThreeFresh state.nextFresh nodeOne nodeTwo nodeThree oneFresh twoFresh threeFresh
        oneNeTwo oneNeThree twoNeThree

/-- ★ **A pure-cup block preserves the node-value root-class census.**  `AllCupArity` induction, threading
`WireStateFresh` (`stepCup_wireStateFresh`) and the forest (`isUnionFindForest_stepCup`) alongside the
census, each cup step discharged by `nodeRootClassSmall_stepCup`.  Positivity-free (the cup sentinel never
fires). -/
private theorem nodeRootClassSmall_processSpine_ofAllCup
    {overallSource overallTarget : adjunctionGraph.Mode}
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (pureCup : AllCupArity atoms) :
    (state : WireState) → WireStateFresh state → isUnionFindForest state.links →
    NodeRootClassSmall state → NodeRootClassSmall (processSpine state atoms) := by
  induction pureCup with
  | nil => intro state _ _ base; exact base
  | cons hasCupDomArity hasCupCodArity _restAllCup restCensus =>
      rename_i headAtom rest
      intro state fresh forest base
      show NodeRootClassSmall (processSpine (stepAtom state headAtom) rest)
      rw [stepAtom_ofCupArity state headAtom hasCupDomArity hasCupCodArity]
      exact restCensus (stepCup state headAtom.leftContext.length)
        (stepCup_wireStateFresh state headAtom.leftContext.length fresh)
        (isUnionFindForest_stepCup state headAtom.leftContext.length forest)
        (nodeRootClassSmall_stepCup state headAtom.leftContext.length fresh forest base)

/-- The width-`0` seed satisfies the node census vacuously (`nextFresh = 0`). -/
private theorem nodeRootClassSmall_seedZero :
    NodeRootClassSmall ⟨List.range 0, [], 0, 0⟩ := by
  intro nodeOne _ _ oneLt _ _ _ _ _ _ _
  exact absurd oneLt (Nat.not_lt_zero nodeOne)

/-! ## Open-wire distinctness at the width-0 seed (positivity-free) -/

/-- A pure-cup block preserves open-wire distinctness from the width-`0` seed — each cup splices two fresh
legs (`stepCup_wireListDistinct`), no cap sentinel needed. -/
private theorem wireListDistinct_processSpine_ofAllCup
    {overallSource overallTarget : adjunctionGraph.Mode}
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (pureCup : AllCupArity atoms) :
    (state : WireState) → WireStateFresh state → WireListDistinct state.openWires →
    WireListDistinct (processSpine state atoms).openWires := by
  induction pureCup with
  | nil => intro state _ distinct; exact distinct
  | cons hasCupDomArity hasCupCodArity _restAllCup restDistinct =>
      rename_i headAtom rest
      intro state fresh distinct
      show WireListDistinct (processSpine (stepAtom state headAtom) rest).openWires
      rw [stepAtom_ofCupArity state headAtom hasCupDomArity hasCupCodArity]
      exact restDistinct (stepCup state headAtom.leftContext.length)
        (stepCup_wireStateFresh state headAtom.leftContext.length fresh)
        (stepCup_wireListDistinct state headAtom.leftContext.length fresh distinct)

/-! ## The width-0 boundary-index census, discharged -/

/-- ★ **The width-`0` pure-cup matching state satisfies the carrier-free boundary-index census.**  Three
distinct in-range boundary indices read three distinct open wires (open-wire distinctness), each below
`nextFresh` (`WireStateFresh`); pairwise same-component means pairwise equal roots, so the node census
(each component `≤ 2` members) is violated. -/
theorem widthZeroPureCup_boundaryIndexCensus
    {overallSource overallTarget : adjunctionGraph.Mode}
    (spine : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (pureCup : AllCupArity spine) :
    BoundaryIndexCensus (processSpine ⟨List.range 0, [], 0, 0⟩ spine).links
      (List.range 0 ++ (processSpine ⟨List.range 0, [], 0, 0⟩ spine).openWires)
      (0 + (processSpine ⟨List.range 0, [], 0, 0⟩ spine).openWires.length) := by
  have fresh : WireStateFresh (processSpine ⟨List.range 0, [], 0, 0⟩ spine) :=
    wireStateFresh_processSpine_ofAllCup spine pureCup ⟨List.range 0, [], 0, 0⟩ (wireStateFresh_initial 0)
  have census : NodeRootClassSmall (processSpine ⟨List.range 0, [], 0, 0⟩ spine) :=
    nodeRootClassSmall_processSpine_ofAllCup spine pureCup ⟨List.range 0, [], 0, 0⟩
      (wireStateFresh_initial 0) isUnionFindForest_nil nodeRootClassSmall_seedZero
  have distinct : WireListDistinct (processSpine ⟨List.range 0, [], 0, 0⟩ spine).openWires :=
    wireListDistinct_processSpine_ofAllCup spine pureCup ⟨List.range 0, [], 0, 0⟩
      (wireStateFresh_initial 0) (by intro indexOne _ _ twoInRange; exact absurd twoInRange (Nat.not_lt_zero _))
  intro indexOne indexTwo indexThree oneLt twoLt threeLt oneNeTwo oneNeThree twoNeThree sameOneTwo sameOneThree
  -- reduce the boundary to the open wires (List.range 0 ++ ow = ow) and the total to ow.length
  have oneLt' : indexOne < (processSpine ⟨List.range 0, [], 0, 0⟩ spine).openWires.length := by
    rw [Nat.zero_add] at oneLt; exact oneLt
  have twoLt' : indexTwo < (processSpine ⟨List.range 0, [], 0, 0⟩ spine).openWires.length := by
    rw [Nat.zero_add] at twoLt; exact twoLt
  have threeLt' : indexThree < (processSpine ⟨List.range 0, [], 0, 0⟩ spine).openWires.length := by
    rw [Nat.zero_add] at threeLt; exact threeLt
  -- the three reads (List.range 0 ++ ow reduces to ow definitionally)
  have readOne : natListGetAt (List.range 0 ++ (processSpine ⟨List.range 0, [], 0, 0⟩ spine).openWires) indexOne
      = natListGetAt (processSpine ⟨List.range 0, [], 0, 0⟩ spine).openWires indexOne := rfl
  have readTwo : natListGetAt (List.range 0 ++ (processSpine ⟨List.range 0, [], 0, 0⟩ spine).openWires) indexTwo
      = natListGetAt (processSpine ⟨List.range 0, [], 0, 0⟩ spine).openWires indexTwo := rfl
  have readThree : natListGetAt (List.range 0 ++ (processSpine ⟨List.range 0, [], 0, 0⟩ spine).openWires) indexThree
      = natListGetAt (processSpine ⟨List.range 0, [], 0, 0⟩ spine).openWires indexThree := rfl
  rw [readOne, readTwo] at sameOneTwo
  rw [readOne, readThree] at sameOneThree
  -- reads below nextFresh
  have nodeOneLow : natListGetAt (processSpine ⟨List.range 0, [], 0, 0⟩ spine).openWires indexOne
      < (processSpine ⟨List.range 0, [], 0, 0⟩ spine).nextFresh :=
    fresh.1 _ (natListGetAt_mem_inRange _ indexOne oneLt')
  have nodeTwoLow : natListGetAt (processSpine ⟨List.range 0, [], 0, 0⟩ spine).openWires indexTwo
      < (processSpine ⟨List.range 0, [], 0, 0⟩ spine).nextFresh :=
    fresh.1 _ (natListGetAt_mem_inRange _ indexTwo twoLt')
  have nodeThreeLow : natListGetAt (processSpine ⟨List.range 0, [], 0, 0⟩ spine).openWires indexThree
      < (processSpine ⟨List.range 0, [], 0, 0⟩ spine).nextFresh :=
    fresh.1 _ (natListGetAt_mem_inRange _ indexThree threeLt')
  -- distinct positions read distinct nodes
  have nodeOneNeTwo := distinctReadNe _ distinct indexOne indexTwo oneLt' twoLt' oneNeTwo
  have nodeOneNeThree := distinctReadNe _ distinct indexOne indexThree oneLt' threeLt' oneNeThree
  have nodeTwoNeThree := distinctReadNe _ distinct indexTwo indexThree twoLt' threeLt' twoNeThree
  -- pairwise same-component ⇒ pairwise equal roots
  exact census _ _ _ nodeOneLow nodeTwoLow nodeThreeLow nodeOneNeTwo nodeOneNeThree nodeTwoNeThree
    (of_decide_eq_true sameOneTwo) (of_decide_eq_true sameOneThree)

/-! ## The width-0 partner involution -/

/-- ★ **The width-`0` pure-cup boundary matching is a fixed-point-free involution (POSITIVITY-FREE).**  For
a pure-cup spine over the width-`0` bottom boundary, a non-fixed boundary port's partner-of-partner is the
port again — the width-0 partner involution the LOCATE snake exclusion consumes.  Landed by the carrier-free
`partnerIndexOf_isInvolution_ofBoundaryIndexCensus` at the discharged width-0 census
(`widthZeroPureCup_boundaryIndexCensus`), with NO `arcDiagram_eq_matching` bridge and NO `0 < bottomCount`
— the make-or-break of the Track B width-0 stack, positivity-free. -/
theorem matchingOfSpineListZero_partner_isInvolution
    {overallSource overallTarget : adjunctionGraph.Mode}
    (spine : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (pureCup : AllCupArity spine)
    (index : Nat)
    (inRange : index < 0 + (matchingOfSpineList 0 spine).topCount)
    (notFixed : natListGetAt (matchingOfSpineList 0 spine).partner index ≠ index) :
    natListGetAt (matchingOfSpineList 0 spine).partner
        (natListGetAt (matchingOfSpineList 0 spine).partner index)
      = index := by
  -- `matchingOfSpineList 0 spine .partner` reads as `partnerIndexOf state.links boundary total`
  have partnerListEq : (matchingOfSpineList 0 spine).partner
      = (List.range (0 + (processSpine ⟨List.range 0, [], 0, 0⟩ spine).openWires.length)).map
          (partnerIndexOf (processSpine ⟨List.range 0, [], 0, 0⟩ spine).links
            (List.range 0 ++ (processSpine ⟨List.range 0, [], 0, 0⟩ spine).openWires)
            (0 + (processSpine ⟨List.range 0, [], 0, 0⟩ spine).openWires.length)) := rfl
  have topEq : (matchingOfSpineList 0 spine).topCount
      = (processSpine ⟨List.range 0, [], 0, 0⟩ spine).openWires.length := rfl
  rw [topEq] at inRange
  -- read the two `.partner` accesses as `partnerIndexOf`
  have readAt : ∀ probe, probe < 0 + (processSpine ⟨List.range 0, [], 0, 0⟩ spine).openWires.length →
      natListGetAt (matchingOfSpineList 0 spine).partner probe
        = partnerIndexOf (processSpine ⟨List.range 0, [], 0, 0⟩ spine).links
            (List.range 0 ++ (processSpine ⟨List.range 0, [], 0, 0⟩ spine).openWires)
            (0 + (processSpine ⟨List.range 0, [], 0, 0⟩ spine).openWires.length) probe := by
    intro probe probeInRange
    rw [partnerListEq]
    exact natListGetAt_map_range _ _ probe probeInRange
  have partnerBelow : partnerIndexOf (processSpine ⟨List.range 0, [], 0, 0⟩ spine).links
      (List.range 0 ++ (processSpine ⟨List.range 0, [], 0, 0⟩ spine).openWires)
      (0 + (processSpine ⟨List.range 0, [], 0, 0⟩ spine).openWires.length) index
      < 0 + (processSpine ⟨List.range 0, [], 0, 0⟩ spine).openWires.length :=
    partnerIndexOf_below_generic _ _ _ index inRange
  have notFixed' : partnerIndexOf (processSpine ⟨List.range 0, [], 0, 0⟩ spine).links
      (List.range 0 ++ (processSpine ⟨List.range 0, [], 0, 0⟩ spine).openWires)
      (0 + (processSpine ⟨List.range 0, [], 0, 0⟩ spine).openWires.length) index ≠ index := by
    rw [← readAt index inRange]; exact notFixed
  have involuted := partnerIndexOf_isInvolution_ofBoundaryIndexCensus
    (processSpine ⟨List.range 0, [], 0, 0⟩ spine).links
    (List.range 0 ++ (processSpine ⟨List.range 0, [], 0, 0⟩ spine).openWires)
    (0 + (processSpine ⟨List.range 0, [], 0, 0⟩ spine).openWires.length)
    (widthZeroPureCup_boundaryIndexCensus spine pureCup) index inRange notFixed'
  rw [readAt index inRange, readAt _ partnerBelow]
  exact involuted

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the width-`0` pure-cup partner INVOLUTION is landed POSITIVITY-FREE (Track B b#1,
the make-or-break).**  `matchingOfSpineListZero_partner_isInvolution`: for a pure-cup spine over the
width-`0` bottom boundary, `matchingOfSpineList 0`'s partner map is a fixed-point-free involution.  Landed
by discharging the carrier-free `BoundaryIndexCensus` at the width-0 matching state
(`widthZeroPureCup_boundaryIndexCensus`) — two positivity-free pure-cup fold invariants (the node-value
root-class census `NodeRootClassSmall`, each cup adding a disjoint size-2 fresh class; and open-wire
distinctness via `stepCup_wireListDistinct`) — then applying the carrier-free involution
(`partnerIndexOf_isInvolution_ofBoundaryIndexCensus`).  NO `arcDiagram_eq_matching` bridge, NO
`0 < bottomCount`, NO arc census port.

  This replaces the DEAD `matchingOf_partner_isInvolution` (positivity-gated) at the width-0 seed.  It
  supplies the involution the LOCATE snake exclusion (`forwardChordsNotAdjacent` twin, b#5) consumes.  What
  this marker does NOT close: the location induction `matchingLocateAux` (b#5) and the sort assembly closing
  `WidthZeroPureCupDeterminacy` (c).  `convOfMapEq` and the fib-3 gate flags stay `false`.  `= true`. -/
def fxMode_hasMatchingWidthZeroInvolution : Bool := true

end FX1Poly.Polygraph
