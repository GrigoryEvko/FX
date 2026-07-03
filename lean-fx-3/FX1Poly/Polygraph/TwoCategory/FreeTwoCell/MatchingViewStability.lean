import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingBoundaryReads
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingJoinEvents

/-! # mode-3 — connectivity-view stability under caps and cups (the view-sim step arms)

The MODE3-C congruence fields need two runs related only through the CONNECTIVITY VIEW —
`openWires.length`, `loops`, and the boundary same-component relation `matchingSameComponent` on
in-range index pairs — to stay related through disciplined steps.  This file ships the CAP arm's
three transports:

  * ★ `matchingViewAgrees_stepCap` — the crux: if two states' views agree on all in-range pairs,
    the post-cap views agree on all post-cap in-range pairs.  Both post-cap reads factor through
    the SAME `capBoundaryReindex` (the reindex is state-independent), both post-cap link tables
    are unconditional joins on the two window reads, and the flat-disjunction characterization
    `isSameComponent_unionFindJoin` reduces each side to five view atoms at old in-range indices
    — where the premise closes them pointwise;
  * `matchingViewLoops_stepCap` — the loop counts stay equal: each side increments by ITS view's
    boolean at the window (`stepCap_loops_eq_addViewIncrement`), and the window indices are in
    range, so the premise equates the increments;
  * `matchingViewLength_stepCap` — the open-wire counts stay equal (additive length bookkeeping;
    the cancellation is two `Nat.succ.inj` applications — core `Nat.add_right_cancel` leaks).

The cup arm ships the fresh-separation kit, the three-zone classifier
(`stepCup_boundaryRead_zones`), the per-class join evaluations, and the nine-case transport
`matchingViewAgrees_stepCup` (plus its trivial loop and length siblings).  The bundled
view-sim structure, the per-atom dispatch, and the fold are the next bricks.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **View agreement is stable under a cap.**  Two states whose connectivity views agree on all
in-range boundary-index pairs keep agreeing after capping at the same in-range window: both
post-cap reads factor through the state-independent `capBoundaryReindex`, both post-cap link
tables are the unconditional join on the two window reads, and the flat-disjunction
characterization reduces each side to five pre-cap view atoms — all at in-range indices, where
the agreement premise closes them pointwise. -/
theorem matchingViewAgrees_stepCap (bottomCount : Nat) (stateS stateT : WireState)
    (position : Nat) (windowS : position + 2 ≤ stateS.openWires.length)
    (lengthEq : stateT.openWires.length = stateS.openWires.length)
    (forestS : isUnionFindForest stateS.links) (forestT : isUnionFindForest stateT.links)
    (viewAgrees : ∀ firstIndex secondIndex,
      firstIndex < bottomCount + stateS.openWires.length →
      secondIndex < bottomCount + stateS.openWires.length →
      matchingSameComponent bottomCount stateT firstIndex secondIndex
        = matchingSameComponent bottomCount stateS firstIndex secondIndex)
    (firstIndex secondIndex : Nat)
    (firstInRange : firstIndex < bottomCount + (stepCap stateS position).openWires.length)
    (secondInRange : secondIndex < bottomCount + (stepCap stateS position).openWires.length) :
    matchingSameComponent bottomCount (stepCap stateT position) firstIndex secondIndex
      = matchingSameComponent bottomCount (stepCap stateS position) firstIndex secondIndex := by
  have windowT : position + 2 ≤ stateT.openWires.length := by
    rw [lengthEq]
    exact windowS
  have firstOldLt := capBoundaryReindex_lt_ofNewRange bottomCount stateS position firstIndex
    windowS firstInRange
  have secondOldLt := capBoundaryReindex_lt_ofNewRange bottomCount stateS position secondIndex
    windowS secondInRange
  have legFirstLt : bottomCount + position < bottomCount + stateS.openWires.length :=
    Nat.add_lt_add_left
      (Nat.lt_of_lt_of_le
        (Nat.lt_of_lt_of_le (Nat.lt_succ_self position) (Nat.le_succ (position + 1)))
        windowS)
      bottomCount
  have legSecondLt : bottomCount + (position + 1) < bottomCount + stateS.openWires.length :=
    Nat.add_lt_add_left (Nat.lt_of_lt_of_le (Nat.lt_succ_self (position + 1)) windowS)
      bottomCount
  show isSameComponent (stepCap stateT position).links
      (natListGetAt (matchingBoundaryNodes bottomCount (stepCap stateT position)) firstIndex)
      (natListGetAt (matchingBoundaryNodes bottomCount (stepCap stateT position)) secondIndex)
    = isSameComponent (stepCap stateS position).links
      (natListGetAt (matchingBoundaryNodes bottomCount (stepCap stateS position)) firstIndex)
      (natListGetAt (matchingBoundaryNodes bottomCount (stepCap stateS position)) secondIndex)
  rw [matchingBoundaryNodes_stepCap_getAt_reindex bottomCount stateT position firstIndex
      windowT,
    matchingBoundaryNodes_stepCap_getAt_reindex bottomCount stateT position secondIndex
      windowT,
    matchingBoundaryNodes_stepCap_getAt_reindex bottomCount stateS position firstIndex
      windowS,
    matchingBoundaryNodes_stepCap_getAt_reindex bottomCount stateS position secondIndex
      windowS,
    stepCap_links_eq_unionFindJoin_boundaryReads bottomCount stateT position,
    stepCap_links_eq_unionFindJoin_boundaryReads bottomCount stateS position,
    isSameComponent_unionFindJoin stateT.links forestT,
    isSameComponent_unionFindJoin stateS.links forestS]
  have atomProbes : isSameComponent stateT.links
        (natListGetAt (matchingBoundaryNodes bottomCount stateT)
          (capBoundaryReindex bottomCount position firstIndex))
        (natListGetAt (matchingBoundaryNodes bottomCount stateT)
          (capBoundaryReindex bottomCount position secondIndex))
      = isSameComponent stateS.links
        (natListGetAt (matchingBoundaryNodes bottomCount stateS)
          (capBoundaryReindex bottomCount position firstIndex))
        (natListGetAt (matchingBoundaryNodes bottomCount stateS)
          (capBoundaryReindex bottomCount position secondIndex)) :=
    viewAgrees _ _ firstOldLt secondOldLt
  have atomLegFirst : isSameComponent stateT.links
        (natListGetAt (matchingBoundaryNodes bottomCount stateT) (bottomCount + position))
        (natListGetAt (matchingBoundaryNodes bottomCount stateT)
          (capBoundaryReindex bottomCount position firstIndex))
      = isSameComponent stateS.links
        (natListGetAt (matchingBoundaryNodes bottomCount stateS) (bottomCount + position))
        (natListGetAt (matchingBoundaryNodes bottomCount stateS)
          (capBoundaryReindex bottomCount position firstIndex)) :=
    viewAgrees _ _ legFirstLt firstOldLt
  have atomLegSecond : isSameComponent stateT.links
        (natListGetAt (matchingBoundaryNodes bottomCount stateT)
          (bottomCount + (position + 1)))
        (natListGetAt (matchingBoundaryNodes bottomCount stateT)
          (capBoundaryReindex bottomCount position secondIndex))
      = isSameComponent stateS.links
        (natListGetAt (matchingBoundaryNodes bottomCount stateS)
          (bottomCount + (position + 1)))
        (natListGetAt (matchingBoundaryNodes bottomCount stateS)
          (capBoundaryReindex bottomCount position secondIndex)) :=
    viewAgrees _ _ legSecondLt secondOldLt
  have atomCrossFirst : isSameComponent stateT.links
        (natListGetAt (matchingBoundaryNodes bottomCount stateT) (bottomCount + position))
        (natListGetAt (matchingBoundaryNodes bottomCount stateT)
          (capBoundaryReindex bottomCount position secondIndex))
      = isSameComponent stateS.links
        (natListGetAt (matchingBoundaryNodes bottomCount stateS) (bottomCount + position))
        (natListGetAt (matchingBoundaryNodes bottomCount stateS)
          (capBoundaryReindex bottomCount position secondIndex)) :=
    viewAgrees _ _ legFirstLt secondOldLt
  have atomCrossSecond : isSameComponent stateT.links
        (natListGetAt (matchingBoundaryNodes bottomCount stateT)
          (capBoundaryReindex bottomCount position firstIndex))
        (natListGetAt (matchingBoundaryNodes bottomCount stateT)
          (bottomCount + (position + 1)))
      = isSameComponent stateS.links
        (natListGetAt (matchingBoundaryNodes bottomCount stateS)
          (capBoundaryReindex bottomCount position firstIndex))
        (natListGetAt (matchingBoundaryNodes bottomCount stateS)
          (bottomCount + (position + 1))) :=
    viewAgrees _ _ firstOldLt legSecondLt
  rw [atomProbes, atomLegFirst, atomLegSecond, atomCrossFirst, atomCrossSecond]

/-- **Loop counts stay equal under a cap**: each side increments by its own view's boolean at
the window, the window indices are in range, and the view agreement equates the increments. -/
theorem matchingViewLoops_stepCap (bottomCount : Nat) (stateS stateT : WireState)
    (position : Nat) (windowS : position + 2 ≤ stateS.openWires.length)
    (loopsEq : stateT.loops = stateS.loops)
    (viewAgrees : ∀ firstIndex secondIndex,
      firstIndex < bottomCount + stateS.openWires.length →
      secondIndex < bottomCount + stateS.openWires.length →
      matchingSameComponent bottomCount stateT firstIndex secondIndex
        = matchingSameComponent bottomCount stateS firstIndex secondIndex) :
    (stepCap stateT position).loops = (stepCap stateS position).loops := by
  have legFirstLt : bottomCount + position < bottomCount + stateS.openWires.length :=
    Nat.add_lt_add_left
      (Nat.lt_of_lt_of_le
        (Nat.lt_of_lt_of_le (Nat.lt_succ_self position) (Nat.le_succ (position + 1)))
        windowS)
      bottomCount
  have legSecondLt : bottomCount + (position + 1) < bottomCount + stateS.openWires.length :=
    Nat.add_lt_add_left (Nat.lt_of_lt_of_le (Nat.lt_succ_self (position + 1)) windowS)
      bottomCount
  rw [stepCap_loops_eq_addViewIncrement bottomCount stateT position,
    stepCap_loops_eq_addViewIncrement bottomCount stateS position, loopsEq,
    viewAgrees (bottomCount + position) (bottomCount + (position + 1)) legFirstLt legSecondLt]

/-- **Open-wire counts stay equal under a cap** (additive bookkeeping; the cancellation is two
`Nat.succ.inj` applications — core `Nat.add_right_cancel` leaks `propext`). -/
theorem matchingViewLength_stepCap (stateS stateT : WireState) (position : Nat)
    (windowS : position + 2 ≤ stateS.openWires.length)
    (lengthEq : stateT.openWires.length = stateS.openWires.length) :
    (stepCap stateT position).openWires.length
      = (stepCap stateS position).openWires.length := by
  have windowT : position + 2 ≤ stateT.openWires.length := by
    rw [lengthEq]
    exact windowS
  have combined : (stepCap stateT position).openWires.length + 2
      = (stepCap stateS position).openWires.length + 2 :=
    ((stepCap_openWiresLength stateT position windowT).trans lengthEq).trans
      (stepCap_openWiresLength stateS position windowS).symm
  exact Nat.succ.inj (Nat.succ.inj combined)

/-! ## The fresh-separation kit (the cup arm's foundation)

A cup's two spliced legs are FRESH ids (`nextFresh`, `nextFresh + 1`), so at a fresh state
(`MatchingSwapStateConditions`) they are same-component-separated from EVERY pre-cup boundary
node: an old boundary node's root stays below the fresh counter
(`unionFindRootOf_lt_of_fresh`), while a fresh id is its own root
(`unionFindRootOf_eq_self_ofFresh`) — the roots cannot collide. -/

private theorem memAppendBounded (bound : Nat) : (front back : List Nat) →
    (∀ member ∈ front, member < bound) → (∀ member ∈ back, member < bound) →
    ∀ member ∈ front ++ back, member < bound
  | [], _, _, backBounded => backBounded
  | head :: tail, back, frontBounded, backBounded => fun member memberInAppend => by
      cases memberInAppend with
      | head => exact frontBounded head (List.Mem.head tail)
      | tail _ memberInRest =>
          exact memAppendBounded bound tail back
            (fun innerMember innerMem => frontBounded innerMember
              (List.Mem.tail head innerMem))
            backBounded member memberInRest

/-- **Every boundary read sits below the fresh counter** at a conditioned state: bottom nodes
are below `bottomCount ≤ nextFresh`, open wires are fresh-bounded, and the out-of-range default
`0` is covered by `nfPos`. -/
theorem matchingBoundaryNode_lt_nextFresh (bottomCount : Nat) (state : WireState)
    (conditions : MatchingSwapStateConditions bottomCount state) (index : Nat) :
    natListGetAt (matchingBoundaryNodes bottomCount state) index < state.nextFresh :=
  natListGetAt_lt state.nextFresh conditions.nfPos
    (matchingBoundaryNodes bottomCount state) index
    (show ∀ member ∈ List.range bottomCount ++ state.openWires,
        member < state.nextFresh from
      memAppendBounded state.nextFresh (List.range bottomCount) state.openWires
        (fun member memberInRange =>
          Nat.lt_of_lt_of_le (mem_range_imp_lt memberInRange) conditions.bottomLe)
        conditions.fresh.1)

/-- **A boundary read is never same-component with a fresh id**: the read's root stays below
the fresh counter while the fresh id is its own root at or above it. -/
theorem isSameComponent_boundaryRead_fresh_eq_false (bottomCount : Nat) (state : WireState)
    (conditions : MatchingSwapStateConditions bottomCount state) (index : Nat)
    (freshIdentifier : Nat) (freshAtLeast : state.nextFresh ≤ freshIdentifier) :
    isSameComponent state.links
      (natListGetAt (matchingBoundaryNodes bottomCount state) index) freshIdentifier
      = false := by
  have rootBelow : unionFindRootOf state.links
      (natListGetAt (matchingBoundaryNodes bottomCount state) index) < state.nextFresh :=
    unionFindRootOf_lt_of_fresh state.links state.nextFresh
      (fun edge edgeInLinks => (conditions.fresh.2 edge edgeInLinks).2)
      (natListGetAt (matchingBoundaryNodes bottomCount state) index)
      (matchingBoundaryNode_lt_nextFresh bottomCount state conditions index)
  show (unionFindRootOf state.links
      (natListGetAt (matchingBoundaryNodes bottomCount state) index)
    == unionFindRootOf state.links freshIdentifier) = false
  rw [unionFindRootOf_eq_self_ofFresh state.nextFresh state.links
    (fun edge edgeInLinks => (conditions.fresh.2 edge edgeInLinks).1)
    freshIdentifier freshAtLeast]
  exact decide_eq_false (fun rootsEqual => Nat.lt_irrefl freshIdentifier
    (Nat.lt_of_lt_of_le (rootsEqual ▸ rootBelow) freshAtLeast))

/-- The flipped orientation of `isSameComponent_boundaryRead_fresh_eq_false`. -/
theorem isSameComponent_fresh_boundaryRead_eq_false (bottomCount : Nat) (state : WireState)
    (conditions : MatchingSwapStateConditions bottomCount state) (index : Nat)
    (freshIdentifier : Nat) (freshAtLeast : state.nextFresh ≤ freshIdentifier) :
    isSameComponent state.links freshIdentifier
      (natListGetAt (matchingBoundaryNodes bottomCount state) index)
      = false :=
  (isSameComponent_symm state.links freshIdentifier
      (natListGetAt (matchingBoundaryNodes bottomCount state) index)).trans
    (isSameComponent_boundaryRead_fresh_eq_false bottomCount state conditions index
      freshIdentifier freshAtLeast)

/-- **A cup's two legs are never already connected** at a conditioned state (the instance of
`isSameComponent_freshPair_eq_false` at the state's own counter). -/
theorem isSameComponent_cupLegs_eq_false (bottomCount : Nat) (state : WireState)
    (conditions : MatchingSwapStateConditions bottomCount state) :
    isSameComponent state.links state.nextFresh (state.nextFresh + 1) = false :=
  isSameComponent_freshPair_eq_false state.nextFresh state.links
    (fun edge edgeInLinks => (conditions.fresh.2 edge edgeInLinks).1)
    state.nextFresh (Nat.le_refl state.nextFresh)

/-- The flipped orientation of `isSameComponent_cupLegs_eq_false`. -/
theorem isSameComponent_cupLegs_flipped_eq_false (bottomCount : Nat) (state : WireState)
    (conditions : MatchingSwapStateConditions bottomCount state) :
    isSameComponent state.links (state.nextFresh + 1) state.nextFresh = false :=
  (isSameComponent_symm state.links (state.nextFresh + 1) state.nextFresh).trans
    (isSameComponent_cupLegs_eq_false bottomCount state conditions)

/-! ## The cup zone classifier

The cup has NO total reindex (its window reads are FRESH values, not old reads), so the cup
arm's per-index classification is a three-way disjunction: an in-range post-cup boundary index
either reads an old boundary node at the SAME state-independent old index in both states, or
reads the LEFT fresh leg in both, or the RIGHT fresh leg in both. -/

/-- ★ **The cup zone classifier**: every in-range post-cup boundary index falls in one of three
state-independent zones — old (below the window or past the spliced block, factoring through
one shared old in-range index), left leg, or right leg. -/
theorem stepCup_boundaryRead_zones (bottomCount : Nat) (stateS stateT : WireState)
    (position index : Nat) (positionLeS : position ≤ stateS.openWires.length)
    (lengthEq : stateT.openWires.length = stateS.openWires.length)
    (indexInNewRange : index < bottomCount + (stepCup stateS position).openWires.length) :
    (∃ oldIndex, oldIndex < bottomCount + stateS.openWires.length
      ∧ natListGetAt (matchingBoundaryNodes bottomCount (stepCup stateS position)) index
          = natListGetAt (matchingBoundaryNodes bottomCount stateS) oldIndex
      ∧ natListGetAt (matchingBoundaryNodes bottomCount (stepCup stateT position)) index
          = natListGetAt (matchingBoundaryNodes bottomCount stateT) oldIndex)
    ∨ (natListGetAt (matchingBoundaryNodes bottomCount (stepCup stateS position)) index
          = stateS.nextFresh
        ∧ natListGetAt (matchingBoundaryNodes bottomCount (stepCup stateT position)) index
          = stateT.nextFresh)
    ∨ (natListGetAt (matchingBoundaryNodes bottomCount (stepCup stateS position)) index
          = stateS.nextFresh + 1
        ∧ natListGetAt (matchingBoundaryNodes bottomCount (stepCup stateT position)) index
          = stateT.nextFresh + 1) := by
  have positionLeT : position ≤ stateT.openWires.length := by
    rw [lengthEq]
    exact positionLeS
  cases Nat.lt_or_ge index (bottomCount + position) with
  | inl belowWindow =>
      refine Or.inl ⟨index,
        Nat.lt_of_lt_of_le belowWindow (Nat.add_le_add_left positionLeS bottomCount),
        ?_, ?_⟩
      · cases Nat.lt_or_ge index bottomCount with
        | inl belowBottom =>
            exact matchingBoundaryNodes_getAt_bottomAgrees bottomCount
              (stepCup stateS position) stateS index belowBottom
        | inr atLeastBottom =>
            obtain ⟨offset, rfl⟩ := Nat.le.dest atLeastBottom
            have offsetBelowWindow : offset < position :=
              Nat.lt_of_add_lt_add_left belowWindow
            exact matchingBoundaryNodes_stepCup_getAt_below bottomCount stateS position
              offset offsetBelowWindow (Nat.lt_of_lt_of_le offsetBelowWindow positionLeS)
      · cases Nat.lt_or_ge index bottomCount with
        | inl belowBottom =>
            exact matchingBoundaryNodes_getAt_bottomAgrees bottomCount
              (stepCup stateT position) stateT index belowBottom
        | inr atLeastBottom =>
            obtain ⟨offset, rfl⟩ := Nat.le.dest atLeastBottom
            have offsetBelowWindow : offset < position :=
              Nat.lt_of_add_lt_add_left belowWindow
            exact matchingBoundaryNodes_stepCup_getAt_below bottomCount stateT position
              offset offsetBelowWindow (Nat.lt_of_lt_of_le offsetBelowWindow positionLeT)
  | inr atOrPastWindow =>
      obtain ⟨offset, rfl⟩ := Nat.le.dest atOrPastWindow
      cases offset with
      | zero =>
          exact Or.inr (Or.inl
            ⟨matchingBoundaryNodes_stepCup_getAt_leftLeg bottomCount stateS position
              positionLeS,
             matchingBoundaryNodes_stepCup_getAt_leftLeg bottomCount stateT position
              positionLeT⟩)
      | succ offsetTail =>
          cases offsetTail with
          | zero =>
              exact Or.inr (Or.inr
                ⟨matchingBoundaryNodes_stepCup_getAt_rightLeg bottomCount stateS position
                  positionLeS,
                 matchingBoundaryNodes_stepCup_getAt_rightLeg bottomCount stateT position
                  positionLeT⟩)
          | succ pastOffset =>
              have indexForm := Nat.add_assoc bottomCount position
                (Nat.succ (Nat.succ pastOffset))
              refine Or.inl ⟨bottomCount + (position + pastOffset), ?_, ?_, ?_⟩
              · have shifted := indexInNewRange
                rw [stepCup_openWiresLength stateS position] at shifted
                have stripped : bottomCount + position + pastOffset
                    < bottomCount + stateS.openWires.length :=
                  Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ shifted)
                exact Nat.add_assoc bottomCount position pastOffset ▸ stripped
              · rw [indexForm]
                exact matchingBoundaryNodes_stepCup_getAt_pastBlock bottomCount stateS
                  position pastOffset positionLeS
              · rw [indexForm]
                exact matchingBoundaryNodes_stepCup_getAt_pastBlock bottomCount stateT
                  position pastOffset positionLeT

/-! ## The per-class join evaluations at a cup

The cup joins the two FRESH legs, so `isSameComponent` after the join evaluates per probe
class: two old boundary reads keep their pre-cup connectivity (the fresh atoms in the
flat-disjunction characterization all die), an old read is separated from either leg, and the
two legs are connected to each other (and to themselves). -/

/-- **Two old boundary reads keep their pre-cup connectivity through the cup's join**: all four
fresh atoms of the flat-disjunction characterization are separations. -/
theorem stepCup_isSameComponent_boundaryReads (bottomCount : Nat) (state : WireState)
    (conditions : MatchingSwapStateConditions bottomCount state) (indexA indexB : Nat) :
    isSameComponent (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
        (natListGetAt (matchingBoundaryNodes bottomCount state) indexA)
        (natListGetAt (matchingBoundaryNodes bottomCount state) indexB)
      = isSameComponent state.links
        (natListGetAt (matchingBoundaryNodes bottomCount state) indexA)
        (natListGetAt (matchingBoundaryNodes bottomCount state) indexB) := by
  rw [isSameComponent_unionFindJoin state.links conditions.forest,
    isSameComponent_fresh_boundaryRead_eq_false bottomCount state conditions indexA
      state.nextFresh (Nat.le_refl state.nextFresh),
    isSameComponent_fresh_boundaryRead_eq_false bottomCount state conditions indexB
      (state.nextFresh + 1) (Nat.le_succ state.nextFresh),
    isSameComponent_fresh_boundaryRead_eq_false bottomCount state conditions indexB
      state.nextFresh (Nat.le_refl state.nextFresh),
    isSameComponent_boundaryRead_fresh_eq_false bottomCount state conditions indexA
      (state.nextFresh + 1) (Nat.le_succ state.nextFresh)]
  cases isSameComponent state.links
      (natListGetAt (matchingBoundaryNodes bottomCount state) indexA)
      (natListGetAt (matchingBoundaryNodes bottomCount state) indexB) with
  | false => rfl
  | true => rfl

/-- An old boundary read is not connected to the LEFT leg through the cup's join. -/
theorem stepCup_isSameComponent_boundaryRead_leftLeg (bottomCount : Nat) (state : WireState)
    (conditions : MatchingSwapStateConditions bottomCount state) (index : Nat) :
    isSameComponent (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
        (natListGetAt (matchingBoundaryNodes bottomCount state) index) state.nextFresh
      = false := by
  rw [isSameComponent_unionFindJoin state.links conditions.forest,
    isSameComponent_boundaryRead_fresh_eq_false bottomCount state conditions index
      state.nextFresh (Nat.le_refl state.nextFresh),
    isSameComponent_fresh_boundaryRead_eq_false bottomCount state conditions index
      state.nextFresh (Nat.le_refl state.nextFresh),
    isSameComponent_cupLegs_flipped_eq_false bottomCount state conditions,
    isSameComponent_self state.links state.nextFresh,
    isSameComponent_boundaryRead_fresh_eq_false bottomCount state conditions index
      (state.nextFresh + 1) (Nat.le_succ state.nextFresh)]
  rfl

/-- An old boundary read is not connected to the RIGHT leg through the cup's join. -/
theorem stepCup_isSameComponent_boundaryRead_rightLeg (bottomCount : Nat) (state : WireState)
    (conditions : MatchingSwapStateConditions bottomCount state) (index : Nat) :
    isSameComponent (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
        (natListGetAt (matchingBoundaryNodes bottomCount state) index) (state.nextFresh + 1)
      = false := by
  rw [isSameComponent_unionFindJoin state.links conditions.forest,
    isSameComponent_boundaryRead_fresh_eq_false bottomCount state conditions index
      (state.nextFresh + 1) (Nat.le_succ state.nextFresh),
    isSameComponent_fresh_boundaryRead_eq_false bottomCount state conditions index
      state.nextFresh (Nat.le_refl state.nextFresh),
    isSameComponent_self state.links (state.nextFresh + 1),
    isSameComponent_cupLegs_eq_false bottomCount state conditions]
  rfl

/-- The LEFT leg is not connected to an old boundary read through the cup's join. -/
theorem stepCup_isSameComponent_leftLeg_boundaryRead (bottomCount : Nat) (state : WireState)
    (conditions : MatchingSwapStateConditions bottomCount state) (index : Nat) :
    isSameComponent (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
        state.nextFresh (natListGetAt (matchingBoundaryNodes bottomCount state) index)
      = false := by
  rw [isSameComponent_unionFindJoin state.links conditions.forest,
    isSameComponent_fresh_boundaryRead_eq_false bottomCount state conditions index
      state.nextFresh (Nat.le_refl state.nextFresh),
    isSameComponent_self state.links state.nextFresh,
    isSameComponent_fresh_boundaryRead_eq_false bottomCount state conditions index
      (state.nextFresh + 1) (Nat.le_succ state.nextFresh),
    isSameComponent_cupLegs_eq_false bottomCount state conditions]
  rfl

/-- The RIGHT leg is not connected to an old boundary read through the cup's join. -/
theorem stepCup_isSameComponent_rightLeg_boundaryRead (bottomCount : Nat) (state : WireState)
    (conditions : MatchingSwapStateConditions bottomCount state) (index : Nat) :
    isSameComponent (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
        (state.nextFresh + 1) (natListGetAt (matchingBoundaryNodes bottomCount state) index)
      = false := by
  rw [isSameComponent_unionFindJoin state.links conditions.forest,
    isSameComponent_fresh_boundaryRead_eq_false bottomCount state conditions index
      (state.nextFresh + 1) (Nat.le_succ state.nextFresh),
    isSameComponent_cupLegs_eq_false bottomCount state conditions,
    isSameComponent_fresh_boundaryRead_eq_false bottomCount state conditions index
      state.nextFresh (Nat.le_refl state.nextFresh),
    isSameComponent_self state.links (state.nextFresh + 1)]
  rfl

/-- The two legs ARE connected by the cup's join (left-to-right orientation). -/
theorem stepCup_isSameComponent_leftLeg_rightLeg (bottomCount : Nat) (state : WireState)
    (conditions : MatchingSwapStateConditions bottomCount state) :
    isSameComponent (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
        state.nextFresh (state.nextFresh + 1)
      = true := by
  rw [isSameComponent_unionFindJoin state.links conditions.forest,
    isSameComponent_cupLegs_eq_false bottomCount state conditions,
    isSameComponent_self state.links state.nextFresh,
    isSameComponent_self state.links (state.nextFresh + 1)]
  rfl

/-- The two legs ARE connected by the cup's join (right-to-left orientation). -/
theorem stepCup_isSameComponent_rightLeg_leftLeg (bottomCount : Nat) (state : WireState)
    (conditions : MatchingSwapStateConditions bottomCount state) :
    isSameComponent (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
        (state.nextFresh + 1) state.nextFresh
      = true := by
  rw [isSameComponent_unionFindJoin state.links conditions.forest,
    isSameComponent_cupLegs_flipped_eq_false bottomCount state conditions,
    isSameComponent_cupLegs_eq_false bottomCount state conditions,
    isSameComponent_self state.links state.nextFresh,
    isSameComponent_self state.links (state.nextFresh + 1)]
  rfl

/-! ## The cup arm of the view stability -/

/-- ★ **View agreement is stable under a cup.**  Two conditioned states whose connectivity
views agree on all in-range boundary-index pairs keep agreeing after cupping at the same
in-window position: the three-zone classifier splits each probe into a shared old read or a
fresh leg, and the per-class join evaluations close all nine zone pairs — eight to closed
booleans, the old/old pair to the pre-cup view atom, where the agreement premise closes it. -/
theorem matchingViewAgrees_stepCup (bottomCount : Nat) (stateS stateT : WireState)
    (position : Nat) (positionLeS : position ≤ stateS.openWires.length)
    (lengthEq : stateT.openWires.length = stateS.openWires.length)
    (conditionsS : MatchingSwapStateConditions bottomCount stateS)
    (conditionsT : MatchingSwapStateConditions bottomCount stateT)
    (viewAgrees : ∀ firstIndex secondIndex,
      firstIndex < bottomCount + stateS.openWires.length →
      secondIndex < bottomCount + stateS.openWires.length →
      matchingSameComponent bottomCount stateT firstIndex secondIndex
        = matchingSameComponent bottomCount stateS firstIndex secondIndex)
    (firstIndex secondIndex : Nat)
    (firstInRange : firstIndex < bottomCount + (stepCup stateS position).openWires.length)
    (secondInRange : secondIndex < bottomCount + (stepCup stateS position).openWires.length) :
    matchingSameComponent bottomCount (stepCup stateT position) firstIndex secondIndex
      = matchingSameComponent bottomCount (stepCup stateS position) firstIndex secondIndex := by
  have firstZones := stepCup_boundaryRead_zones bottomCount stateS stateT position firstIndex
    positionLeS lengthEq firstInRange
  have secondZones := stepCup_boundaryRead_zones bottomCount stateS stateT position secondIndex
    positionLeS lengthEq secondInRange
  show isSameComponent (stepCup stateT position).links
      (natListGetAt (matchingBoundaryNodes bottomCount (stepCup stateT position)) firstIndex)
      (natListGetAt (matchingBoundaryNodes bottomCount (stepCup stateT position)) secondIndex)
    = isSameComponent (stepCup stateS position).links
      (natListGetAt (matchingBoundaryNodes bottomCount (stepCup stateS position)) firstIndex)
      (natListGetAt (matchingBoundaryNodes bottomCount (stepCup stateS position)) secondIndex)
  rw [stepCup_links stateT position, stepCup_links stateS position]
  cases firstZones with
  | inl firstOld =>
      obtain ⟨firstOldIndex, firstOldLt, firstReadS, firstReadT⟩ := firstOld
      rw [firstReadT, firstReadS]
      cases secondZones with
      | inl secondOld =>
          obtain ⟨secondOldIndex, secondOldLt, secondReadS, secondReadT⟩ := secondOld
          rw [secondReadT, secondReadS,
            stepCup_isSameComponent_boundaryReads bottomCount stateT conditionsT
              firstOldIndex secondOldIndex,
            stepCup_isSameComponent_boundaryReads bottomCount stateS conditionsS
              firstOldIndex secondOldIndex]
          exact viewAgrees firstOldIndex secondOldIndex firstOldLt secondOldLt
      | inr secondLegs =>
          cases secondLegs with
          | inl secondLeft =>
              obtain ⟨secondLeftS, secondLeftT⟩ := secondLeft
              rw [secondLeftT, secondLeftS,
                stepCup_isSameComponent_boundaryRead_leftLeg bottomCount stateT conditionsT
                  firstOldIndex,
                stepCup_isSameComponent_boundaryRead_leftLeg bottomCount stateS conditionsS
                  firstOldIndex]
          | inr secondRight =>
              obtain ⟨secondRightS, secondRightT⟩ := secondRight
              rw [secondRightT, secondRightS,
                stepCup_isSameComponent_boundaryRead_rightLeg bottomCount stateT conditionsT
                  firstOldIndex,
                stepCup_isSameComponent_boundaryRead_rightLeg bottomCount stateS conditionsS
                  firstOldIndex]
  | inr firstLegs =>
      cases firstLegs with
      | inl firstLeft =>
          obtain ⟨firstLeftS, firstLeftT⟩ := firstLeft
          rw [firstLeftT, firstLeftS]
          cases secondZones with
          | inl secondOld =>
              obtain ⟨secondOldIndex, secondOldLt, secondReadS, secondReadT⟩ := secondOld
              rw [secondReadT, secondReadS,
                stepCup_isSameComponent_leftLeg_boundaryRead bottomCount stateT conditionsT
                  secondOldIndex,
                stepCup_isSameComponent_leftLeg_boundaryRead bottomCount stateS conditionsS
                  secondOldIndex]
          | inr secondLegs =>
              cases secondLegs with
              | inl secondLeft =>
                  obtain ⟨secondLeftS, secondLeftT⟩ := secondLeft
                  rw [secondLeftT, secondLeftS,
                    isSameComponent_self
                      (unionFindJoin stateT.links stateT.nextFresh (stateT.nextFresh + 1))
                      stateT.nextFresh,
                    isSameComponent_self
                      (unionFindJoin stateS.links stateS.nextFresh (stateS.nextFresh + 1))
                      stateS.nextFresh]
              | inr secondRight =>
                  obtain ⟨secondRightS, secondRightT⟩ := secondRight
                  rw [secondRightT, secondRightS,
                    stepCup_isSameComponent_leftLeg_rightLeg bottomCount stateT conditionsT,
                    stepCup_isSameComponent_leftLeg_rightLeg bottomCount stateS conditionsS]
      | inr firstRight =>
          obtain ⟨firstRightS, firstRightT⟩ := firstRight
          rw [firstRightT, firstRightS]
          cases secondZones with
          | inl secondOld =>
              obtain ⟨secondOldIndex, secondOldLt, secondReadS, secondReadT⟩ := secondOld
              rw [secondReadT, secondReadS,
                stepCup_isSameComponent_rightLeg_boundaryRead bottomCount stateT conditionsT
                  secondOldIndex,
                stepCup_isSameComponent_rightLeg_boundaryRead bottomCount stateS conditionsS
                  secondOldIndex]
          | inr secondLegs =>
              cases secondLegs with
              | inl secondLeft =>
                  obtain ⟨secondLeftS, secondLeftT⟩ := secondLeft
                  rw [secondLeftT, secondLeftS,
                    stepCup_isSameComponent_rightLeg_leftLeg bottomCount stateT conditionsT,
                    stepCup_isSameComponent_rightLeg_leftLeg bottomCount stateS conditionsS]
              | inr secondRight =>
                  obtain ⟨secondRightS, secondRightT⟩ := secondRight
                  rw [secondRightT, secondRightS,
                    isSameComponent_self
                      (unionFindJoin stateT.links stateT.nextFresh (stateT.nextFresh + 1))
                      (stateT.nextFresh + 1),
                    isSameComponent_self
                      (unionFindJoin stateS.links stateS.nextFresh (stateS.nextFresh + 1))
                      (stateS.nextFresh + 1)]

/-- **Loop counts stay equal under a cup** — a cup never closes a loop. -/
theorem matchingViewLoops_stepCup (stateS stateT : WireState)
    (loopsEq : stateT.loops = stateS.loops) (position : Nat) :
    (stepCup stateT position).loops = (stepCup stateS position).loops := loopsEq

/-- **Open-wire counts stay equal under a cup** — both sides grow by exactly two. -/
theorem matchingViewLength_stepCup (stateS stateT : WireState) (position : Nat)
    (lengthEq : stateT.openWires.length = stateS.openWires.length) :
    (stepCup stateT position).openWires.length
      = (stepCup stateS position).openWires.length := by
  rw [stepCup_openWiresLength stateT position, stepCup_openWiresLength stateS position,
    lengthEq]

/-! ## Honesty markers -/

/-- **Honesty marker — the connectivity view's CAP stability + the fresh-separation kit are
SHIPPED.**  Cap arm: in-range view agreement is preserved (`matchingViewAgrees_stepCap`, via
the state-independent reindex factoring + the unconditional join legs + the flat-disjunction
characterization reducing to five in-range pre-cap atoms), loop counts stay equal (the
increment IS the view boolean at the window), and open-wire counts stay equal.  Cup
foundation: every boundary read sits below the fresh counter
(`matchingBoundaryNode_lt_nextFresh`) and is same-component-separated from every fresh id in
both orientations.  The cup arm's own transport is `fxMode_hasMatchingViewCupStability`.
`= true`. -/
def fxMode_hasMatchingViewCapStability : Bool := true

/-- **Honesty marker — the connectivity view's CUP stability is SHIPPED.**  The three-zone
classifier (`stepCup_boundaryRead_zones`) splits every in-range post-cup boundary index into a
shared old read, the left fresh leg, or the right fresh leg; the per-class join evaluations
close all nine zone pairs — eight to closed booleans via the fresh-separation kit, the old/old
pair to the pre-cup view atom, where the agreement premise closes it
(`matchingViewAgrees_stepCup`).  Loop counts are untouched by a cup and open-wire counts grow
by two on both sides.  NOT yet covered: the bundled view-sim structure over
`MatchingSwapStateConditions` + the per-atom dispatch and fold over a disciplined atom list,
and the run-composition law behind the `MatchingSaturatedCongruence` fields — the remaining
MODE3-C bricks.  `= true`. -/
def fxMode_hasMatchingViewCupStability : Bool := true

end FX1Poly.Polygraph
