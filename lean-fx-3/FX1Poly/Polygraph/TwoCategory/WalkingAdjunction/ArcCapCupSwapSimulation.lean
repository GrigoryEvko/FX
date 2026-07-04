import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupCapSwapSimulation

/-! # ArcCapCupSwapSimulation — the CAP x CUP two-step core simulation (ARC-2b brick iii-1d-beta3)

The mirror mixed case: the low atom is a cap, the high atom a cup.  Order S fires the cap at
`positionLow` then the cup at `gap + positionLow` (the cap consumed two wires, so the cup's
window slid DOWN by two); order T fires the cup first at `gap + 2 + positionLow` then the cap
at `positionLow`.  The reconciling renaming is the fresh-block transposition at widths `1, 3`
(the cap allocates one identifier, the cup three).

Here the wire-value agreement is even simpler than in the cup-cap case: order T's cap reads
strictly BELOW the cup's splice point, so the iii-1a below-locality law collapses its reads to
the original wires with no index arithmetic at all.  Both orders again build the SAME merged
component `unionFindJoin links leftRead rightRead` at the low window, and every field reduces
to the cup atlas (alpha1), the cap atlas (beta1), and the shared merge:

  * S-side roots: the cap fires FIRST, so the cap atlas applies at the original state and the
    cup's triple sits directly on top (the alpha1 legs apply verbatim to the final state);
  * T-side roots: the cup fires first, so old nodes and the cap's event thread through the
    cup's joins exactly as in the cup-cap case's order S;
  * `openMap` is the iii-1a remove-below/insert-above commutation; `loopsEq` is the
    same-component test's stability through the cup.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- `List.map` on a two-element literal, exposed as a rewrite (definitional). -/
private theorem mapPairValues (rename : Nat → Nat) (firstValue secondValue : Nat) :
    List.map rename [firstValue, secondValue] = [rename firstValue, rename secondValue] := rfl

/-- **The order-T links exposed over the ORIGINAL reads.**  The cap's join-of-join over the
post-cup state; the cap reads strictly below the cup's splice point, so below-locality
collapses both reads. -/
theorem capCupSwap_linksT (state : ArcWireState) (gap positionLow : Nat)
    (positionBound : gap + positionLow + 2 ≤ state.openWires.length) :
    (stepCapArc (stepCupArc state (gap + 2 + positionLow)) positionLow).links
      = unionFindJoin
          (unionFindJoin (stepCupArc state (gap + 2 + positionLow)).links
            (natListGetAt state.openWires positionLow)
            (natListGetAt state.openWires (positionLow + 1)))
          (state.nextFresh + 3)
          (natListGetAt state.openWires positionLow) := by
  have windowWithinLength : positionLow + 2 ≤ state.openWires.length :=
    Nat.le_trans (Nat.le_add_left (positionLow + 2) gap)
      (by rw [← Nat.add_assoc]; exact positionBound)
  have belowLength : positionLow < state.openWires.length :=
    Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide)) windowWithinLength
  have succBelowLength : positionLow + 1 < state.openWires.length :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by decide) positionLow) windowWithinLength
  have gapTwoPos : 0 < gap + 2 := Nat.zero_lt_succ (gap + 1)
  have oneLtGapTwo : 1 < gap + 2 :=
    Nat.lt_of_lt_of_le (by decide) (Nat.le_add_left 2 gap)
  have belowInsert : positionLow < gap + 2 + positionLow := by
    rw [Nat.add_comm (gap + 2) positionLow]
    exact Nat.lt_add_of_pos_right gapTwoPos
  have succBelowInsert : positionLow + 1 < gap + 2 + positionLow := by
    rw [Nat.add_comm (gap + 2) positionLow]
    exact Nat.add_lt_add_left oneLtGapTwo positionLow
  show unionFindJoin
      (unionFindJoin (stepCupArc state (gap + 2 + positionLow)).links
        (natListGetAt (natListInsertAt state.openWires (gap + 2 + positionLow)
          [state.nextFresh, state.nextFresh + 1]) positionLow)
        (natListGetAt (natListInsertAt state.openWires (gap + 2 + positionLow)
          [state.nextFresh, state.nextFresh + 1]) (positionLow + 1)))
      (state.nextFresh + 3)
      (natListGetAt (natListInsertAt state.openWires (gap + 2 + positionLow)
        [state.nextFresh, state.nextFresh + 1]) positionLow)
    = unionFindJoin
        (unionFindJoin (stepCupArc state (gap + 2 + positionLow)).links
          (natListGetAt state.openWires positionLow)
          (natListGetAt state.openWires (positionLow + 1)))
        (state.nextFresh + 3)
        (natListGetAt state.openWires positionLow)
  rw [natListGetAt_natListInsertAt_below state.openWires (gap + 2 + positionLow)
      [state.nextFresh, state.nextFresh + 1] positionLow belowInsert belowLength,
    natListGetAt_natListInsertAt_below state.openWires (gap + 2 + positionLow)
      [state.nextFresh, state.nextFresh + 1] (positionLow + 1) succBelowInsert
      succBelowLength]

/-! ## Order-T roots — through the cup, then the cap -/

/-- **Old nodes keep their merged roots through order T.**  The cup leaves old roots alone, so
the T-side merge behaves exactly like the shared merge; the cap's event join is invisible to
old-rooted nodes. -/
theorem capCupSwapT_root_old (state : ArcWireState)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (nfPos : 0 < state.nextFresh) (gap positionLow : Nat)
    (positionBound : gap + positionLow + 2 ≤ state.openWires.length)
    (node : Nat) (nodeBelow : node < state.nextFresh) :
    unionFindRootOf
        (stepCapArc (stepCupArc state (gap + 2 + positionLow)) positionLow).links node
      = unionFindRootOf
          (unionFindJoin state.links (natListGetAt state.openWires positionLow)
            (natListGetAt state.openWires (positionLow + 1)))
          node := by
  have forestCupMid :
      isUnionFindForest (stepCupArc state (gap + 2 + positionLow)).links :=
    isUnionFindForest_stepCupArc state (gap + 2 + positionLow) forest
  have freshCupMid : ArcStateFresh (stepCupArc state (gap + 2 + positionLow)) :=
    stepCupArc_arcStateFresh state (gap + 2 + positionLow) fresh
  have linkParentsBelow : ∀ edge ∈ state.links, edge.2 < state.nextFresh :=
    fun edge edgeInLinks => (fresh.2.1 edge edgeInLinks).2
  have rootLeftBelow :
      unionFindRootOf state.links (natListGetAt state.openWires positionLow)
        < state.nextFresh :=
    unionFindRootOf_lt_of_fresh state.links state.nextFresh linkParentsBelow _
      (natListGetAt_lt state.nextFresh nfPos state.openWires positionLow fresh.1)
  have rootRightBelow :
      unionFindRootOf state.links (natListGetAt state.openWires (positionLow + 1))
        < state.nextFresh :=
    unionFindRootOf_lt_of_fresh state.links state.nextFresh linkParentsBelow _
      (natListGetAt_lt state.nextFresh nfPos state.openWires (positionLow + 1) fresh.1)
  have rootNodeBelow : unionFindRootOf state.links node < state.nextFresh :=
    unionFindRootOf_lt_of_fresh state.links state.nextFresh linkParentsBelow node nodeBelow
  have collapseLeft :
      unionFindRootOf (stepCupArc state (gap + 2 + positionLow)).links
          (natListGetAt state.openWires positionLow)
        = unionFindRootOf state.links (natListGetAt state.openWires positionLow) :=
    unionFindRootOf_stepCupArc_old state (gap + 2 + positionLow) fresh forest _ rootLeftBelow
  have collapseRight :
      unionFindRootOf (stepCupArc state (gap + 2 + positionLow)).links
          (natListGetAt state.openWires (positionLow + 1))
        = unionFindRootOf state.links (natListGetAt state.openWires (positionLow + 1)) :=
    unionFindRootOf_stepCupArc_old state (gap + 2 + positionLow) fresh forest _
      rootRightBelow
  have collapseNode :
      unionFindRootOf (stepCupArc state (gap + 2 + positionLow)).links node
        = unionFindRootOf state.links node :=
    unionFindRootOf_stepCupArc_old state (gap + 2 + positionLow) fresh forest node
      rootNodeBelow
  have forestMergedT :
      isUnionFindForest (unionFindJoin (stepCupArc state (gap + 2 + positionLow)).links
        (natListGetAt state.openWires positionLow)
        (natListGetAt state.openWires (positionLow + 1))) :=
    isUnionFindForest_unionFindJoin _ _ _ forestCupMid
  have mergedTChildrenBelow :
      ∀ edge ∈ unionFindJoin (stepCupArc state (gap + 2 + positionLow)).links
          (natListGetAt state.openWires positionLow)
          (natListGetAt state.openWires (positionLow + 1)),
        edge.1 < state.nextFresh + 3 :=
    fun edge edgeInJoin =>
      (unionFindJoin_all_lt (state.nextFresh + 3)
        (stepCupArc state (gap + 2 + positionLow)).links _ _
        freshCupMid.2.1
        (by
          rw [collapseLeft]
          exact Nat.lt_trans rootLeftBelow (Nat.lt_add_of_pos_right (by decide)))
        (by
          rw [collapseRight]
          exact Nat.lt_trans rootRightBelow (Nat.lt_add_of_pos_right (by decide)))
        edge edgeInJoin).1
  have rootMergedTEvent :
      unionFindRootOf
          (unionFindJoin (stepCupArc state (gap + 2 + positionLow)).links
            (natListGetAt state.openWires positionLow)
            (natListGetAt state.openWires (positionLow + 1)))
          (state.nextFresh + 3)
        = state.nextFresh + 3 :=
    unionFindRootOf_of_parentless _ _
      (unionFindParent_none_of_lt (state.nextFresh + 3) _ mergedTChildrenBelow
        (state.nextFresh + 3) (Nat.le_refl _))
  have bridgeMerged :
      unionFindRootOf
          (unionFindJoin (stepCupArc state (gap + 2 + positionLow)).links
            (natListGetAt state.openWires positionLow)
            (natListGetAt state.openWires (positionLow + 1)))
          node
        = unionFindRootOf
            (unionFindJoin state.links (natListGetAt state.openWires positionLow)
              (natListGetAt state.openWires (positionLow + 1)))
            node := by
    rw [unionFindRootOf_unionFindJoin (stepCupArc state (gap + 2 + positionLow)).links
        (natListGetAt state.openWires positionLow)
        (natListGetAt state.openWires (positionLow + 1)) node forestCupMid,
      unionFindRootOf_unionFindJoin state.links
        (natListGetAt state.openWires positionLow)
        (natListGetAt state.openWires (positionLow + 1)) node forest,
      collapseLeft, collapseRight, collapseNode]
  have mergedRootBelow :
      unionFindRootOf
          (unionFindJoin state.links (natListGetAt state.openWires positionLow)
            (natListGetAt state.openWires (positionLow + 1)))
          node
        < state.nextFresh :=
    capMerge_root_below state positionLow fresh nfPos node nodeBelow
  have mergedRootBelowEvent :
      unionFindRootOf
          (unionFindJoin state.links (natListGetAt state.openWires positionLow)
            (natListGetAt state.openWires (positionLow + 1)))
          node
        < state.nextFresh + 3 :=
    Nat.lt_trans mergedRootBelow (Nat.lt_add_of_pos_right (by decide))
  have guardFresh :
      ¬ (state.nextFresh + 3
          == unionFindRootOf
              (unionFindJoin state.links (natListGetAt state.openWires positionLow)
                (natListGetAt state.openWires (positionLow + 1)))
              node) = true :=
    fun isTrue => Bool.noConfusion (beq_false_of_lt mergedRootBelowEvent ▸ isTrue)
  rw [capCupSwap_linksT state gap positionLow positionBound,
    unionFindRootOf_unionFindJoin
      (unionFindJoin (stepCupArc state (gap + 2 + positionLow)).links
        (natListGetAt state.openWires positionLow)
        (natListGetAt state.openWires (positionLow + 1)))
      (state.nextFresh + 3) (natListGetAt state.openWires positionLow) node forestMergedT,
    rootMergedTEvent, bridgeMerged, if_neg guardFresh]

/-- **The cup's fresh triple still roots at `nextFresh + 1` through order T's cap** — the
cap's merge joins two OLD-rooted wires, so the triple's component is untouched. -/
theorem capCupSwapT_root_triple (state : ArcWireState)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (nfPos : 0 < state.nextFresh) (gap positionLow : Nat)
    (positionBound : gap + positionLow + 2 ≤ state.openWires.length)
    (tripleNode : Nat)
    (cupRootAtRightLeg :
      unionFindRootOf (stepCupArc state (gap + 2 + positionLow)).links tripleNode
        = state.nextFresh + 1) :
    unionFindRootOf
        (stepCapArc (stepCupArc state (gap + 2 + positionLow)) positionLow).links
        tripleNode
      = state.nextFresh + 1 := by
  have forestCupMid :
      isUnionFindForest (stepCupArc state (gap + 2 + positionLow)).links :=
    isUnionFindForest_stepCupArc state (gap + 2 + positionLow) forest
  have freshCupMid : ArcStateFresh (stepCupArc state (gap + 2 + positionLow)) :=
    stepCupArc_arcStateFresh state (gap + 2 + positionLow) fresh
  have linkParentsBelow : ∀ edge ∈ state.links, edge.2 < state.nextFresh :=
    fun edge edgeInLinks => (fresh.2.1 edge edgeInLinks).2
  have rootLeftBelow :
      unionFindRootOf state.links (natListGetAt state.openWires positionLow)
        < state.nextFresh :=
    unionFindRootOf_lt_of_fresh state.links state.nextFresh linkParentsBelow _
      (natListGetAt_lt state.nextFresh nfPos state.openWires positionLow fresh.1)
  have rootRightBelow :
      unionFindRootOf state.links (natListGetAt state.openWires (positionLow + 1))
        < state.nextFresh :=
    unionFindRootOf_lt_of_fresh state.links state.nextFresh linkParentsBelow _
      (natListGetAt_lt state.nextFresh nfPos state.openWires (positionLow + 1) fresh.1)
  have collapseLeft :
      unionFindRootOf (stepCupArc state (gap + 2 + positionLow)).links
          (natListGetAt state.openWires positionLow)
        = unionFindRootOf state.links (natListGetAt state.openWires positionLow) :=
    unionFindRootOf_stepCupArc_old state (gap + 2 + positionLow) fresh forest _ rootLeftBelow
  have collapseRight :
      unionFindRootOf (stepCupArc state (gap + 2 + positionLow)).links
          (natListGetAt state.openWires (positionLow + 1))
        = unionFindRootOf state.links (natListGetAt state.openWires (positionLow + 1)) :=
    unionFindRootOf_stepCupArc_old state (gap + 2 + positionLow) fresh forest _
      rootRightBelow
  have forestMergedT :
      isUnionFindForest (unionFindJoin (stepCupArc state (gap + 2 + positionLow)).links
        (natListGetAt state.openWires positionLow)
        (natListGetAt state.openWires (positionLow + 1))) :=
    isUnionFindForest_unionFindJoin _ _ _ forestCupMid
  have mergedTChildrenBelow :
      ∀ edge ∈ unionFindJoin (stepCupArc state (gap + 2 + positionLow)).links
          (natListGetAt state.openWires positionLow)
          (natListGetAt state.openWires (positionLow + 1)),
        edge.1 < state.nextFresh + 3 :=
    fun edge edgeInJoin =>
      (unionFindJoin_all_lt (state.nextFresh + 3)
        (stepCupArc state (gap + 2 + positionLow)).links _ _
        freshCupMid.2.1
        (by
          rw [collapseLeft]
          exact Nat.lt_trans rootLeftBelow (Nat.lt_add_of_pos_right (by decide)))
        (by
          rw [collapseRight]
          exact Nat.lt_trans rootRightBelow (Nat.lt_add_of_pos_right (by decide)))
        edge edgeInJoin).1
  have rootMergedTEvent :
      unionFindRootOf
          (unionFindJoin (stepCupArc state (gap + 2 + positionLow)).links
            (natListGetAt state.openWires positionLow)
            (natListGetAt state.openWires (positionLow + 1)))
          (state.nextFresh + 3)
        = state.nextFresh + 3 :=
    unionFindRootOf_of_parentless _ _
      (unionFindParent_none_of_lt (state.nextFresh + 3) _ mergedTChildrenBelow
        (state.nextFresh + 3) (Nat.le_refl _))
  have rootMergedTTriple :
      unionFindRootOf
          (unionFindJoin (stepCupArc state (gap + 2 + positionLow)).links
            (natListGetAt state.openWires positionLow)
            (natListGetAt state.openWires (positionLow + 1)))
          tripleNode
        = state.nextFresh + 1 := by
    have rootLeftBelowRightLeg :
        unionFindRootOf state.links (natListGetAt state.openWires positionLow)
          < state.nextFresh + 1 :=
      Nat.lt_trans rootLeftBelow (Nat.lt_add_of_pos_right (by decide))
    have guardLeft :
        ¬ (unionFindRootOf state.links (natListGetAt state.openWires positionLow)
            == state.nextFresh + 1) = true :=
      fun isTrue =>
        Bool.noConfusion (beq_false_of_lt_left rootLeftBelowRightLeg ▸ isTrue)
    rw [unionFindRootOf_unionFindJoin (stepCupArc state (gap + 2 + positionLow)).links
        (natListGetAt state.openWires positionLow)
        (natListGetAt state.openWires (positionLow + 1)) tripleNode forestCupMid,
      collapseLeft, cupRootAtRightLeg, if_neg guardLeft]
  have oneBelowEventNode : state.nextFresh + 1 < state.nextFresh + 3 :=
    Nat.add_lt_add_left (by decide) state.nextFresh
  have guardOuter : ¬ (state.nextFresh + 3 == state.nextFresh + 1) = true :=
    fun isTrue => Bool.noConfusion (beq_false_of_lt oneBelowEventNode ▸ isTrue)
  rw [capCupSwap_linksT state gap positionLow positionBound,
    unionFindRootOf_unionFindJoin
      (unionFindJoin (stepCupArc state (gap + 2 + positionLow)).links
        (natListGetAt state.openWires positionLow)
        (natListGetAt state.openWires (positionLow + 1)))
      (state.nextFresh + 3) (natListGetAt state.openWires positionLow) tripleNode
      forestMergedT,
    rootMergedTEvent, rootMergedTTriple, if_neg guardOuter]

/-- **Order T's cap event roots at the right wire's old root** — through the cup the right
wire's root is unchanged, and the cap hangs its event under the merged representative. -/
theorem capCupSwapT_root_capEvent (state : ArcWireState)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (nfPos : 0 < state.nextFresh) (gap positionLow : Nat)
    (positionBound : gap + positionLow + 2 ≤ state.openWires.length) :
    unionFindRootOf
        (stepCapArc (stepCupArc state (gap + 2 + positionLow)) positionLow).links
        (state.nextFresh + 3)
      = unionFindRootOf state.links (natListGetAt state.openWires (positionLow + 1)) := by
  have forestCupMid :
      isUnionFindForest (stepCupArc state (gap + 2 + positionLow)).links :=
    isUnionFindForest_stepCupArc state (gap + 2 + positionLow) forest
  have linkParentsBelow : ∀ edge ∈ state.links, edge.2 < state.nextFresh :=
    fun edge edgeInLinks => (fresh.2.1 edge edgeInLinks).2
  have rootLeftBelow :
      unionFindRootOf state.links (natListGetAt state.openWires positionLow)
        < state.nextFresh :=
    unionFindRootOf_lt_of_fresh state.links state.nextFresh linkParentsBelow _
      (natListGetAt_lt state.nextFresh nfPos state.openWires positionLow fresh.1)
  have rootRightBelow :
      unionFindRootOf state.links (natListGetAt state.openWires (positionLow + 1))
        < state.nextFresh :=
    unionFindRootOf_lt_of_fresh state.links state.nextFresh linkParentsBelow _
      (natListGetAt_lt state.nextFresh nfPos state.openWires (positionLow + 1) fresh.1)
  have collapseRight :
      unionFindRootOf (stepCupArc state (gap + 2 + positionLow)).links
          (natListGetAt state.openWires (positionLow + 1))
        = unionFindRootOf state.links (natListGetAt state.openWires (positionLow + 1)) :=
    unionFindRootOf_stepCupArc_old state (gap + 2 + positionLow) fresh forest _
      rootRightBelow
  have forestMergedT :
      isUnionFindForest (unionFindJoin (stepCupArc state (gap + 2 + positionLow)).links
        (natListGetAt state.openWires positionLow)
        (natListGetAt state.openWires (positionLow + 1))) :=
    isUnionFindForest_unionFindJoin _ _ _ forestCupMid
  have selfGuardOuter :
      (unionFindRootOf
          (unionFindJoin (stepCupArc state (gap + 2 + positionLow)).links
            (natListGetAt state.openWires positionLow)
            (natListGetAt state.openWires (positionLow + 1)))
          (state.nextFresh + 3)
        == unionFindRootOf
            (unionFindJoin (stepCupArc state (gap + 2 + positionLow)).links
              (natListGetAt state.openWires positionLow)
              (natListGetAt state.openWires (positionLow + 1)))
            (state.nextFresh + 3)) = true := decide_eq_true rfl
  have selfGuardInner :
      (unionFindRootOf (stepCupArc state (gap + 2 + positionLow)).links
          (natListGetAt state.openWires positionLow)
        == unionFindRootOf (stepCupArc state (gap + 2 + positionLow)).links
            (natListGetAt state.openWires positionLow)) = true := decide_eq_true rfl
  rw [capCupSwap_linksT state gap positionLow positionBound,
    unionFindRootOf_unionFindJoin
      (unionFindJoin (stepCupArc state (gap + 2 + positionLow)).links
        (natListGetAt state.openWires positionLow)
        (natListGetAt state.openWires (positionLow + 1)))
      (state.nextFresh + 3) (natListGetAt state.openWires positionLow)
      (state.nextFresh + 3) forestMergedT,
    if_pos selfGuardOuter,
    unionFindRootOf_unionFindJoin (stepCupArc state (gap + 2 + positionLow)).links
      (natListGetAt state.openWires positionLow)
      (natListGetAt state.openWires (positionLow + 1))
      (natListGetAt state.openWires positionLow) forestCupMid,
    if_pos selfGuardInner, collapseRight]

/-- **Nodes at or above both allocations stay parentless through order T.** -/
theorem capCupSwapT_root_above (state : ArcWireState)
    (fresh : ArcStateFresh state) (gap positionLow : Nat)
    (node : Nat) (isAtOrAbove : state.nextFresh + 4 ≤ node) :
    unionFindRootOf
        (stepCapArc (stepCupArc state (gap + 2 + positionLow)) positionLow).links node
      = node :=
  unionFindRootOf_of_parentless _ node
    (unionFindParent_none_of_freshNode
      (stepCapArc (stepCupArc state (gap + 2 + positionLow)) positionLow)
      (stepCapArc_arcStateFresh (stepCupArc state (gap + 2 + positionLow)) positionLow
        (stepCupArc_arcStateFresh state (gap + 2 + positionLow) fresh))
      node isAtOrAbove)

/-- **Order-T counts over OLD events collapse to the shared merged links.** -/
theorem capCupSwapT_countOld (state : ArcWireState)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (nfPos : 0 < state.nextFresh) (gap positionLow : Nat)
    (positionBound : gap + positionLow + 2 ≤ state.openWires.length)
    (rootHere : Nat) (events : List Nat)
    (allEventsBelow : ∀ node ∈ events, node < state.nextFresh) :
    countEventsInRoot
        (stepCapArc (stepCupArc state (gap + 2 + positionLow)) positionLow).links
        rootHere events
      = countEventsInRoot
          (unionFindJoin state.links (natListGetAt state.openWires positionLow)
            (natListGetAt state.openWires (positionLow + 1)))
          rootHere events :=
  countEventsInRoot_congr_links _ _ rootHere events
    (fun eventNode eventInList =>
      capCupSwapT_root_old state fresh forest nfPos gap positionLow positionBound eventNode
        (allEventsBelow eventNode eventInList))

/-! ## Order-S roots — through the cap, then the cup -/

/-- **Old nodes keep their merged roots through order S** — the cap atlas collapses the cap,
the cup leaves old roots alone. -/
theorem capCupSwapS_root_old (state : ArcWireState)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (nfPos : 0 < state.nextFresh) (gap positionLow : Nat)
    (node : Nat) (nodeBelow : node < state.nextFresh) :
    unionFindRootOf
        (stepCupArc (stepCapArc state positionLow) (gap + positionLow)).links node
      = unionFindRootOf
          (unionFindJoin state.links (natListGetAt state.openWires positionLow)
            (natListGetAt state.openWires (positionLow + 1)))
          node := by
  have freshCapMid : ArcStateFresh (stepCapArc state positionLow) :=
    stepCapArc_arcStateFresh state positionLow fresh
  have forestCapMid : isUnionFindForest (stepCapArc state positionLow).links :=
    isUnionFindForest_stepCapArc state positionLow forest
  have mergedRootBelow :
      unionFindRootOf
          (unionFindJoin state.links (natListGetAt state.openWires positionLow)
            (natListGetAt state.openWires (positionLow + 1)))
          node
        < state.nextFresh :=
    capMerge_root_below state positionLow fresh nfPos node nodeBelow
  have capOld :
      unionFindRootOf (stepCapArc state positionLow).links node
        = unionFindRootOf
            (unionFindJoin state.links (natListGetAt state.openWires positionLow)
              (natListGetAt state.openWires (positionLow + 1)))
            node :=
    stepCapArc_root_old state positionLow fresh forest nfPos node mergedRootBelow
  have rootMidBelow :
      unionFindRootOf (stepCapArc state positionLow).links node
        < state.nextFresh + 1 := by
    rw [capOld]
    exact Nat.lt_trans mergedRootBelow (Nat.lt_add_of_pos_right (by decide))
  exact Eq.trans
    (unionFindRootOf_stepCupArc_old (stepCapArc state positionLow) (gap + positionLow)
      freshCapMid forestCapMid node rootMidBelow)
    capOld

/-- **Order S's cap event keeps its old root through the cup** — it roots at the right wire's
old root, which is below every fresh allocation. -/
theorem capCupSwapS_root_capEvent (state : ArcWireState)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (nfPos : 0 < state.nextFresh) (gap positionLow : Nat) :
    unionFindRootOf
        (stepCupArc (stepCapArc state positionLow) (gap + positionLow)).links
        state.nextFresh
      = unionFindRootOf state.links (natListGetAt state.openWires (positionLow + 1)) := by
  have freshCapMid : ArcStateFresh (stepCapArc state positionLow) :=
    stepCapArc_arcStateFresh state positionLow fresh
  have forestCapMid : isUnionFindForest (stepCapArc state positionLow).links :=
    isUnionFindForest_stepCapArc state positionLow forest
  have linkParentsBelow : ∀ edge ∈ state.links, edge.2 < state.nextFresh :=
    fun edge edgeInLinks => (fresh.2.1 edge edgeInLinks).2
  have rootRightBelow :
      unionFindRootOf state.links (natListGetAt state.openWires (positionLow + 1))
        < state.nextFresh :=
    unionFindRootOf_lt_of_fresh state.links state.nextFresh linkParentsBelow _
      (natListGetAt_lt state.nextFresh nfPos state.openWires (positionLow + 1) fresh.1)
  have capEventRoot :
      unionFindRootOf (stepCapArc state positionLow).links state.nextFresh
        = unionFindRootOf state.links (natListGetAt state.openWires (positionLow + 1)) :=
    stepCapArc_root_event state positionLow fresh forest nfPos
  have rootMidBelow :
      unionFindRootOf (stepCapArc state positionLow).links state.nextFresh
        < state.nextFresh + 1 := by
    rw [capEventRoot]
    exact Nat.lt_trans rootRightBelow (Nat.lt_add_of_pos_right (by decide))
  exact Eq.trans
    (unionFindRootOf_stepCupArc_old (stepCapArc state positionLow) (gap + positionLow)
      freshCapMid forestCapMid state.nextFresh rootMidBelow)
    capEventRoot

/-- **Nodes at or above both allocations stay parentless through order S.** -/
theorem capCupSwapS_root_above (state : ArcWireState)
    (fresh : ArcStateFresh state) (gap positionLow : Nat)
    (node : Nat) (isAtOrAbove : state.nextFresh + 4 ≤ node) :
    unionFindRootOf
        (stepCupArc (stepCapArc state positionLow) (gap + positionLow)).links node
      = node :=
  unionFindRootOf_of_parentless _ node
    (unionFindParent_none_of_freshNode
      (stepCupArc (stepCapArc state positionLow) (gap + positionLow))
      (stepCupArc_arcStateFresh (stepCapArc state positionLow) (gap + positionLow)
        (stepCapArc_arcStateFresh state positionLow fresh))
      node isAtOrAbove)

/-- **Order-S counts over OLD events collapse to the shared merged links.** -/
theorem capCupSwapS_countOld (state : ArcWireState)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (nfPos : 0 < state.nextFresh) (gap positionLow : Nat)
    (rootHere : Nat) (events : List Nat)
    (allEventsBelow : ∀ node ∈ events, node < state.nextFresh) :
    countEventsInRoot
        (stepCupArc (stepCapArc state positionLow) (gap + positionLow)).links
        rootHere events
      = countEventsInRoot
          (unionFindJoin state.links (natListGetAt state.openWires positionLow)
            (natListGetAt state.openWires (positionLow + 1)))
          rootHere events :=
  countEventsInRoot_congr_links _ _ rootHere events
    (fun eventNode eventInList =>
      capCupSwapS_root_old state fresh forest nfPos gap positionLow eventNode
        (allEventsBelow eventNode eventInList))

/-- **Counts of old events at a fresh root over the merged links vanish** — the merge is an
old-world operation. -/
theorem capCupSwap_countMergedZero (state : ArcWireState)
    (fresh : ArcStateFresh state) (nfPos : 0 < state.nextFresh) (positionLow : Nat)
    (rootHere : Nat) (isAtOrAbove : state.nextFresh ≤ rootHere)
    (events : List Nat) (allEventsBelow : ∀ node ∈ events, node < state.nextFresh) :
    countEventsInRoot
        (unionFindJoin state.links (natListGetAt state.openWires positionLow)
          (natListGetAt state.openWires (positionLow + 1)))
        rootHere events
      = 0 :=
  countEventsInRoot_eq_zero_of_freshRoot _ state.nextFresh
    (fun edge edgeInJoin =>
      (capMerge_all_below state positionLow fresh nfPos edge edgeInJoin).2)
    rootHere isAtOrAbove events allEventsBelow

/-! ## The three transposition field lemmas -/

/-- ★ **The width-`1, 3` transposition root-commutes between the two orders.**  Below
`nextFresh` everything is fixed and both orders collapse to the shared merged links; the two
cap events exchange and both root at the right wire's old root; the cup's triple maps
block-to-block (S roots at `nextFresh + 2`, T at `nextFresh + 1` — the transposition's image);
at or above both allocations everything is parentless and fixed. -/
theorem capCupSwap_rootComm (state : ArcWireState)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (nfPos : 0 < state.nextFresh) (gap positionLow : Nat)
    (positionBound : gap + positionLow + 2 ≤ state.openWires.length)
    (node : Nat) :
    unionFindRootOf
        (stepCapArc (stepCupArc state (gap + 2 + positionLow)) positionLow).links
        (arcFreshBlockTransposition state.nextFresh 1 3 node)
      = arcFreshBlockTransposition state.nextFresh 1 3
          (unionFindRootOf
            (stepCupArc (stepCapArc state positionLow) (gap + positionLow)).links
            node) := by
  cases Nat.lt_or_ge node state.nextFresh with
  | inl nodeBelow =>
      have mergedRootBelow :
          unionFindRootOf
              (unionFindJoin state.links (natListGetAt state.openWires positionLow)
                (natListGetAt state.openWires (positionLow + 1)))
              node
            < state.nextFresh :=
        capMerge_root_below state positionLow fresh nfPos node nodeBelow
      rw [arcFreshBlockTransposition_ofBelow state.nextFresh 1 3 node nodeBelow,
        capCupSwapT_root_old state fresh forest nfPos gap positionLow positionBound node
          nodeBelow,
        capCupSwapS_root_old state fresh forest nfPos gap positionLow node nodeBelow,
        arcFreshBlockTransposition_ofBelow state.nextFresh 1 3
          (unionFindRootOf
            (unionFindJoin state.links (natListGetAt state.openWires positionLow)
              (natListGetAt state.openWires (positionLow + 1)))
            node)
          mergedRootBelow]
  | inr nodeAtOrAbove =>
      have freshCapMid : ArcStateFresh (stepCapArc state positionLow) :=
        stepCapArc_arcStateFresh state positionLow fresh
      have forestCapMid : isUnionFindForest (stepCapArc state positionLow).links :=
        isUnionFindForest_stepCapArc state positionLow forest
      have linkParentsBelow : ∀ edge ∈ state.links, edge.2 < state.nextFresh :=
        fun edge edgeInLinks => (fresh.2.1 edge edgeInLinks).2
      have rootRightBelow :
          unionFindRootOf state.links (natListGetAt state.openWires (positionLow + 1))
            < state.nextFresh :=
        unionFindRootOf_lt_of_fresh state.links state.nextFresh linkParentsBelow _
          (natListGetAt_lt state.nextFresh nfPos state.openWires (positionLow + 1) fresh.1)
      have sigmaFirstZero :
          arcFreshBlockTransposition state.nextFresh 1 3 state.nextFresh
            = state.nextFresh + 3 :=
        arcFreshBlockTransposition_onFirstBlock state.nextFresh 1 3 0 (by decide)
      have sigmaSecondZero :
          arcFreshBlockTransposition state.nextFresh 1 3 (state.nextFresh + 1)
            = state.nextFresh :=
        arcFreshBlockTransposition_onSecondBlock state.nextFresh 1 3 0 (by decide)
      have sigmaSecondOne :
          arcFreshBlockTransposition state.nextFresh 1 3 (state.nextFresh + 2)
            = state.nextFresh + 1 :=
        arcFreshBlockTransposition_onSecondBlock state.nextFresh 1 3 1 (by decide)
      have sigmaSecondTwo :
          arcFreshBlockTransposition state.nextFresh 1 3 (state.nextFresh + 3)
            = state.nextFresh + 2 :=
        arcFreshBlockTransposition_onSecondBlock state.nextFresh 1 3 2 (by decide)
      have rootSLeftLeg :
          unionFindRootOf
              (stepCupArc (stepCapArc state positionLow) (gap + positionLow)).links
              (state.nextFresh + 1)
            = state.nextFresh + 2 :=
        stepCupArc_root_leftLeg (stepCapArc state positionLow) (gap + positionLow)
          freshCapMid forestCapMid
      have rootSRightLeg :
          unionFindRootOf
              (stepCupArc (stepCapArc state positionLow) (gap + positionLow)).links
              (state.nextFresh + 2)
            = state.nextFresh + 2 :=
        stepCupArc_root_rightLeg (stepCapArc state positionLow) (gap + positionLow)
          freshCapMid forestCapMid
      have rootSEventNode :
          unionFindRootOf
              (stepCupArc (stepCapArc state positionLow) (gap + positionLow)).links
              (state.nextFresh + 3)
            = state.nextFresh + 2 :=
        stepCupArc_root_eventNode (stepCapArc state positionLow) (gap + positionLow)
          freshCapMid forestCapMid
      have rootTAtBase :
          unionFindRootOf
              (stepCapArc (stepCupArc state (gap + 2 + positionLow)) positionLow).links
              state.nextFresh
            = state.nextFresh + 1 :=
        capCupSwapT_root_triple state fresh forest nfPos gap positionLow positionBound
          state.nextFresh
          (stepCupArc_root_leftLeg state (gap + 2 + positionLow) fresh forest)
      have rootTAtOne :
          unionFindRootOf
              (stepCapArc (stepCupArc state (gap + 2 + positionLow)) positionLow).links
              (state.nextFresh + 1)
            = state.nextFresh + 1 :=
        capCupSwapT_root_triple state fresh forest nfPos gap positionLow positionBound
          (state.nextFresh + 1)
          (stepCupArc_root_rightLeg state (gap + 2 + positionLow) fresh forest)
      have rootTAtTwo :
          unionFindRootOf
              (stepCapArc (stepCupArc state (gap + 2 + positionLow)) positionLow).links
              (state.nextFresh + 2)
            = state.nextFresh + 1 :=
        capCupSwapT_root_triple state fresh forest nfPos gap positionLow positionBound
          (state.nextFresh + 2)
          (stepCupArc_root_eventNode state (gap + 2 + positionLow) fresh forest)
      have rootTCapEvent :
          unionFindRootOf
              (stepCapArc (stepCupArc state (gap + 2 + positionLow)) positionLow).links
              (state.nextFresh + 3)
            = unionFindRootOf state.links
                (natListGetAt state.openWires (positionLow + 1)) :=
        capCupSwapT_root_capEvent state fresh forest nfPos gap positionLow positionBound
      have rootSCapEvent :
          unionFindRootOf
              (stepCupArc (stepCapArc state positionLow) (gap + positionLow)).links
              state.nextFresh
            = unionFindRootOf state.links
                (natListGetAt state.openWires (positionLow + 1)) :=
        capCupSwapS_root_capEvent state fresh forest nfPos gap positionLow
      cases Nat.lt_or_ge node (state.nextFresh + 1) with
      | inl belowOne =>
          have nodeIsBase : node = state.nextFresh :=
            Nat.le_antisymm (Nat.le_of_lt_succ belowOne) nodeAtOrAbove
          subst nodeIsBase
          rw [sigmaFirstZero, rootTCapEvent, rootSCapEvent,
            arcFreshBlockTransposition_ofBelow state.nextFresh 1 3
              (unionFindRootOf state.links
                (natListGetAt state.openWires (positionLow + 1)))
              rootRightBelow]
      | inr nodeAtLeastOne =>
      cases Nat.lt_or_ge node (state.nextFresh + 2) with
      | inl belowTwo =>
          have nodeIsOne : node = state.nextFresh + 1 :=
            Nat.le_antisymm (Nat.le_of_lt_succ belowTwo) nodeAtLeastOne
          subst nodeIsOne
          rw [sigmaSecondZero, rootTAtBase, rootSLeftLeg, sigmaSecondOne]
      | inr nodeAtLeastTwo =>
      cases Nat.lt_or_ge node (state.nextFresh + 3) with
      | inl belowThree =>
          have nodeIsTwo : node = state.nextFresh + 2 :=
            Nat.le_antisymm (Nat.le_of_lt_succ belowThree) nodeAtLeastTwo
          subst nodeIsTwo
          rw [sigmaSecondOne, rootTAtOne, rootSRightLeg, sigmaSecondOne]
      | inr nodeAtLeastThree =>
      cases Nat.lt_or_ge node (state.nextFresh + 4) with
      | inl belowFour =>
          have nodeIsThree : node = state.nextFresh + 3 :=
            Nat.le_antisymm (Nat.le_of_lt_succ belowFour) nodeAtLeastThree
          subst nodeIsThree
          rw [sigmaSecondTwo, rootTAtTwo, rootSEventNode, sigmaSecondOne]
      | inr nodeAtLeastFour =>
          have sigmaFixed :
              arcFreshBlockTransposition state.nextFresh 1 3 node = node :=
            arcFreshBlockTransposition_ofAtOrAbove state.nextFresh 1 3 node
              nodeAtLeastFour
          rw [sigmaFixed,
            capCupSwapT_root_above state fresh gap positionLow node nodeAtLeastFour,
            capCupSwapS_root_above state fresh gap positionLow node nodeAtLeastFour,
            sigmaFixed]

/-- ★ **The per-root cup-event counts correspond across the transposition.**  Each order
pushes ONE cup event — `nextFresh + 3` in S (rooting at `nextFresh + 2`) and `nextFresh + 2`
in T (rooting at `nextFresh + 1`, the transposition's image) — so the head guards fire at
exactly corresponding roots; old counts collapse to the shared merged links; fresh tails
vanish. -/
theorem capCupSwap_cupCorr (state : ArcWireState)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (nfPos : 0 < state.nextFresh) (gap positionLow : Nat)
    (positionBound : gap + positionLow + 2 ≤ state.openWires.length)
    (countRoot : Nat) :
    countEventsInRoot
        (stepCapArc (stepCupArc state (gap + 2 + positionLow)) positionLow).links
        (arcFreshBlockTransposition state.nextFresh 1 3 countRoot)
        (stepCapArc (stepCupArc state (gap + 2 + positionLow)) positionLow).cupEventNodes
      = countEventsInRoot
          (stepCupArc (stepCapArc state positionLow) (gap + positionLow)).links
          countRoot
          (stepCupArc (stepCapArc state positionLow) (gap + positionLow)).cupEventNodes
    := by
  have freshCapMid : ArcStateFresh (stepCapArc state positionLow) :=
    stepCapArc_arcStateFresh state positionLow fresh
  have forestCapMid : isUnionFindForest (stepCapArc state positionLow).links :=
    isUnionFindForest_stepCapArc state positionLow forest
  have rootTHeadTwo :
      unionFindRootOf
          (stepCapArc (stepCupArc state (gap + 2 + positionLow)) positionLow).links
          (state.nextFresh + 2)
        = state.nextFresh + 1 :=
    capCupSwapT_root_triple state fresh forest nfPos gap positionLow positionBound
      (state.nextFresh + 2)
      (stepCupArc_root_eventNode state (gap + 2 + positionLow) fresh forest)
  have rootSHeadThree :
      unionFindRootOf
          (stepCupArc (stepCapArc state positionLow) (gap + positionLow)).links
          (state.nextFresh + 3)
        = state.nextFresh + 2 :=
    stepCupArc_root_eventNode (stepCapArc state positionLow) (gap + positionLow)
      freshCapMid forestCapMid
  show (if unionFindRootOf
          (stepCapArc (stepCupArc state (gap + 2 + positionLow)) positionLow).links
          (state.nextFresh + 2)
        == arcFreshBlockTransposition state.nextFresh 1 3 countRoot then (1 : Nat) else 0)
      + countEventsInRoot
          (stepCapArc (stepCupArc state (gap + 2 + positionLow)) positionLow).links
          (arcFreshBlockTransposition state.nextFresh 1 3 countRoot) state.cupEventNodes
    = (if unionFindRootOf
          (stepCupArc (stepCapArc state positionLow) (gap + positionLow)).links
          (state.nextFresh + 3)
        == countRoot then (1 : Nat) else 0)
      + countEventsInRoot
          (stepCupArc (stepCapArc state positionLow) (gap + positionLow)).links
          countRoot state.cupEventNodes
  rw [rootTHeadTwo, rootSHeadThree]
  have sigmaFirstZero :
      arcFreshBlockTransposition state.nextFresh 1 3 state.nextFresh
        = state.nextFresh + 3 :=
    arcFreshBlockTransposition_onFirstBlock state.nextFresh 1 3 0 (by decide)
  have sigmaSecondZero :
      arcFreshBlockTransposition state.nextFresh 1 3 (state.nextFresh + 1)
        = state.nextFresh :=
    arcFreshBlockTransposition_onSecondBlock state.nextFresh 1 3 0 (by decide)
  have sigmaSecondOne :
      arcFreshBlockTransposition state.nextFresh 1 3 (state.nextFresh + 2)
        = state.nextFresh + 1 :=
    arcFreshBlockTransposition_onSecondBlock state.nextFresh 1 3 1 (by decide)
  have sigmaSecondTwo :
      arcFreshBlockTransposition state.nextFresh 1 3 (state.nextFresh + 3)
        = state.nextFresh + 2 :=
    arcFreshBlockTransposition_onSecondBlock state.nextFresh 1 3 2 (by decide)
  have baseBelowOne : state.nextFresh < state.nextFresh + 1 :=
    Nat.lt_add_of_pos_right (by decide)
  have baseBelowTwo : state.nextFresh < state.nextFresh + 2 :=
    Nat.lt_add_of_pos_right (by decide)
  have oneBelowTwo : state.nextFresh + 1 < state.nextFresh + 2 :=
    Nat.add_lt_add_left (by decide) state.nextFresh
  have oneBelowThree : state.nextFresh + 1 < state.nextFresh + 3 :=
    Nat.add_lt_add_left (by decide) state.nextFresh
  have twoBelowThree : state.nextFresh + 2 < state.nextFresh + 3 :=
    Nat.add_lt_add_left (by decide) state.nextFresh
  have guardOneThree : ¬ (state.nextFresh + 1 == state.nextFresh + 3) = true :=
    fun isTrue => Bool.noConfusion (beq_false_of_lt_left oneBelowThree ▸ isTrue)
  have guardTwoBase : ¬ (state.nextFresh + 2 == state.nextFresh) = true :=
    fun isTrue => Bool.noConfusion (beq_false_of_lt baseBelowTwo ▸ isTrue)
  have guardOneBase : ¬ (state.nextFresh + 1 == state.nextFresh) = true :=
    fun isTrue => Bool.noConfusion (beq_false_of_lt baseBelowOne ▸ isTrue)
  have guardTwoOne : ¬ (state.nextFresh + 2 == state.nextFresh + 1) = true :=
    fun isTrue => Bool.noConfusion (beq_false_of_lt oneBelowTwo ▸ isTrue)
  have guardOneTwo : ¬ (state.nextFresh + 1 == state.nextFresh + 2) = true :=
    fun isTrue => Bool.noConfusion (beq_false_of_lt_left oneBelowTwo ▸ isTrue)
  have guardTwoThree : ¬ (state.nextFresh + 2 == state.nextFresh + 3) = true :=
    fun isTrue => Bool.noConfusion (beq_false_of_lt_left twoBelowThree ▸ isTrue)
  have trueOneOne : (state.nextFresh + 1 == state.nextFresh + 1) = true :=
    decide_eq_true rfl
  have trueTwoTwo : (state.nextFresh + 2 == state.nextFresh + 2) = true :=
    decide_eq_true rfl
  cases Nat.lt_or_ge countRoot state.nextFresh with
  | inl rootBelow =>
      have guardOneOld : ¬ (state.nextFresh + 1 == countRoot) = true :=
        fun isTrue =>
          Bool.noConfusion
            (beq_false_of_lt (Nat.lt_trans rootBelow baseBelowOne) ▸ isTrue)
      have guardTwoOld : ¬ (state.nextFresh + 2 == countRoot) = true :=
        fun isTrue =>
          Bool.noConfusion
            (beq_false_of_lt (Nat.lt_trans rootBelow baseBelowTwo) ▸ isTrue)
      rw [arcFreshBlockTransposition_ofBelow state.nextFresh 1 3 countRoot rootBelow,
        if_neg guardOneOld, if_neg guardTwoOld,
        capCupSwapT_countOld state fresh forest nfPos gap positionLow positionBound
          countRoot state.cupEventNodes fresh.2.2.1,
        capCupSwapS_countOld state fresh forest nfPos gap positionLow countRoot
          state.cupEventNodes fresh.2.2.1]
  | inr rootAtLeastBase =>
  cases Nat.lt_or_ge countRoot (state.nextFresh + 1) with
  | inl belowOne =>
      have rootIsBase : countRoot = state.nextFresh :=
        Nat.le_antisymm (Nat.le_of_lt_succ belowOne) rootAtLeastBase
      subst rootIsBase
      rw [sigmaFirstZero, if_neg guardOneThree, if_neg guardTwoBase,
        capCupSwapT_countOld state fresh forest nfPos gap positionLow positionBound
          (state.nextFresh + 3) state.cupEventNodes fresh.2.2.1,
        capCupSwapS_countOld state fresh forest nfPos gap positionLow state.nextFresh
          state.cupEventNodes fresh.2.2.1,
        capCupSwap_countMergedZero state fresh nfPos positionLow (state.nextFresh + 3)
          (Nat.le_add_right state.nextFresh 3) state.cupEventNodes fresh.2.2.1,
        capCupSwap_countMergedZero state fresh nfPos positionLow state.nextFresh
          (Nat.le_refl state.nextFresh) state.cupEventNodes fresh.2.2.1]
  | inr rootAtLeastOne =>
  cases Nat.lt_or_ge countRoot (state.nextFresh + 2) with
  | inl belowTwo =>
      have rootIsOne : countRoot = state.nextFresh + 1 :=
        Nat.le_antisymm (Nat.le_of_lt_succ belowTwo) rootAtLeastOne
      subst rootIsOne
      rw [sigmaSecondZero, if_neg guardOneBase, if_neg guardTwoOne,
        capCupSwapT_countOld state fresh forest nfPos gap positionLow positionBound
          state.nextFresh state.cupEventNodes fresh.2.2.1,
        capCupSwapS_countOld state fresh forest nfPos gap positionLow
          (state.nextFresh + 1) state.cupEventNodes fresh.2.2.1,
        capCupSwap_countMergedZero state fresh nfPos positionLow state.nextFresh
          (Nat.le_refl state.nextFresh) state.cupEventNodes fresh.2.2.1,
        capCupSwap_countMergedZero state fresh nfPos positionLow (state.nextFresh + 1)
          (Nat.le_add_right state.nextFresh 1) state.cupEventNodes fresh.2.2.1]
  | inr rootAtLeastTwo =>
  cases Nat.lt_or_ge countRoot (state.nextFresh + 3) with
  | inl belowThree =>
      have rootIsTwo : countRoot = state.nextFresh + 2 :=
        Nat.le_antisymm (Nat.le_of_lt_succ belowThree) rootAtLeastTwo
      subst rootIsTwo
      rw [sigmaSecondOne, if_pos trueOneOne, if_pos trueTwoTwo,
        capCupSwapT_countOld state fresh forest nfPos gap positionLow positionBound
          (state.nextFresh + 1) state.cupEventNodes fresh.2.2.1,
        capCupSwapS_countOld state fresh forest nfPos gap positionLow
          (state.nextFresh + 2) state.cupEventNodes fresh.2.2.1,
        capCupSwap_countMergedZero state fresh nfPos positionLow (state.nextFresh + 1)
          (Nat.le_add_right state.nextFresh 1) state.cupEventNodes fresh.2.2.1,
        capCupSwap_countMergedZero state fresh nfPos positionLow (state.nextFresh + 2)
          (Nat.le_add_right state.nextFresh 2) state.cupEventNodes fresh.2.2.1]
  | inr rootAtLeastThree =>
  cases Nat.lt_or_ge countRoot (state.nextFresh + 4) with
  | inl belowFour =>
      have rootIsThree : countRoot = state.nextFresh + 3 :=
        Nat.le_antisymm (Nat.le_of_lt_succ belowFour) rootAtLeastThree
      subst rootIsThree
      rw [sigmaSecondTwo, if_neg guardOneTwo, if_neg guardTwoThree,
        capCupSwapT_countOld state fresh forest nfPos gap positionLow positionBound
          (state.nextFresh + 2) state.cupEventNodes fresh.2.2.1,
        capCupSwapS_countOld state fresh forest nfPos gap positionLow
          (state.nextFresh + 3) state.cupEventNodes fresh.2.2.1,
        capCupSwap_countMergedZero state fresh nfPos positionLow (state.nextFresh + 2)
          (Nat.le_add_right state.nextFresh 2) state.cupEventNodes fresh.2.2.1,
        capCupSwap_countMergedZero state fresh nfPos positionLow (state.nextFresh + 3)
          (Nat.le_add_right state.nextFresh 3) state.cupEventNodes fresh.2.2.1]
  | inr rootAtLeastFour =>
      have sigmaFixed :
          arcFreshBlockTransposition state.nextFresh 1 3 countRoot = countRoot :=
        arcFreshBlockTransposition_ofAtOrAbove state.nextFresh 1 3 countRoot
          rootAtLeastFour
      have oneBelowRoot : state.nextFresh + 1 < countRoot :=
        Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by decide) state.nextFresh)
          rootAtLeastFour
      have twoBelowRoot : state.nextFresh + 2 < countRoot :=
        Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by decide) state.nextFresh)
          rootAtLeastFour
      have guardOneHigh : ¬ (state.nextFresh + 1 == countRoot) = true :=
        fun isTrue => Bool.noConfusion (beq_false_of_lt_left oneBelowRoot ▸ isTrue)
      have guardTwoHigh : ¬ (state.nextFresh + 2 == countRoot) = true :=
        fun isTrue => Bool.noConfusion (beq_false_of_lt_left twoBelowRoot ▸ isTrue)
      rw [sigmaFixed, if_neg guardOneHigh, if_neg guardTwoHigh,
        capCupSwapT_countOld state fresh forest nfPos gap positionLow positionBound
          countRoot state.cupEventNodes fresh.2.2.1,
        capCupSwapS_countOld state fresh forest nfPos gap positionLow countRoot
          state.cupEventNodes fresh.2.2.1,
        capCupSwap_countMergedZero state fresh nfPos positionLow countRoot
          (Nat.le_trans (Nat.le_add_right state.nextFresh 4) rootAtLeastFour)
          state.cupEventNodes fresh.2.2.1]

/-- ★ **The per-root cap-event counts correspond across the transposition.**  Both orders'
cap events root at the SAME old root (the right wire's), so the head guards agree wherever
the transposition acts; old tails collapse to the shared merged links; fresh tails vanish. -/
theorem capCupSwap_capCorr (state : ArcWireState)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (nfPos : 0 < state.nextFresh) (gap positionLow : Nat)
    (positionBound : gap + positionLow + 2 ≤ state.openWires.length)
    (countRoot : Nat) :
    countEventsInRoot
        (stepCapArc (stepCupArc state (gap + 2 + positionLow)) positionLow).links
        (arcFreshBlockTransposition state.nextFresh 1 3 countRoot)
        (stepCapArc (stepCupArc state (gap + 2 + positionLow)) positionLow).capEventNodes
      = countEventsInRoot
          (stepCupArc (stepCapArc state positionLow) (gap + positionLow)).links
          countRoot
          (stepCupArc (stepCapArc state positionLow) (gap + positionLow)).capEventNodes
    := by
  have linkParentsBelow : ∀ edge ∈ state.links, edge.2 < state.nextFresh :=
    fun edge edgeInLinks => (fresh.2.1 edge edgeInLinks).2
  have rootRightBelow :
      unionFindRootOf state.links (natListGetAt state.openWires (positionLow + 1))
        < state.nextFresh :=
    unionFindRootOf_lt_of_fresh state.links state.nextFresh linkParentsBelow _
      (natListGetAt_lt state.nextFresh nfPos state.openWires (positionLow + 1) fresh.1)
  have rootTCapEvent :
      unionFindRootOf
          (stepCapArc (stepCupArc state (gap + 2 + positionLow)) positionLow).links
          (state.nextFresh + 3)
        = unionFindRootOf state.links (natListGetAt state.openWires (positionLow + 1)) :=
    capCupSwapT_root_capEvent state fresh forest nfPos gap positionLow positionBound
  have rootSCapEvent :
      unionFindRootOf
          (stepCupArc (stepCapArc state positionLow) (gap + positionLow)).links
          state.nextFresh
        = unionFindRootOf state.links (natListGetAt state.openWires (positionLow + 1)) :=
    capCupSwapS_root_capEvent state fresh forest nfPos gap positionLow
  show (if unionFindRootOf
          (stepCapArc (stepCupArc state (gap + 2 + positionLow)) positionLow).links
          (state.nextFresh + 3)
        == arcFreshBlockTransposition state.nextFresh 1 3 countRoot then (1 : Nat) else 0)
      + countEventsInRoot
          (stepCapArc (stepCupArc state (gap + 2 + positionLow)) positionLow).links
          (arcFreshBlockTransposition state.nextFresh 1 3 countRoot) state.capEventNodes
    = (if unionFindRootOf
          (stepCupArc (stepCapArc state positionLow) (gap + positionLow)).links
          state.nextFresh
        == countRoot then (1 : Nat) else 0)
      + countEventsInRoot
          (stepCupArc (stepCapArc state positionLow) (gap + positionLow)).links
          countRoot state.capEventNodes
  rw [rootTCapEvent, rootSCapEvent]
  cases Nat.lt_or_ge countRoot state.nextFresh with
  | inl rootBelow =>
      rw [arcFreshBlockTransposition_ofBelow state.nextFresh 1 3 countRoot rootBelow,
        capCupSwapT_countOld state fresh forest nfPos gap positionLow positionBound
          countRoot state.capEventNodes fresh.2.2.2,
        capCupSwapS_countOld state fresh forest nfPos gap positionLow countRoot
          state.capEventNodes fresh.2.2.2]
  | inr rootAtOrAbove =>
      have sigmaImageAtOrAbove :
          state.nextFresh
            ≤ arcFreshBlockTransposition state.nextFresh 1 3 countRoot :=
        sigmaAtOrAbove_of_fixesBelow (arcFreshBlockTransposition state.nextFresh 1 3)
          (fun firstId secondId imagesEqual =>
            arcFreshBlockTransposition_injective state.nextFresh 1 3 firstId secondId
              imagesEqual)
          state.nextFresh
          (fun identifier isBelow =>
            arcFreshBlockTransposition_ofBelow state.nextFresh 1 3 identifier isBelow)
          countRoot rootAtOrAbove
      have guardSourceHigh :
          ¬ (unionFindRootOf state.links
              (natListGetAt state.openWires (positionLow + 1))
            == countRoot) = true :=
        fun isTrue =>
          Bool.noConfusion
            (beq_false_of_lt_left (Nat.lt_of_lt_of_le rootRightBelow rootAtOrAbove)
              ▸ isTrue)
      have guardTargetHigh :
          ¬ (unionFindRootOf state.links
              (natListGetAt state.openWires (positionLow + 1))
            == arcFreshBlockTransposition state.nextFresh 1 3 countRoot) = true :=
        fun isTrue =>
          Bool.noConfusion
            (beq_false_of_lt_left (Nat.lt_of_lt_of_le rootRightBelow sigmaImageAtOrAbove)
              ▸ isTrue)
      rw [if_neg guardTargetHigh, if_neg guardSourceHigh,
        capCupSwapT_countOld state fresh forest nfPos gap positionLow positionBound
          (arcFreshBlockTransposition state.nextFresh 1 3 countRoot) state.capEventNodes
          fresh.2.2.2,
        capCupSwapS_countOld state fresh forest nfPos gap positionLow countRoot
          state.capEventNodes fresh.2.2.2,
        capCupSwap_countMergedZero state fresh nfPos positionLow
          (arcFreshBlockTransposition state.nextFresh 1 3 countRoot) sigmaImageAtOrAbove
          state.capEventNodes fresh.2.2.2,
        capCupSwap_countMergedZero state fresh nfPos positionLow countRoot rootAtOrAbove
          state.capEventNodes fresh.2.2.2]

/-! ## The assembled simulation -/

/-- ★ **The CAP x CUP two-step core simulation.**  Order S fires the low cap at `positionLow`
then the high cup at `gap + positionLow` (the cap consumed two wires); order T fires the high
cup at `gap + 2 + positionLow` then the low cap at `positionLow`.  The fresh-block
transposition at widths `1, 3` is an `ArcStepSimCount` between the results: order T's cap
reads strictly below the cup's splice (below-locality), so both orders consume the same wire
values and build the same merged component; `openMap` is the iii-1a remove-below/insert-above
commutation; `loopsEq` is the same-component test's stability through the cup. -/
theorem arcStepSimCount_capCupSwap (state : ArcWireState)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (nfPos : 0 < state.nextFresh)
    (gap positionLow : Nat)
    (positionBound : gap + positionLow + 2 ≤ state.openWires.length) :
    ArcStepSimCount (arcFreshBlockTransposition state.nextFresh 1 3)
      (stepCupArc (stepCapArc state positionLow) (gap + positionLow))
      (stepCapArc (stepCupArc state (gap + 2 + positionLow)) positionLow) where
  openMap := by
    have sigmaSecondZero :
        arcFreshBlockTransposition state.nextFresh 1 3 (state.nextFresh + 1)
          = state.nextFresh :=
      arcFreshBlockTransposition_onSecondBlock state.nextFresh 1 3 0 (by decide)
    have sigmaSecondOne :
        arcFreshBlockTransposition state.nextFresh 1 3 (state.nextFresh + 2)
          = state.nextFresh + 1 :=
      arcFreshBlockTransposition_onSecondBlock state.nextFresh 1 3 1 (by decide)
    show natListRemoveTwoAt
        (natListInsertAt state.openWires (gap + 2 + positionLow)
          [state.nextFresh, state.nextFresh + 1])
        positionLow
      = (natListInsertAt (natListRemoveTwoAt state.openWires positionLow)
          (gap + positionLow)
          [state.nextFresh + 1, state.nextFresh + 2]).map
          (arcFreshBlockTransposition state.nextFresh 1 3)
    rw [natListInsertAt_map (arcFreshBlockTransposition state.nextFresh 1 3)
        (natListRemoveTwoAt state.openWires positionLow) (gap + positionLow)
        [state.nextFresh + 1, state.nextFresh + 2],
      natListRemoveTwoAt_map (arcFreshBlockTransposition state.nextFresh 1 3)
        state.openWires positionLow,
      mapPairValues (arcFreshBlockTransposition state.nextFresh 1 3)
        (state.nextFresh + 1) (state.nextFresh + 2),
      sigmaSecondZero, sigmaSecondOne,
      mapFixedOn (arcFreshBlockTransposition state.nextFresh 1 3) state.openWires
        (fun wire wireInList =>
          arcFreshBlockTransposition_ofBelow state.nextFresh 1 3 wire
            (fresh.1 wire wireInList)),
      natListRemoveTwoAt_insertAbove_commute state.openWires positionLow gap
        [state.nextFresh, state.nextFresh + 1] positionBound]
  nfEq := rfl
  rootComm := fun node =>
    capCupSwap_rootComm state fresh forest nfPos gap positionLow positionBound node
  loopsEq := by
    have windowWithinLength : positionLow + 2 ≤ state.openWires.length :=
      Nat.le_trans (Nat.le_add_left (positionLow + 2) gap)
        (by rw [← Nat.add_assoc]; exact positionBound)
    have belowLength : positionLow < state.openWires.length :=
      Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide)) windowWithinLength
    have succBelowLength : positionLow + 1 < state.openWires.length :=
      Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by decide) positionLow) windowWithinLength
    have gapTwoPos : 0 < gap + 2 := Nat.zero_lt_succ (gap + 1)
    have oneLtGapTwo : 1 < gap + 2 :=
      Nat.lt_of_lt_of_le (by decide) (Nat.le_add_left 2 gap)
    have belowInsert : positionLow < gap + 2 + positionLow := by
      rw [Nat.add_comm (gap + 2) positionLow]
      exact Nat.lt_add_of_pos_right gapTwoPos
    have succBelowInsert : positionLow + 1 < gap + 2 + positionLow := by
      rw [Nat.add_comm (gap + 2) positionLow]
      exact Nat.add_lt_add_left oneLtGapTwo positionLow
    have linkParentsBelow : ∀ edge ∈ state.links, edge.2 < state.nextFresh :=
      fun edge edgeInLinks => (fresh.2.1 edge edgeInLinks).2
    have rootLeftBelow :
        unionFindRootOf state.links (natListGetAt state.openWires positionLow)
          < state.nextFresh :=
      unionFindRootOf_lt_of_fresh state.links state.nextFresh linkParentsBelow _
        (natListGetAt_lt state.nextFresh nfPos state.openWires positionLow fresh.1)
    have rootRightBelow :
        unionFindRootOf state.links (natListGetAt state.openWires (positionLow + 1))
          < state.nextFresh :=
      unionFindRootOf_lt_of_fresh state.links state.nextFresh linkParentsBelow _
        (natListGetAt_lt state.nextFresh nfPos state.openWires (positionLow + 1) fresh.1)
    have collapseLeft :
        unionFindRootOf (stepCupArc state (gap + 2 + positionLow)).links
            (natListGetAt state.openWires positionLow)
          = unionFindRootOf state.links (natListGetAt state.openWires positionLow) :=
      unionFindRootOf_stepCupArc_old state (gap + 2 + positionLow) fresh forest _
        rootLeftBelow
    have collapseRight :
        unionFindRootOf (stepCupArc state (gap + 2 + positionLow)).links
            (natListGetAt state.openWires (positionLow + 1))
          = unionFindRootOf state.links (natListGetAt state.openWires (positionLow + 1))
        :=
      unionFindRootOf_stepCupArc_old state (gap + 2 + positionLow) fresh forest _
        rootRightBelow
    have componentStable :
        isSameComponent (stepCupArc state (gap + 2 + positionLow)).links
            (natListGetAt state.openWires positionLow)
            (natListGetAt state.openWires (positionLow + 1))
          = isSameComponent state.links (natListGetAt state.openWires positionLow)
              (natListGetAt state.openWires (positionLow + 1)) := by
      show (unionFindRootOf (stepCupArc state (gap + 2 + positionLow)).links
            (natListGetAt state.openWires positionLow)
          == unionFindRootOf (stepCupArc state (gap + 2 + positionLow)).links
              (natListGetAt state.openWires (positionLow + 1)))
        = (unionFindRootOf state.links (natListGetAt state.openWires positionLow)
          == unionFindRootOf state.links
              (natListGetAt state.openWires (positionLow + 1)))
      rw [collapseLeft, collapseRight]
    show (if isSameComponent (stepCupArc state (gap + 2 + positionLow)).links
            (natListGetAt (natListInsertAt state.openWires (gap + 2 + positionLow)
              [state.nextFresh, state.nextFresh + 1]) positionLow)
            (natListGetAt (natListInsertAt state.openWires (gap + 2 + positionLow)
              [state.nextFresh, state.nextFresh + 1]) (positionLow + 1))
          then state.loops + 1 else state.loops)
      = (if isSameComponent state.links (natListGetAt state.openWires positionLow)
            (natListGetAt state.openWires (positionLow + 1))
          then state.loops + 1 else state.loops)
    rw [natListGetAt_natListInsertAt_below state.openWires (gap + 2 + positionLow)
        [state.nextFresh, state.nextFresh + 1] positionLow belowInsert belowLength,
      natListGetAt_natListInsertAt_below state.openWires (gap + 2 + positionLow)
        [state.nextFresh, state.nextFresh + 1] (positionLow + 1) succBelowInsert
        succBelowLength,
      componentStable]
  cupCorr := fun countRoot =>
    capCupSwap_cupCorr state fresh forest nfPos gap positionLow positionBound countRoot
  capCorr := fun countRoot =>
    capCupSwap_capCorr state fresh forest nfPos gap positionLow positionBound countRoot
  forestS :=
    isUnionFindForest_stepCupArc (stepCapArc state positionLow) (gap + positionLow)
      (isUnionFindForest_stepCapArc state positionLow forest)
  forestT :=
    isUnionFindForest_stepCapArc (stepCupArc state (gap + 2 + positionLow)) positionLow
      (isUnionFindForest_stepCupArc state (gap + 2 + positionLow) forest)

/-! ## Honesty marker -/

/-- **Honesty marker — the CAP x CUP two-step core simulation is SHIPPED (ARC-2b brick
iii-1d-beta3).**  `arcStepSimCount_capCupSwap`: the two run orders of a cap-cup
disjoint-window swap are `ArcStepSimCount`-related by the fresh-block transposition at widths
`1, 3`.  Order T's cap reads strictly BELOW the cup's splice point, so below-locality
collapses its reads with no index arithmetic; both orders build the same merged component at
the low window, and roots and counts reduce to the alpha1 cup atlas + the beta1 cap atlas +
the shared merge.  `openMap` rides the iii-1a remove-below/insert-above commutation.  NOT yet
shipped: the CAP x CAP case (with the loop-transfer crossing analysis) and the dispatcher
that reads the realized ii-b swap pair into these position forms.  `= true`. -/
def fxMode_hasCapCupSwapSimulation : Bool := true

end FX1Poly.Polygraph
