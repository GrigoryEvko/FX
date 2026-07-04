import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupCupSwapSimulation

/-! # ArcCapRootAtlas — roots through one cap step (ARC-2b brick iii-1d-beta1)

Unlike a cup, a cap's links READ the state: it joins the two consumed wire values (old
identifiers, read off `openWires` at the fire position) and then joins its fresh event node
into the merged component.  The mixed arity cases of the two-step core simulation therefore
need a cap-side atlas phrased over the MERGED links
`unionFindJoin links leftWire rightWire` — the part both run orders share, since the two
orders consume the SAME wire values:

  * every merged-links edge stays below `nextFresh` (`capMerge_all_below`) — the merge is an
    OLD-world operation, so merged roots of old nodes stay old (`capMerge_root_below`);
  * the cap's event node roots at the RIGHT wire's old root (`stepCapArc_root_event`) — the
    join chain redirects `leftWire`'s component to `rightWire`'s root and hangs the event
    under it;
  * old nodes keep their MERGED roots through the cap (`stepCapArc_root_old`) — the event
    join's child is fresh and never sits on an old chain;
  * nodes at or above the cap's single fresh allocation stay parentless
    (`stepCapArc_root_above`);
  * per-root counts over old events collapse to the merged links
    (`stepCapArc_countOldEvents_congr`).

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- **Every merged-links edge stays below `nextFresh`.**  The cap's first join operates on two
OLD wire values (fresh openWires + the `natListGetAt` bound, with `0 < nextFresh` covering the
past-the-end default read), so the prepended edge joins two old roots. -/
theorem capMerge_all_below (state : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh state) (nfPos : 0 < state.nextFresh) :
    ∀ edge ∈ unionFindJoin state.links (natListGetAt state.openWires position)
        (natListGetAt state.openWires (position + 1)),
      edge.1 < state.nextFresh ∧ edge.2 < state.nextFresh :=
  unionFindJoin_all_lt state.nextFresh state.links
    (natListGetAt state.openWires position) (natListGetAt state.openWires (position + 1))
    fresh.2.1
    (unionFindRootOf_lt_of_fresh state.links state.nextFresh
      (fun edge edgeInLinks => (fresh.2.1 edge edgeInLinks).2)
      (natListGetAt state.openWires position)
      (natListGetAt_lt state.nextFresh nfPos state.openWires position fresh.1))
    (unionFindRootOf_lt_of_fresh state.links state.nextFresh
      (fun edge edgeInLinks => (fresh.2.1 edge edgeInLinks).2)
      (natListGetAt state.openWires (position + 1))
      (natListGetAt_lt state.nextFresh nfPos state.openWires (position + 1) fresh.1))

/-- **Merged roots of old nodes stay old** — the merged links' parents are all below
`nextFresh`, so root-following from below stays below. -/
theorem capMerge_root_below (state : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh state) (nfPos : 0 < state.nextFresh)
    (node : Nat) (nodeBelow : node < state.nextFresh) :
    unionFindRootOf
        (unionFindJoin state.links (natListGetAt state.openWires position)
          (natListGetAt state.openWires (position + 1)))
        node
      < state.nextFresh :=
  unionFindRootOf_lt_of_fresh
    (unionFindJoin state.links (natListGetAt state.openWires position)
      (natListGetAt state.openWires (position + 1)))
    state.nextFresh
    (fun edge edgeInJoin =>
      (capMerge_all_below state position fresh nfPos edge edgeInJoin).2)
    node nodeBelow

/-- ★ **The cap's event node roots at the right wire's old root.**  The outer join hangs the
event under `leftWire`'s post-merge root, and the merge itself redirected `leftWire`'s
component to `rightWire`'s root (in the already-connected case both are that root
outright). -/
theorem stepCapArc_root_event (state : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (nfPos : 0 < state.nextFresh) :
    unionFindRootOf (stepCapArc state position).links state.nextFresh
      = unionFindRootOf state.links (natListGetAt state.openWires (position + 1)) := by
  have forestMerged :
      isUnionFindForest (unionFindJoin state.links (natListGetAt state.openWires position)
        (natListGetAt state.openWires (position + 1))) :=
    isUnionFindForest_unionFindJoin state.links (natListGetAt state.openWires position)
      (natListGetAt state.openWires (position + 1)) forest
  have mergedChildrenBelow :
      ∀ edge ∈ unionFindJoin state.links (natListGetAt state.openWires position)
          (natListGetAt state.openWires (position + 1)),
        edge.1 < state.nextFresh :=
    fun edge edgeInJoin =>
      (capMerge_all_below state position fresh nfPos edge edgeInJoin).1
  have rootMergedEvent :
      unionFindRootOf
          (unionFindJoin state.links (natListGetAt state.openWires position)
            (natListGetAt state.openWires (position + 1)))
          state.nextFresh
        = state.nextFresh :=
    unionFindRootOf_of_parentless _ state.nextFresh
      (unionFindParent_none_of_lt state.nextFresh _ mergedChildrenBelow state.nextFresh
        (Nat.le_refl _))
  have selfGuardOuter :
      (unionFindRootOf
          (unionFindJoin state.links (natListGetAt state.openWires position)
            (natListGetAt state.openWires (position + 1)))
          state.nextFresh
        == unionFindRootOf
            (unionFindJoin state.links (natListGetAt state.openWires position)
              (natListGetAt state.openWires (position + 1)))
            state.nextFresh) = true := decide_eq_true rfl
  have selfGuardInner :
      (unionFindRootOf state.links (natListGetAt state.openWires position)
        == unionFindRootOf state.links (natListGetAt state.openWires position)) = true :=
    decide_eq_true rfl
  show unionFindRootOf
      (unionFindJoin
        (unionFindJoin state.links (natListGetAt state.openWires position)
          (natListGetAt state.openWires (position + 1)))
        state.nextFresh (natListGetAt state.openWires position))
      state.nextFresh
    = unionFindRootOf state.links (natListGetAt state.openWires (position + 1))
  rw [unionFindRootOf_unionFindJoin
      (unionFindJoin state.links (natListGetAt state.openWires position)
        (natListGetAt state.openWires (position + 1)))
      state.nextFresh (natListGetAt state.openWires position) state.nextFresh forestMerged,
    if_pos selfGuardOuter,
    unionFindRootOf_unionFindJoin state.links (natListGetAt state.openWires position)
      (natListGetAt state.openWires (position + 1)) (natListGetAt state.openWires position)
      forest,
    if_pos selfGuardInner]

/-- ★ **Old nodes keep their merged roots through the cap.**  The event join's child is the
fresh event node, which never lies on a chain from a node whose merged root is old. -/
theorem stepCapArc_root_old (state : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (nfPos : 0 < state.nextFresh)
    (node : Nat)
    (mergedRootBelow :
      unionFindRootOf
          (unionFindJoin state.links (natListGetAt state.openWires position)
            (natListGetAt state.openWires (position + 1)))
          node
        < state.nextFresh) :
    unionFindRootOf (stepCapArc state position).links node
      = unionFindRootOf
          (unionFindJoin state.links (natListGetAt state.openWires position)
            (natListGetAt state.openWires (position + 1)))
          node := by
  have forestMerged :
      isUnionFindForest (unionFindJoin state.links (natListGetAt state.openWires position)
        (natListGetAt state.openWires (position + 1))) :=
    isUnionFindForest_unionFindJoin state.links (natListGetAt state.openWires position)
      (natListGetAt state.openWires (position + 1)) forest
  have mergedChildrenBelow :
      ∀ edge ∈ unionFindJoin state.links (natListGetAt state.openWires position)
          (natListGetAt state.openWires (position + 1)),
        edge.1 < state.nextFresh :=
    fun edge edgeInJoin =>
      (capMerge_all_below state position fresh nfPos edge edgeInJoin).1
  have rootMergedEvent :
      unionFindRootOf
          (unionFindJoin state.links (natListGetAt state.openWires position)
            (natListGetAt state.openWires (position + 1)))
          state.nextFresh
        = state.nextFresh :=
    unionFindRootOf_of_parentless _ state.nextFresh
      (unionFindParent_none_of_lt state.nextFresh _ mergedChildrenBelow state.nextFresh
        (Nat.le_refl _))
  have guardFalse :
      ¬ (state.nextFresh
          == unionFindRootOf
              (unionFindJoin state.links (natListGetAt state.openWires position)
                (natListGetAt state.openWires (position + 1)))
              node) = true :=
    fun isTrue => Bool.noConfusion (beq_false_of_lt mergedRootBelow ▸ isTrue)
  show unionFindRootOf
      (unionFindJoin
        (unionFindJoin state.links (natListGetAt state.openWires position)
          (natListGetAt state.openWires (position + 1)))
        state.nextFresh (natListGetAt state.openWires position))
      node
    = unionFindRootOf
        (unionFindJoin state.links (natListGetAt state.openWires position)
          (natListGetAt state.openWires (position + 1)))
        node
  rw [unionFindRootOf_unionFindJoin
      (unionFindJoin state.links (natListGetAt state.openWires position)
        (natListGetAt state.openWires (position + 1)))
      state.nextFresh (natListGetAt state.openWires position) node forestMerged,
    rootMergedEvent, if_neg guardFalse]

/-- **Nodes at or above the cap's fresh allocation stay parentless** through the cap. -/
theorem stepCapArc_root_above (state : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh state)
    (node : Nat) (isAtOrAbove : state.nextFresh + 1 ≤ node) :
    unionFindRootOf (stepCapArc state position).links node = node :=
  unionFindRootOf_of_parentless _ node
    (unionFindParent_none_of_freshNode (stepCapArc state position)
      (stepCapArc_arcStateFresh state position fresh) node isAtOrAbove)

/-- ★ **Per-root counts over OLD event nodes collapse to the merged links** — each old event's
merged root stays old, so the cap's event join is invisible to the count. -/
theorem stepCapArc_countOldEvents_congr (state : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (nfPos : 0 < state.nextFresh)
    (rootHere : Nat) (events : List Nat)
    (allEventsBelow : ∀ node ∈ events, node < state.nextFresh) :
    countEventsInRoot (stepCapArc state position).links rootHere events
      = countEventsInRoot
          (unionFindJoin state.links (natListGetAt state.openWires position)
            (natListGetAt state.openWires (position + 1)))
          rootHere events :=
  countEventsInRoot_congr_links (stepCapArc state position).links
    (unionFindJoin state.links (natListGetAt state.openWires position)
      (natListGetAt state.openWires (position + 1)))
    rootHere events
    (fun eventNode eventInList =>
      stepCapArc_root_old state position fresh forest nfPos eventNode
        (capMerge_root_below state position fresh nfPos eventNode
          (allEventsBelow eventNode eventInList)))

/-! ## Honesty marker -/

/-- **Honesty marker — the cap root atlas is SHIPPED (ARC-2b brick iii-1d-beta1).**  Roots
through one cap step over the MERGED links `unionFindJoin links leftWire rightWire`: the
merged edges stay old (`capMerge_all_below`), merged roots of old nodes stay old
(`capMerge_root_below`), the cap's event node roots at the right wire's old root
(`stepCapArc_root_event`), old nodes keep their merged roots (`stepCapArc_root_old`), the
range above stays parentless (`stepCapArc_root_above`), and old-event counts collapse to the
merged links (`stepCapArc_countOldEvents_congr`).  The merged links are the ORDER-SHARED part:
both run orders of a mixed swap consume the same wire values, so the mixed atlases (beta2+)
compose these with the alpha1 cup atlas at the appropriate mid states.  NOT yet shipped: the
mixed two-step simulations (cup-cap / cap-cup / cap-cap, the last with the loop-transfer
crossing case) and the dispatcher.  `= true`. -/
def fxMode_hasArcCapRootAtlas : Bool := true

end FX1Poly.Polygraph
