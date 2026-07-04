import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcFreshSelfSimulation

/-! # ArcCupRootAtlas — roots of a cup's fresh triple, one and two cups deep (ARC-2b brick iii-1d-alpha1)

The two-step core simulation compares the two run orders of a disjoint-window swap.  For the
CUP x CUP arity case the two orders produce LITERALLY IDENTICAL link lists — `stepCupArc`'s
joins read only `nextFresh`, never the position — so the entire simulation content concentrates
in one question: what are the ROOTS of the double-cup link list?  This brick ships that atlas:

  * after ONE cup, each of the three fresh nodes (`nextFresh`, `+1`, `+2`) roots at the right
    leg `nextFresh + 1` (the two joins chain leftLeg -> rightLeg and eventNode -> rightLeg);
  * after TWO cups, the first cup's triple still roots at `nextFresh + 1` (the second cup's
    joins never touch a root below its own base), and the second cup's triple roots at
    `nextFresh + 4`;
  * OLD nodes keep their original roots through both cups, so per-root event counts over the
    double-cup links collapse to counts over the original links (`cupPair_countOldEvents_congr`);
  * nodes at or above both triples stay parentless.

The CUP x CUP `ArcStepSimCount` assembly (next brick) reads every field off this atlas plus the
iii-1a window-commutation kit and the iii-1b transposition interface.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- `(a == b) = false` from `a < b` — the mirror of `beq_false_of_lt` (which gives
`(b == a) = false`). -/
theorem beq_false_of_lt_left {lowValue highValue : Nat} (isBelow : lowValue < highValue) :
    (lowValue == highValue) = false := by
  apply decide_eq_false
  intro valuesEqual
  exact absurd valuesEqual (Nat.ne_of_lt isBelow)

/-! ## One cup deep — the fresh triple roots at the right leg -/

/-- **The cup's left leg roots at the right leg.**  The inner join records
`leftLeg -> rightLeg`; the outer join (event node into the component) does not move it. -/
theorem stepCupArc_root_leftLeg (state : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links) :
    unionFindRootOf (stepCupArc state position).links state.nextFresh
      = state.nextFresh + 1 := by
  have rootLeftLegBase : unionFindRootOf state.links state.nextFresh = state.nextFresh :=
    unionFindRootOf_of_parentless state.links state.nextFresh
      (unionFindParent_none_of_freshNode state fresh state.nextFresh (Nat.le_refl _))
  have rootRightLegBase :
      unionFindRootOf state.links (state.nextFresh + 1) = state.nextFresh + 1 :=
    unionFindRootOf_of_parentless state.links (state.nextFresh + 1)
      (unionFindParent_none_of_freshNode state fresh (state.nextFresh + 1) (Nat.le_add_right _ 1))
  have forestInner :
      isUnionFindForest (unionFindJoin state.links state.nextFresh (state.nextFresh + 1)) :=
    isUnionFindForest_unionFindJoin state.links state.nextFresh (state.nextFresh + 1) forest
  have twoAbove : state.nextFresh < state.nextFresh + 2 :=
    Nat.lt_add_of_pos_right (by decide)
  have rightLegBelowEventNode : state.nextFresh + 1 < state.nextFresh + 2 :=
    Nat.add_lt_add_left (by decide) state.nextFresh
  have innerChildrenBelow :
      ∀ edge ∈ unionFindJoin state.links state.nextFresh (state.nextFresh + 1),
        edge.1 < state.nextFresh + 2 :=
    fun edge edgeInJoin =>
      (unionFindJoin_all_lt (state.nextFresh + 2) state.links state.nextFresh
        (state.nextFresh + 1)
        (fun linkEdge linkEdgeInLinks =>
          ⟨Nat.lt_trans (fresh.2.1 linkEdge linkEdgeInLinks).1 twoAbove,
            Nat.lt_trans (fresh.2.1 linkEdge linkEdgeInLinks).2 twoAbove⟩)
        (by rw [rootLeftLegBase]; exact twoAbove)
        (by rw [rootRightLegBase]; exact rightLegBelowEventNode)
        edge edgeInJoin).1
  have rootInnerEventNode :
      unionFindRootOf (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
        (state.nextFresh + 2) = state.nextFresh + 2 :=
    unionFindRootOf_of_parentless _ (state.nextFresh + 2)
      (unionFindParent_none_of_lt (state.nextFresh + 2) _ innerChildrenBelow
        (state.nextFresh + 2) (Nat.le_refl _))
  have selfGuardBase :
      (unionFindRootOf state.links state.nextFresh
        == unionFindRootOf state.links state.nextFresh) = true := decide_eq_true rfl
  have rootInnerLeftLeg :
      unionFindRootOf (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
        state.nextFresh = state.nextFresh + 1 := by
    rw [unionFindRootOf_unionFindJoin state.links state.nextFresh (state.nextFresh + 1)
        state.nextFresh forest,
      if_pos selfGuardBase, rootRightLegBase]
  have guardFalse : ¬ (state.nextFresh + 2 == state.nextFresh + 1) = true :=
    fun isTrue => Bool.noConfusion (beq_false_of_lt rightLegBelowEventNode ▸ isTrue)
  show unionFindRootOf
      (unionFindJoin (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
        (state.nextFresh + 2) state.nextFresh) state.nextFresh
    = state.nextFresh + 1
  rw [unionFindRootOf_unionFindJoin
      (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
      (state.nextFresh + 2) state.nextFresh state.nextFresh forestInner,
    rootInnerEventNode, rootInnerLeftLeg, if_neg guardFalse]

/-- **The cup's right leg is its own root** — the component representative both joins point
into. -/
theorem stepCupArc_root_rightLeg (state : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links) :
    unionFindRootOf (stepCupArc state position).links (state.nextFresh + 1)
      = state.nextFresh + 1 := by
  have rootLeftLegBase : unionFindRootOf state.links state.nextFresh = state.nextFresh :=
    unionFindRootOf_of_parentless state.links state.nextFresh
      (unionFindParent_none_of_freshNode state fresh state.nextFresh (Nat.le_refl _))
  have rootRightLegBase :
      unionFindRootOf state.links (state.nextFresh + 1) = state.nextFresh + 1 :=
    unionFindRootOf_of_parentless state.links (state.nextFresh + 1)
      (unionFindParent_none_of_freshNode state fresh (state.nextFresh + 1) (Nat.le_add_right _ 1))
  have forestInner :
      isUnionFindForest (unionFindJoin state.links state.nextFresh (state.nextFresh + 1)) :=
    isUnionFindForest_unionFindJoin state.links state.nextFresh (state.nextFresh + 1) forest
  have twoAbove : state.nextFresh < state.nextFresh + 2 :=
    Nat.lt_add_of_pos_right (by decide)
  have rightLegBelowEventNode : state.nextFresh + 1 < state.nextFresh + 2 :=
    Nat.add_lt_add_left (by decide) state.nextFresh
  have leftLegBelowRightLeg : state.nextFresh < state.nextFresh + 1 :=
    Nat.lt_add_of_pos_right (by decide)
  have innerChildrenBelow :
      ∀ edge ∈ unionFindJoin state.links state.nextFresh (state.nextFresh + 1),
        edge.1 < state.nextFresh + 2 :=
    fun edge edgeInJoin =>
      (unionFindJoin_all_lt (state.nextFresh + 2) state.links state.nextFresh
        (state.nextFresh + 1)
        (fun linkEdge linkEdgeInLinks =>
          ⟨Nat.lt_trans (fresh.2.1 linkEdge linkEdgeInLinks).1 twoAbove,
            Nat.lt_trans (fresh.2.1 linkEdge linkEdgeInLinks).2 twoAbove⟩)
        (by rw [rootLeftLegBase]; exact twoAbove)
        (by rw [rootRightLegBase]; exact rightLegBelowEventNode)
        edge edgeInJoin).1
  have rootInnerEventNode :
      unionFindRootOf (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
        (state.nextFresh + 2) = state.nextFresh + 2 :=
    unionFindRootOf_of_parentless _ (state.nextFresh + 2)
      (unionFindParent_none_of_lt (state.nextFresh + 2) _ innerChildrenBelow
        (state.nextFresh + 2) (Nat.le_refl _))
  have leftNotRightGuard : ¬ (state.nextFresh == state.nextFresh + 1) = true :=
    fun isTrue => Bool.noConfusion (beq_false_of_lt_left leftLegBelowRightLeg ▸ isTrue)
  have rootInnerRightLeg :
      unionFindRootOf (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
        (state.nextFresh + 1) = state.nextFresh + 1 := by
    rw [unionFindRootOf_unionFindJoin state.links state.nextFresh (state.nextFresh + 1)
        (state.nextFresh + 1) forest, rootLeftLegBase, rootRightLegBase,
      if_neg leftNotRightGuard]
  have guardFalse : ¬ (state.nextFresh + 2 == state.nextFresh + 1) = true :=
    fun isTrue => Bool.noConfusion (beq_false_of_lt rightLegBelowEventNode ▸ isTrue)
  show unionFindRootOf
      (unionFindJoin (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
        (state.nextFresh + 2) state.nextFresh) (state.nextFresh + 1)
    = state.nextFresh + 1
  rw [unionFindRootOf_unionFindJoin
      (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
      (state.nextFresh + 2) state.nextFresh (state.nextFresh + 1) forestInner,
    rootInnerEventNode, rootInnerRightLeg, if_neg guardFalse]

/-- **The cup's event node roots at the right leg** — the outer join sends it into the leg
component. -/
theorem stepCupArc_root_eventNode (state : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links) :
    unionFindRootOf (stepCupArc state position).links (state.nextFresh + 2)
      = state.nextFresh + 1 := by
  have rootLeftLegBase : unionFindRootOf state.links state.nextFresh = state.nextFresh :=
    unionFindRootOf_of_parentless state.links state.nextFresh
      (unionFindParent_none_of_freshNode state fresh state.nextFresh (Nat.le_refl _))
  have rootRightLegBase :
      unionFindRootOf state.links (state.nextFresh + 1) = state.nextFresh + 1 :=
    unionFindRootOf_of_parentless state.links (state.nextFresh + 1)
      (unionFindParent_none_of_freshNode state fresh (state.nextFresh + 1) (Nat.le_add_right _ 1))
  have forestInner :
      isUnionFindForest (unionFindJoin state.links state.nextFresh (state.nextFresh + 1)) :=
    isUnionFindForest_unionFindJoin state.links state.nextFresh (state.nextFresh + 1) forest
  have twoAbove : state.nextFresh < state.nextFresh + 2 :=
    Nat.lt_add_of_pos_right (by decide)
  have rightLegBelowEventNode : state.nextFresh + 1 < state.nextFresh + 2 :=
    Nat.add_lt_add_left (by decide) state.nextFresh
  have innerChildrenBelow :
      ∀ edge ∈ unionFindJoin state.links state.nextFresh (state.nextFresh + 1),
        edge.1 < state.nextFresh + 2 :=
    fun edge edgeInJoin =>
      (unionFindJoin_all_lt (state.nextFresh + 2) state.links state.nextFresh
        (state.nextFresh + 1)
        (fun linkEdge linkEdgeInLinks =>
          ⟨Nat.lt_trans (fresh.2.1 linkEdge linkEdgeInLinks).1 twoAbove,
            Nat.lt_trans (fresh.2.1 linkEdge linkEdgeInLinks).2 twoAbove⟩)
        (by rw [rootLeftLegBase]; exact twoAbove)
        (by rw [rootRightLegBase]; exact rightLegBelowEventNode)
        edge edgeInJoin).1
  have rootInnerEventNode :
      unionFindRootOf (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
        (state.nextFresh + 2) = state.nextFresh + 2 :=
    unionFindRootOf_of_parentless _ (state.nextFresh + 2)
      (unionFindParent_none_of_lt (state.nextFresh + 2) _ innerChildrenBelow
        (state.nextFresh + 2) (Nat.le_refl _))
  have selfGuardBase :
      (unionFindRootOf state.links state.nextFresh
        == unionFindRootOf state.links state.nextFresh) = true := decide_eq_true rfl
  have rootInnerLeftLeg :
      unionFindRootOf (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
        state.nextFresh = state.nextFresh + 1 := by
    rw [unionFindRootOf_unionFindJoin state.links state.nextFresh (state.nextFresh + 1)
        state.nextFresh forest,
      if_pos selfGuardBase, rootRightLegBase]
  have selfGuardInnerEvent :
      (unionFindRootOf (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
          (state.nextFresh + 2)
        == unionFindRootOf (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
          (state.nextFresh + 2)) = true := decide_eq_true rfl
  show unionFindRootOf
      (unionFindJoin (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
        (state.nextFresh + 2) state.nextFresh) (state.nextFresh + 2)
    = state.nextFresh + 1
  rw [unionFindRootOf_unionFindJoin
      (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
      (state.nextFresh + 2) state.nextFresh (state.nextFresh + 2) forestInner,
    if_pos selfGuardInnerEvent, rootInnerLeftLeg]

/-! ## Two cups deep — both triples, old nodes, and the range above -/

/-- ★ **The first cup's triple still roots at `nextFresh + 1` after the second cup** — the
second cup's joins act at its own base `nextFresh + 3` and never move a root below it. -/
theorem cupPair_root_firstBlock (state : ArcWireState) (positionFirst positionSecond : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (offset : Nat) (isInFirst : offset < 3) :
    unionFindRootOf (stepCupArc (stepCupArc state positionFirst) positionSecond).links
      (state.nextFresh + offset) = state.nextFresh + 1 := by
  have freshMid : ArcStateFresh (stepCupArc state positionFirst) :=
    stepCupArc_arcStateFresh state positionFirst fresh
  have forestMid : isUnionFindForest (stepCupArc state positionFirst).links :=
    isUnionFindForest_stepCupArc state positionFirst forest
  have rootMid :
      unionFindRootOf (stepCupArc state positionFirst).links (state.nextFresh + offset)
        = state.nextFresh + 1 := by
    match offset, isInFirst with
    | 0, _ => exact stepCupArc_root_leftLeg state positionFirst fresh forest
    | 1, _ => exact stepCupArc_root_rightLeg state positionFirst fresh forest
    | 2, _ => exact stepCupArc_root_eventNode state positionFirst fresh forest
    | offsetRest + 3, absurdBound =>
        exact absurd
          (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ absurdBound)))
          (Nat.not_succ_le_zero offsetRest)
  have rootMidBelow :
      unionFindRootOf (stepCupArc state positionFirst).links (state.nextFresh + offset)
        < (stepCupArc state positionFirst).nextFresh := by
    rw [rootMid]
    show state.nextFresh + 1 < state.nextFresh + 3
    exact Nat.add_lt_add_left (by decide) state.nextFresh
  rw [unionFindRootOf_stepCupArc_old (stepCupArc state positionFirst) positionSecond freshMid
    forestMid (state.nextFresh + offset) rootMidBelow]
  exact rootMid

/-- ★ **The second cup's triple roots at `nextFresh + 4`** — the one-cup atlas applied at the
mid state, whose fresh base is `nextFresh + 3`. -/
theorem cupPair_root_secondBlock (state : ArcWireState) (positionFirst positionSecond : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (offset : Nat) (isInSecond : offset < 3) :
    unionFindRootOf (stepCupArc (stepCupArc state positionFirst) positionSecond).links
      (state.nextFresh + 3 + offset) = state.nextFresh + 4 := by
  have freshMid : ArcStateFresh (stepCupArc state positionFirst) :=
    stepCupArc_arcStateFresh state positionFirst fresh
  have forestMid : isUnionFindForest (stepCupArc state positionFirst).links :=
    isUnionFindForest_stepCupArc state positionFirst forest
  match offset, isInSecond with
  | 0, _ =>
      exact stepCupArc_root_leftLeg (stepCupArc state positionFirst) positionSecond
        freshMid forestMid
  | 1, _ =>
      exact stepCupArc_root_rightLeg (stepCupArc state positionFirst) positionSecond
        freshMid forestMid
  | 2, _ =>
      exact stepCupArc_root_eventNode (stepCupArc state positionFirst) positionSecond
        freshMid forestMid
  | offsetRest + 3, absurdBound =>
      exact absurd
        (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ absurdBound)))
        (Nat.not_succ_le_zero offsetRest)

/-- ★ **Old nodes keep their roots through both cups** — `unionFindRootOf_stepCupArc_old`
transported twice (each cup's joins only touch its own fresh triple). -/
theorem cupPair_root_old (state : ArcWireState) (positionFirst positionSecond : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (node : Nat) (rootBelow : unionFindRootOf state.links node < state.nextFresh) :
    unionFindRootOf (stepCupArc (stepCupArc state positionFirst) positionSecond).links node
      = unionFindRootOf state.links node := by
  have freshMid : ArcStateFresh (stepCupArc state positionFirst) :=
    stepCupArc_arcStateFresh state positionFirst fresh
  have forestMid : isUnionFindForest (stepCupArc state positionFirst).links :=
    isUnionFindForest_stepCupArc state positionFirst forest
  have rootStillBelow :
      unionFindRootOf (stepCupArc state positionFirst).links node
        < (stepCupArc state positionFirst).nextFresh := by
    rw [unionFindRootOf_stepCupArc_old state positionFirst fresh forest node rootBelow]
    show unionFindRootOf state.links node < state.nextFresh + 3
    exact Nat.lt_trans rootBelow (Nat.lt_add_of_pos_right (by decide))
  rw [unionFindRootOf_stepCupArc_old (stepCupArc state positionFirst) positionSecond freshMid
      forestMid node rootStillBelow,
    unionFindRootOf_stepCupArc_old state positionFirst fresh forest node rootBelow]

/-- **Nodes at or above both triples stay parentless** through the two cups. -/
theorem cupPair_root_aboveBlocks (state : ArcWireState) (positionFirst positionSecond : Nat)
    (fresh : ArcStateFresh state)
    (node : Nat) (isAtOrAbove : state.nextFresh + 6 ≤ node) :
    unionFindRootOf (stepCupArc (stepCupArc state positionFirst) positionSecond).links node
      = node :=
  unionFindRootOf_of_parentless _ node
    (unionFindParent_none_of_freshNode (stepCupArc (stepCupArc state positionFirst) positionSecond)
      (stepCupArc_arcStateFresh (stepCupArc state positionFirst) positionSecond
        (stepCupArc_arcStateFresh state positionFirst fresh))
      node isAtOrAbove)

/-- ★ **Per-root counts over OLD event nodes collapse to the original links** — each old
event's root is untouched by the two cups (`cupPair_root_old` on a root that freshness keeps
below `nextFresh`), so the count congruence rewrites the double-cup links away. -/
theorem cupPair_countOldEvents_congr (state : ArcWireState) (positionFirst positionSecond : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (rootHere : Nat) (events : List Nat)
    (allEventsBelow : ∀ node ∈ events, node < state.nextFresh) :
    countEventsInRoot (stepCupArc (stepCupArc state positionFirst) positionSecond).links
        rootHere events
      = countEventsInRoot state.links rootHere events :=
  countEventsInRoot_congr_links
    (stepCupArc (stepCupArc state positionFirst) positionSecond).links state.links rootHere
    events
    (fun eventNode eventInList =>
      cupPair_root_old state positionFirst positionSecond fresh forest eventNode
        (unionFindRootOf_lt_of_fresh state.links state.nextFresh
          (fun edge edgeInLinks => (fresh.2.1 edge edgeInLinks).2)
          eventNode (allEventsBelow eventNode eventInList)))

/-! ## Honesty marker -/

/-- **Honesty marker — the cup root atlas is SHIPPED (ARC-2b brick iii-1d-alpha1).**  Roots of
a cup's fresh triple after one cup (`stepCupArc_root_leftLeg`/`_rightLeg`/`_eventNode`, all at
the right leg `nextFresh + 1`) and after two cups (`cupPair_root_firstBlock` at `nextFresh + 1`,
`cupPair_root_secondBlock` at `nextFresh + 4`), old-node locality through both cups
(`cupPair_root_old`), the parentless range above (`cupPair_root_aboveBlocks`), and the old-event
count collapse (`cupPair_countOldEvents_congr`).  KEY structural fact consumed by the next
brick: `stepCupArc`'s links read only `nextFresh` — never the position — so the two run orders
of a CUP x CUP swap produce IDENTICAL link lists and the whole two-step simulation reduces to
this atlas.  NOT yet shipped: the CUP x CUP `ArcStepSimCount` assembly (openMap via the iii-1a
kit, rootComm/counts via this atlas), and the cap-side atlas for the mixed arity cases.
`= true`. -/
def fxMode_hasArcCupRootAtlas : Bool := true

end FX1Poly.Polygraph
