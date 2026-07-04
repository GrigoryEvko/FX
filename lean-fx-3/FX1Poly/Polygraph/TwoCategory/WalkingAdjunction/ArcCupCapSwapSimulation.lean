import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapRootAtlas
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingWindowSuffix

/-! # ArcCupCapSwapSimulation — the CUP x CAP two-step core simulation (ARC-2b brick iii-1d-beta2)

The first MIXED arity case: the low atom is a cup, the high atom a cap.  Order S fires the
cup at `positionLow` then the cap at `gap + 2 + positionLow` (the cup produced two wires, so
the cap's window slid up by two); order T fires the cap first at `gap + positionLow` then the
cup at `positionLow`.  The reconciling renaming is the fresh-block transposition at widths
`3, 1` (the cup allocates three identifiers, the cap one).

The load-bearing semantic fact: both orders consume the SAME wire values — the cap's reads in
order S sit past the cup's inserted pair, so the `pastBlock` shift collapses them to the
original reads (`natListGetAt_pastInsertedPair`).  Consequently both orders build the SAME
merged component `unionFindJoin links leftRead rightRead`, and every field reduces to the cup
atlas (alpha1), the cap atlas (beta1), and the shared merged links:

  * S-side roots: the cup's triple still roots at `nextFresh + 1` through the cap's joins, the
    cap's event roots at the right wire's old root, old nodes keep their MERGED roots;
  * T-side roots: the cap's event keeps its old root through the cup, the cup's triple (based
    at `nextFresh + 1`) roots at `nextFresh + 2`, old nodes keep their merged roots;
  * the transposition exchanges the two allocation blocks and fixes everything else;
  * `openMap` is the iii-1a insert-below/remove-above commutation; `loopsEq` is the
    same-component test's stability through the cup (old roots untouched).

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- `List.map` on a two-element literal, exposed as a rewrite (definitional). -/
private theorem mapPairValues (rename : Nat → Nat) (firstValue secondValue : Nat) :
    List.map rename [firstValue, secondValue] = [rename firstValue, rename secondValue] := rfl

/-! ## Reading past the inserted pair — the order-S cap consumes the ORIGINAL wire values -/

/-- **The cap's left read in order S collapses to the original read.**  Reading at
`gap + 2 + positionLow` after splicing a two-element block at `positionLow` is reading at
`gap + positionLow` before — the iii-1a `pastBlock` law with the indices commuted into the
swap discipline's spelling. -/
theorem natListGetAt_pastInsertedPair (wires : List Nat) (positionLow gap : Nat)
    (valueA valueB : Nat) (lowInRange : positionLow ≤ wires.length) :
    natListGetAt (natListInsertAt wires positionLow [valueA, valueB]) (gap + 2 + positionLow)
      = natListGetAt wires (gap + positionLow) := by
  rw [Nat.add_comm (gap + 2) positionLow, ← Nat.add_assoc positionLow gap 2,
    Nat.add_comm gap positionLow]
  exact natListGetAt_natListInsertAt_pastBlock wires positionLow [valueA, valueB] gap
    lowInRange

/-- **The cap's right read in order S collapses to the original read** — the successor-index
companion of `natListGetAt_pastInsertedPair`. -/
theorem natListGetAt_pastInsertedPair_succ (wires : List Nat) (positionLow gap : Nat)
    (valueA valueB : Nat) (lowInRange : positionLow ≤ wires.length) :
    natListGetAt (natListInsertAt wires positionLow [valueA, valueB])
        (gap + 2 + positionLow + 1)
      = natListGetAt wires (gap + positionLow + 1) := by
  rw [Nat.add_right_comm (gap + 2) positionLow 1, Nat.add_comm (gap + 2 + 1) positionLow,
    Nat.add_right_comm gap positionLow 1, Nat.add_comm (gap + 1) positionLow]
  exact natListGetAt_natListInsertAt_pastBlock wires positionLow [valueA, valueB] (gap + 1)
    lowInRange

/-- **The order-S links exposed over the ORIGINAL reads.**  The cap's join-of-join over the
post-cup state, with both wire reads collapsed past the inserted pair. -/
theorem cupCapSwap_linksS (state : ArcWireState) (gap positionLow : Nat)
    (lowInRange : positionLow ≤ state.openWires.length) :
    (stepCapArc (stepCupArc state positionLow) (gap + 2 + positionLow)).links
      = unionFindJoin
          (unionFindJoin (stepCupArc state positionLow).links
            (natListGetAt state.openWires (gap + positionLow))
            (natListGetAt state.openWires (gap + positionLow + 1)))
          (state.nextFresh + 3)
          (natListGetAt state.openWires (gap + positionLow)) := by
  show unionFindJoin
      (unionFindJoin (stepCupArc state positionLow).links
        (natListGetAt (natListInsertAt state.openWires positionLow
          [state.nextFresh, state.nextFresh + 1]) (gap + 2 + positionLow))
        (natListGetAt (natListInsertAt state.openWires positionLow
          [state.nextFresh, state.nextFresh + 1]) (gap + 2 + positionLow + 1)))
      (state.nextFresh + 3)
      (natListGetAt (natListInsertAt state.openWires positionLow
        [state.nextFresh, state.nextFresh + 1]) (gap + 2 + positionLow))
    = unionFindJoin
        (unionFindJoin (stepCupArc state positionLow).links
          (natListGetAt state.openWires (gap + positionLow))
          (natListGetAt state.openWires (gap + positionLow + 1)))
        (state.nextFresh + 3)
        (natListGetAt state.openWires (gap + positionLow))
  rw [natListGetAt_pastInsertedPair state.openWires positionLow gap state.nextFresh
      (state.nextFresh + 1) lowInRange,
    natListGetAt_pastInsertedPair_succ state.openWires positionLow gap state.nextFresh
      (state.nextFresh + 1) lowInRange]

/-! ## Order-S roots — through the cup, then the cap -/

/-- **Old nodes keep their merged roots through order S.**  The cup leaves old roots alone, so
the S-side merge behaves exactly like the shared merge; the cap's event join is invisible to
old-rooted nodes. -/
theorem cupCapSwapS_root_old (state : ArcWireState)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (nfPos : 0 < state.nextFresh) (gap positionLow : Nat)
    (lowInRange : positionLow ≤ state.openWires.length)
    (node : Nat) (nodeBelow : node < state.nextFresh) :
    unionFindRootOf
        (stepCapArc (stepCupArc state positionLow) (gap + 2 + positionLow)).links node
      = unionFindRootOf
          (unionFindJoin state.links (natListGetAt state.openWires (gap + positionLow))
            (natListGetAt state.openWires (gap + positionLow + 1)))
          node := by
  have forestCupMid : isUnionFindForest (stepCupArc state positionLow).links :=
    isUnionFindForest_stepCupArc state positionLow forest
  have freshCupMid : ArcStateFresh (stepCupArc state positionLow) :=
    stepCupArc_arcStateFresh state positionLow fresh
  have linkParentsBelow : ∀ edge ∈ state.links, edge.2 < state.nextFresh :=
    fun edge edgeInLinks => (fresh.2.1 edge edgeInLinks).2
  have rootLeftBelow :
      unionFindRootOf state.links (natListGetAt state.openWires (gap + positionLow))
        < state.nextFresh :=
    unionFindRootOf_lt_of_fresh state.links state.nextFresh linkParentsBelow _
      (natListGetAt_lt state.nextFresh nfPos state.openWires (gap + positionLow) fresh.1)
  have rootRightBelow :
      unionFindRootOf state.links (natListGetAt state.openWires (gap + positionLow + 1))
        < state.nextFresh :=
    unionFindRootOf_lt_of_fresh state.links state.nextFresh linkParentsBelow _
      (natListGetAt_lt state.nextFresh nfPos state.openWires (gap + positionLow + 1) fresh.1)
  have rootNodeBelow : unionFindRootOf state.links node < state.nextFresh :=
    unionFindRootOf_lt_of_fresh state.links state.nextFresh linkParentsBelow node nodeBelow
  have collapseLeft :
      unionFindRootOf (stepCupArc state positionLow).links
          (natListGetAt state.openWires (gap + positionLow))
        = unionFindRootOf state.links (natListGetAt state.openWires (gap + positionLow)) :=
    unionFindRootOf_stepCupArc_old state positionLow fresh forest _ rootLeftBelow
  have collapseRight :
      unionFindRootOf (stepCupArc state positionLow).links
          (natListGetAt state.openWires (gap + positionLow + 1))
        = unionFindRootOf state.links (natListGetAt state.openWires (gap + positionLow + 1)) :=
    unionFindRootOf_stepCupArc_old state positionLow fresh forest _ rootRightBelow
  have collapseNode :
      unionFindRootOf (stepCupArc state positionLow).links node
        = unionFindRootOf state.links node :=
    unionFindRootOf_stepCupArc_old state positionLow fresh forest node rootNodeBelow
  have forestMergedS :
      isUnionFindForest (unionFindJoin (stepCupArc state positionLow).links
        (natListGetAt state.openWires (gap + positionLow))
        (natListGetAt state.openWires (gap + positionLow + 1))) :=
    isUnionFindForest_unionFindJoin _ _ _ forestCupMid
  have mergedSChildrenBelow :
      ∀ edge ∈ unionFindJoin (stepCupArc state positionLow).links
          (natListGetAt state.openWires (gap + positionLow))
          (natListGetAt state.openWires (gap + positionLow + 1)),
        edge.1 < state.nextFresh + 3 :=
    fun edge edgeInJoin =>
      (unionFindJoin_all_lt (state.nextFresh + 3) (stepCupArc state positionLow).links _ _
        freshCupMid.2.1
        (by
          rw [collapseLeft]
          exact Nat.lt_trans rootLeftBelow (Nat.lt_add_of_pos_right (by decide)))
        (by
          rw [collapseRight]
          exact Nat.lt_trans rootRightBelow (Nat.lt_add_of_pos_right (by decide)))
        edge edgeInJoin).1
  have rootMergedSEvent :
      unionFindRootOf
          (unionFindJoin (stepCupArc state positionLow).links
            (natListGetAt state.openWires (gap + positionLow))
            (natListGetAt state.openWires (gap + positionLow + 1)))
          (state.nextFresh + 3)
        = state.nextFresh + 3 :=
    unionFindRootOf_of_parentless _ _
      (unionFindParent_none_of_lt (state.nextFresh + 3) _ mergedSChildrenBelow
        (state.nextFresh + 3) (Nat.le_refl _))
  have bridgeMerged :
      unionFindRootOf
          (unionFindJoin (stepCupArc state positionLow).links
            (natListGetAt state.openWires (gap + positionLow))
            (natListGetAt state.openWires (gap + positionLow + 1)))
          node
        = unionFindRootOf
            (unionFindJoin state.links (natListGetAt state.openWires (gap + positionLow))
              (natListGetAt state.openWires (gap + positionLow + 1)))
            node := by
    rw [unionFindRootOf_unionFindJoin (stepCupArc state positionLow).links
        (natListGetAt state.openWires (gap + positionLow))
        (natListGetAt state.openWires (gap + positionLow + 1)) node forestCupMid,
      unionFindRootOf_unionFindJoin state.links
        (natListGetAt state.openWires (gap + positionLow))
        (natListGetAt state.openWires (gap + positionLow + 1)) node forest,
      collapseLeft, collapseRight, collapseNode]
  have mergedRootBelow :
      unionFindRootOf
          (unionFindJoin state.links (natListGetAt state.openWires (gap + positionLow))
            (natListGetAt state.openWires (gap + positionLow + 1)))
          node
        < state.nextFresh :=
    capMerge_root_below state (gap + positionLow) fresh nfPos node nodeBelow
  have mergedRootBelowEvent :
      unionFindRootOf
          (unionFindJoin state.links (natListGetAt state.openWires (gap + positionLow))
            (natListGetAt state.openWires (gap + positionLow + 1)))
          node
        < state.nextFresh + 3 :=
    Nat.lt_trans mergedRootBelow (Nat.lt_add_of_pos_right (by decide))
  have guardFresh :
      ¬ (state.nextFresh + 3
          == unionFindRootOf
              (unionFindJoin state.links (natListGetAt state.openWires (gap + positionLow))
                (natListGetAt state.openWires (gap + positionLow + 1)))
              node) = true :=
    fun isTrue => Bool.noConfusion (beq_false_of_lt mergedRootBelowEvent ▸ isTrue)
  rw [cupCapSwap_linksS state gap positionLow lowInRange,
    unionFindRootOf_unionFindJoin
      (unionFindJoin (stepCupArc state positionLow).links
        (natListGetAt state.openWires (gap + positionLow))
        (natListGetAt state.openWires (gap + positionLow + 1)))
      (state.nextFresh + 3) (natListGetAt state.openWires (gap + positionLow)) node
      forestMergedS,
    rootMergedSEvent, bridgeMerged, if_neg guardFresh]

/-- **The cup's fresh triple still roots at `nextFresh + 1` through order S's cap** — the
cap's merge joins two OLD-rooted wires, so the triple's component is untouched, and the cap's
event join targets its own fresh node. -/
theorem cupCapSwapS_root_triple (state : ArcWireState)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (nfPos : 0 < state.nextFresh) (gap positionLow : Nat)
    (lowInRange : positionLow ≤ state.openWires.length)
    (tripleNode : Nat)
    (cupRootAtRightLeg :
      unionFindRootOf (stepCupArc state positionLow).links tripleNode
        = state.nextFresh + 1) :
    unionFindRootOf
        (stepCapArc (stepCupArc state positionLow) (gap + 2 + positionLow)).links tripleNode
      = state.nextFresh + 1 := by
  have forestCupMid : isUnionFindForest (stepCupArc state positionLow).links :=
    isUnionFindForest_stepCupArc state positionLow forest
  have freshCupMid : ArcStateFresh (stepCupArc state positionLow) :=
    stepCupArc_arcStateFresh state positionLow fresh
  have linkParentsBelow : ∀ edge ∈ state.links, edge.2 < state.nextFresh :=
    fun edge edgeInLinks => (fresh.2.1 edge edgeInLinks).2
  have rootLeftBelow :
      unionFindRootOf state.links (natListGetAt state.openWires (gap + positionLow))
        < state.nextFresh :=
    unionFindRootOf_lt_of_fresh state.links state.nextFresh linkParentsBelow _
      (natListGetAt_lt state.nextFresh nfPos state.openWires (gap + positionLow) fresh.1)
  have rootRightBelow :
      unionFindRootOf state.links (natListGetAt state.openWires (gap + positionLow + 1))
        < state.nextFresh :=
    unionFindRootOf_lt_of_fresh state.links state.nextFresh linkParentsBelow _
      (natListGetAt_lt state.nextFresh nfPos state.openWires (gap + positionLow + 1) fresh.1)
  have collapseLeft :
      unionFindRootOf (stepCupArc state positionLow).links
          (natListGetAt state.openWires (gap + positionLow))
        = unionFindRootOf state.links (natListGetAt state.openWires (gap + positionLow)) :=
    unionFindRootOf_stepCupArc_old state positionLow fresh forest _ rootLeftBelow
  have collapseRight :
      unionFindRootOf (stepCupArc state positionLow).links
          (natListGetAt state.openWires (gap + positionLow + 1))
        = unionFindRootOf state.links (natListGetAt state.openWires (gap + positionLow + 1)) :=
    unionFindRootOf_stepCupArc_old state positionLow fresh forest _ rootRightBelow
  have forestMergedS :
      isUnionFindForest (unionFindJoin (stepCupArc state positionLow).links
        (natListGetAt state.openWires (gap + positionLow))
        (natListGetAt state.openWires (gap + positionLow + 1))) :=
    isUnionFindForest_unionFindJoin _ _ _ forestCupMid
  have mergedSChildrenBelow :
      ∀ edge ∈ unionFindJoin (stepCupArc state positionLow).links
          (natListGetAt state.openWires (gap + positionLow))
          (natListGetAt state.openWires (gap + positionLow + 1)),
        edge.1 < state.nextFresh + 3 :=
    fun edge edgeInJoin =>
      (unionFindJoin_all_lt (state.nextFresh + 3) (stepCupArc state positionLow).links _ _
        freshCupMid.2.1
        (by
          rw [collapseLeft]
          exact Nat.lt_trans rootLeftBelow (Nat.lt_add_of_pos_right (by decide)))
        (by
          rw [collapseRight]
          exact Nat.lt_trans rootRightBelow (Nat.lt_add_of_pos_right (by decide)))
        edge edgeInJoin).1
  have rootMergedSEvent :
      unionFindRootOf
          (unionFindJoin (stepCupArc state positionLow).links
            (natListGetAt state.openWires (gap + positionLow))
            (natListGetAt state.openWires (gap + positionLow + 1)))
          (state.nextFresh + 3)
        = state.nextFresh + 3 :=
    unionFindRootOf_of_parentless _ _
      (unionFindParent_none_of_lt (state.nextFresh + 3) _ mergedSChildrenBelow
        (state.nextFresh + 3) (Nat.le_refl _))
  have rootMergedSTriple :
      unionFindRootOf
          (unionFindJoin (stepCupArc state positionLow).links
            (natListGetAt state.openWires (gap + positionLow))
            (natListGetAt state.openWires (gap + positionLow + 1)))
          tripleNode
        = state.nextFresh + 1 := by
    have rootLeftBelowRightLeg :
        unionFindRootOf state.links (natListGetAt state.openWires (gap + positionLow))
          < state.nextFresh + 1 :=
      Nat.lt_trans rootLeftBelow (Nat.lt_add_of_pos_right (by decide))
    have guardLeft :
        ¬ (unionFindRootOf state.links (natListGetAt state.openWires (gap + positionLow))
            == state.nextFresh + 1) = true :=
      fun isTrue =>
        Bool.noConfusion (beq_false_of_lt_left rootLeftBelowRightLeg ▸ isTrue)
    rw [unionFindRootOf_unionFindJoin (stepCupArc state positionLow).links
        (natListGetAt state.openWires (gap + positionLow))
        (natListGetAt state.openWires (gap + positionLow + 1)) tripleNode forestCupMid,
      collapseLeft, cupRootAtRightLeg, if_neg guardLeft]
  have oneBelowEventNode : state.nextFresh + 1 < state.nextFresh + 3 :=
    Nat.add_lt_add_left (by decide) state.nextFresh
  have guardOuter : ¬ (state.nextFresh + 3 == state.nextFresh + 1) = true :=
    fun isTrue => Bool.noConfusion (beq_false_of_lt oneBelowEventNode ▸ isTrue)
  rw [cupCapSwap_linksS state gap positionLow lowInRange,
    unionFindRootOf_unionFindJoin
      (unionFindJoin (stepCupArc state positionLow).links
        (natListGetAt state.openWires (gap + positionLow))
        (natListGetAt state.openWires (gap + positionLow + 1)))
      (state.nextFresh + 3) (natListGetAt state.openWires (gap + positionLow)) tripleNode
      forestMergedS,
    rootMergedSEvent, rootMergedSTriple, if_neg guardOuter]

/-- **Order S's cap event roots at the right wire's old root** — through the cup the right
wire's root is unchanged, and the cap hangs its event under the merged representative. -/
theorem cupCapSwapS_root_capEvent (state : ArcWireState)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (nfPos : 0 < state.nextFresh) (gap positionLow : Nat)
    (lowInRange : positionLow ≤ state.openWires.length) :
    unionFindRootOf
        (stepCapArc (stepCupArc state positionLow) (gap + 2 + positionLow)).links
        (state.nextFresh + 3)
      = unionFindRootOf state.links (natListGetAt state.openWires (gap + positionLow + 1))
    := by
  have forestCupMid : isUnionFindForest (stepCupArc state positionLow).links :=
    isUnionFindForest_stepCupArc state positionLow forest
  have freshCupMid : ArcStateFresh (stepCupArc state positionLow) :=
    stepCupArc_arcStateFresh state positionLow fresh
  have linkParentsBelow : ∀ edge ∈ state.links, edge.2 < state.nextFresh :=
    fun edge edgeInLinks => (fresh.2.1 edge edgeInLinks).2
  have rootLeftBelow :
      unionFindRootOf state.links (natListGetAt state.openWires (gap + positionLow))
        < state.nextFresh :=
    unionFindRootOf_lt_of_fresh state.links state.nextFresh linkParentsBelow _
      (natListGetAt_lt state.nextFresh nfPos state.openWires (gap + positionLow) fresh.1)
  have rootRightBelow :
      unionFindRootOf state.links (natListGetAt state.openWires (gap + positionLow + 1))
        < state.nextFresh :=
    unionFindRootOf_lt_of_fresh state.links state.nextFresh linkParentsBelow _
      (natListGetAt_lt state.nextFresh nfPos state.openWires (gap + positionLow + 1) fresh.1)
  have collapseLeft :
      unionFindRootOf (stepCupArc state positionLow).links
          (natListGetAt state.openWires (gap + positionLow))
        = unionFindRootOf state.links (natListGetAt state.openWires (gap + positionLow)) :=
    unionFindRootOf_stepCupArc_old state positionLow fresh forest _ rootLeftBelow
  have collapseRight :
      unionFindRootOf (stepCupArc state positionLow).links
          (natListGetAt state.openWires (gap + positionLow + 1))
        = unionFindRootOf state.links (natListGetAt state.openWires (gap + positionLow + 1)) :=
    unionFindRootOf_stepCupArc_old state positionLow fresh forest _ rootRightBelow
  have forestMergedS :
      isUnionFindForest (unionFindJoin (stepCupArc state positionLow).links
        (natListGetAt state.openWires (gap + positionLow))
        (natListGetAt state.openWires (gap + positionLow + 1))) :=
    isUnionFindForest_unionFindJoin _ _ _ forestCupMid
  have selfGuardOuter :
      (unionFindRootOf
          (unionFindJoin (stepCupArc state positionLow).links
            (natListGetAt state.openWires (gap + positionLow))
            (natListGetAt state.openWires (gap + positionLow + 1)))
          (state.nextFresh + 3)
        == unionFindRootOf
            (unionFindJoin (stepCupArc state positionLow).links
              (natListGetAt state.openWires (gap + positionLow))
              (natListGetAt state.openWires (gap + positionLow + 1)))
            (state.nextFresh + 3)) = true := decide_eq_true rfl
  have selfGuardInner :
      (unionFindRootOf (stepCupArc state positionLow).links
          (natListGetAt state.openWires (gap + positionLow))
        == unionFindRootOf (stepCupArc state positionLow).links
            (natListGetAt state.openWires (gap + positionLow))) = true := decide_eq_true rfl
  rw [cupCapSwap_linksS state gap positionLow lowInRange,
    unionFindRootOf_unionFindJoin
      (unionFindJoin (stepCupArc state positionLow).links
        (natListGetAt state.openWires (gap + positionLow))
        (natListGetAt state.openWires (gap + positionLow + 1)))
      (state.nextFresh + 3) (natListGetAt state.openWires (gap + positionLow))
      (state.nextFresh + 3) forestMergedS,
    if_pos selfGuardOuter,
    unionFindRootOf_unionFindJoin (stepCupArc state positionLow).links
      (natListGetAt state.openWires (gap + positionLow))
      (natListGetAt state.openWires (gap + positionLow + 1))
      (natListGetAt state.openWires (gap + positionLow)) forestCupMid,
    if_pos selfGuardInner, collapseRight]

/-- **Nodes at or above both allocations stay parentless through order S.** -/
theorem cupCapSwapS_root_above (state : ArcWireState)
    (fresh : ArcStateFresh state) (gap positionLow : Nat)
    (node : Nat) (isAtOrAbove : state.nextFresh + 4 ≤ node) :
    unionFindRootOf
        (stepCapArc (stepCupArc state positionLow) (gap + 2 + positionLow)).links node
      = node :=
  unionFindRootOf_of_parentless _ node
    (unionFindParent_none_of_freshNode
      (stepCapArc (stepCupArc state positionLow) (gap + 2 + positionLow))
      (stepCapArc_arcStateFresh (stepCupArc state positionLow) (gap + 2 + positionLow)
        (stepCupArc_arcStateFresh state positionLow fresh))
      node isAtOrAbove)

/-- **Order-S counts over OLD events collapse to the shared merged links.** -/
theorem cupCapSwapS_countOld (state : ArcWireState)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (nfPos : 0 < state.nextFresh) (gap positionLow : Nat)
    (lowInRange : positionLow ≤ state.openWires.length)
    (rootHere : Nat) (events : List Nat)
    (allEventsBelow : ∀ node ∈ events, node < state.nextFresh) :
    countEventsInRoot
        (stepCapArc (stepCupArc state positionLow) (gap + 2 + positionLow)).links
        rootHere events
      = countEventsInRoot
          (unionFindJoin state.links (natListGetAt state.openWires (gap + positionLow))
            (natListGetAt state.openWires (gap + positionLow + 1)))
          rootHere events :=
  countEventsInRoot_congr_links _ _ rootHere events
    (fun eventNode eventInList =>
      cupCapSwapS_root_old state fresh forest nfPos gap positionLow lowInRange eventNode
        (allEventsBelow eventNode eventInList))

/-! ## Order-T roots — through the cap, then the cup -/

/-- **Old nodes keep their merged roots through order T** — the cap atlas collapses the cap,
the cup leaves old roots alone. -/
theorem cupCapSwapT_root_old (state : ArcWireState)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (nfPos : 0 < state.nextFresh) (gap positionLow : Nat)
    (node : Nat) (nodeBelow : node < state.nextFresh) :
    unionFindRootOf
        (stepCupArc (stepCapArc state (gap + positionLow)) positionLow).links node
      = unionFindRootOf
          (unionFindJoin state.links (natListGetAt state.openWires (gap + positionLow))
            (natListGetAt state.openWires (gap + positionLow + 1)))
          node := by
  have freshCapMid : ArcStateFresh (stepCapArc state (gap + positionLow)) :=
    stepCapArc_arcStateFresh state (gap + positionLow) fresh
  have forestCapMid : isUnionFindForest (stepCapArc state (gap + positionLow)).links :=
    isUnionFindForest_stepCapArc state (gap + positionLow) forest
  have mergedRootBelow :
      unionFindRootOf
          (unionFindJoin state.links (natListGetAt state.openWires (gap + positionLow))
            (natListGetAt state.openWires (gap + positionLow + 1)))
          node
        < state.nextFresh :=
    capMerge_root_below state (gap + positionLow) fresh nfPos node nodeBelow
  have capOld :
      unionFindRootOf (stepCapArc state (gap + positionLow)).links node
        = unionFindRootOf
            (unionFindJoin state.links (natListGetAt state.openWires (gap + positionLow))
              (natListGetAt state.openWires (gap + positionLow + 1)))
            node :=
    stepCapArc_root_old state (gap + positionLow) fresh forest nfPos node mergedRootBelow
  have rootMidBelow :
      unionFindRootOf (stepCapArc state (gap + positionLow)).links node
        < state.nextFresh + 1 := by
    rw [capOld]
    exact Nat.lt_trans mergedRootBelow (Nat.lt_add_of_pos_right (by decide))
  exact Eq.trans
    (unionFindRootOf_stepCupArc_old (stepCapArc state (gap + positionLow)) positionLow
      freshCapMid forestCapMid node rootMidBelow)
    capOld

/-- **Order T's cap event keeps its old root through the cup** — it roots at the right wire's
old root, which is below every fresh allocation. -/
theorem cupCapSwapT_root_capEvent (state : ArcWireState)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (nfPos : 0 < state.nextFresh) (gap positionLow : Nat) :
    unionFindRootOf
        (stepCupArc (stepCapArc state (gap + positionLow)) positionLow).links
        state.nextFresh
      = unionFindRootOf state.links (natListGetAt state.openWires (gap + positionLow + 1))
    := by
  have freshCapMid : ArcStateFresh (stepCapArc state (gap + positionLow)) :=
    stepCapArc_arcStateFresh state (gap + positionLow) fresh
  have forestCapMid : isUnionFindForest (stepCapArc state (gap + positionLow)).links :=
    isUnionFindForest_stepCapArc state (gap + positionLow) forest
  have linkParentsBelow : ∀ edge ∈ state.links, edge.2 < state.nextFresh :=
    fun edge edgeInLinks => (fresh.2.1 edge edgeInLinks).2
  have rootRightBelow :
      unionFindRootOf state.links (natListGetAt state.openWires (gap + positionLow + 1))
        < state.nextFresh :=
    unionFindRootOf_lt_of_fresh state.links state.nextFresh linkParentsBelow _
      (natListGetAt_lt state.nextFresh nfPos state.openWires (gap + positionLow + 1) fresh.1)
  have capEventRoot :
      unionFindRootOf (stepCapArc state (gap + positionLow)).links state.nextFresh
        = unionFindRootOf state.links
            (natListGetAt state.openWires (gap + positionLow + 1)) :=
    stepCapArc_root_event state (gap + positionLow) fresh forest nfPos
  have rootMidBelow :
      unionFindRootOf (stepCapArc state (gap + positionLow)).links state.nextFresh
        < state.nextFresh + 1 := by
    rw [capEventRoot]
    exact Nat.lt_trans rootRightBelow (Nat.lt_add_of_pos_right (by decide))
  exact Eq.trans
    (unionFindRootOf_stepCupArc_old (stepCapArc state (gap + positionLow)) positionLow
      freshCapMid forestCapMid state.nextFresh rootMidBelow)
    capEventRoot

/-- **Nodes at or above both allocations stay parentless through order T.** -/
theorem cupCapSwapT_root_above (state : ArcWireState)
    (fresh : ArcStateFresh state) (gap positionLow : Nat)
    (node : Nat) (isAtOrAbove : state.nextFresh + 4 ≤ node) :
    unionFindRootOf
        (stepCupArc (stepCapArc state (gap + positionLow)) positionLow).links node
      = node :=
  unionFindRootOf_of_parentless _ node
    (unionFindParent_none_of_freshNode
      (stepCupArc (stepCapArc state (gap + positionLow)) positionLow)
      (stepCupArc_arcStateFresh (stepCapArc state (gap + positionLow)) positionLow
        (stepCapArc_arcStateFresh state (gap + positionLow) fresh))
      node isAtOrAbove)

/-- **Order-T counts over OLD events collapse to the shared merged links.** -/
theorem cupCapSwapT_countOld (state : ArcWireState)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (nfPos : 0 < state.nextFresh) (gap positionLow : Nat)
    (rootHere : Nat) (events : List Nat)
    (allEventsBelow : ∀ node ∈ events, node < state.nextFresh) :
    countEventsInRoot
        (stepCupArc (stepCapArc state (gap + positionLow)) positionLow).links
        rootHere events
      = countEventsInRoot
          (unionFindJoin state.links (natListGetAt state.openWires (gap + positionLow))
            (natListGetAt state.openWires (gap + positionLow + 1)))
          rootHere events :=
  countEventsInRoot_congr_links _ _ rootHere events
    (fun eventNode eventInList =>
      cupCapSwapT_root_old state fresh forest nfPos gap positionLow eventNode
        (allEventsBelow eventNode eventInList))

/-- **Counts of old events at a fresh root over the merged links vanish** — the merge is an
old-world operation. -/
theorem cupCapSwap_countMergedZero (state : ArcWireState)
    (fresh : ArcStateFresh state) (nfPos : 0 < state.nextFresh) (gap positionLow : Nat)
    (rootHere : Nat) (isAtOrAbove : state.nextFresh ≤ rootHere)
    (events : List Nat) (allEventsBelow : ∀ node ∈ events, node < state.nextFresh) :
    countEventsInRoot
        (unionFindJoin state.links (natListGetAt state.openWires (gap + positionLow))
          (natListGetAt state.openWires (gap + positionLow + 1)))
        rootHere events
      = 0 :=
  countEventsInRoot_eq_zero_of_freshRoot _ state.nextFresh
    (fun edge edgeInJoin =>
      (capMerge_all_below state (gap + positionLow) fresh nfPos edge edgeInJoin).2)
    rootHere isAtOrAbove events allEventsBelow

/-! ## The three transposition field lemmas -/

/-- ★ **The width-`3, 1` transposition root-commutes between the two orders.**  Below
`nextFresh` everything is fixed and both orders collapse to the shared merged links; the cup's
triple maps block-to-block (S roots at `nextFresh + 1`, T at `nextFresh + 2` — the
transposition's image of the former); the two cap events exchange and both root at the right
wire's old root; at or above both allocations everything is parentless and fixed. -/
theorem cupCapSwap_rootComm (state : ArcWireState)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (nfPos : 0 < state.nextFresh) (gap positionLow : Nat)
    (positionBound : gap + positionLow + 2 ≤ state.openWires.length)
    (node : Nat) :
    unionFindRootOf
        (stepCupArc (stepCapArc state (gap + positionLow)) positionLow).links
        (arcFreshBlockTransposition state.nextFresh 3 1 node)
      = arcFreshBlockTransposition state.nextFresh 3 1
          (unionFindRootOf
            (stepCapArc (stepCupArc state positionLow) (gap + 2 + positionLow)).links
            node) := by
  have lowInRange : positionLow ≤ state.openWires.length :=
    Nat.le_trans (Nat.le_add_left positionLow gap)
      (Nat.le_trans (Nat.le_add_right (gap + positionLow) 2) positionBound)
  cases Nat.lt_or_ge node state.nextFresh with
  | inl nodeBelow =>
      have mergedRootBelow :
          unionFindRootOf
              (unionFindJoin state.links (natListGetAt state.openWires (gap + positionLow))
                (natListGetAt state.openWires (gap + positionLow + 1)))
              node
            < state.nextFresh :=
        capMerge_root_below state (gap + positionLow) fresh nfPos node nodeBelow
      rw [arcFreshBlockTransposition_ofBelow state.nextFresh 3 1 node nodeBelow,
        cupCapSwapT_root_old state fresh forest nfPos gap positionLow node nodeBelow,
        cupCapSwapS_root_old state fresh forest nfPos gap positionLow lowInRange node
          nodeBelow,
        arcFreshBlockTransposition_ofBelow state.nextFresh 3 1
          (unionFindRootOf
            (unionFindJoin state.links (natListGetAt state.openWires (gap + positionLow))
              (natListGetAt state.openWires (gap + positionLow + 1)))
            node)
          mergedRootBelow]
  | inr nodeAtOrAbove =>
      obtain ⟨offset, offsetEquation⟩ := Nat.le.dest nodeAtOrAbove
      subst offsetEquation
      have freshCapMid : ArcStateFresh (stepCapArc state (gap + positionLow)) :=
        stepCapArc_arcStateFresh state (gap + positionLow) fresh
      have forestCapMid : isUnionFindForest (stepCapArc state (gap + positionLow)).links :=
        isUnionFindForest_stepCapArc state (gap + positionLow) forest
      have linkParentsBelow : ∀ edge ∈ state.links, edge.2 < state.nextFresh :=
        fun edge edgeInLinks => (fresh.2.1 edge edgeInLinks).2
      have rootRightBelow :
          unionFindRootOf state.links (natListGetAt state.openWires (gap + positionLow + 1))
            < state.nextFresh :=
        unionFindRootOf_lt_of_fresh state.links state.nextFresh linkParentsBelow _
          (natListGetAt_lt state.nextFresh nfPos state.openWires (gap + positionLow + 1)
            fresh.1)
      have sigmaFirstZero :
          arcFreshBlockTransposition state.nextFresh 3 1 state.nextFresh
            = state.nextFresh + 1 :=
        arcFreshBlockTransposition_onFirstBlock state.nextFresh 3 1 0 (by decide)
      have sigmaFirstOne :
          arcFreshBlockTransposition state.nextFresh 3 1 (state.nextFresh + 1)
            = state.nextFresh + 2 :=
        arcFreshBlockTransposition_onFirstBlock state.nextFresh 3 1 1 (by decide)
      have sigmaFirstTwo :
          arcFreshBlockTransposition state.nextFresh 3 1 (state.nextFresh + 2)
            = state.nextFresh + 3 :=
        arcFreshBlockTransposition_onFirstBlock state.nextFresh 3 1 2 (by decide)
      have sigmaSecondZero :
          arcFreshBlockTransposition state.nextFresh 3 1 (state.nextFresh + 3)
            = state.nextFresh :=
        arcFreshBlockTransposition_onSecondBlock state.nextFresh 3 1 0 (by decide)
      have rootTLeftLeg :
          unionFindRootOf
              (stepCupArc (stepCapArc state (gap + positionLow)) positionLow).links
              (state.nextFresh + 1)
            = state.nextFresh + 2 :=
        stepCupArc_root_leftLeg (stepCapArc state (gap + positionLow)) positionLow
          freshCapMid forestCapMid
      have rootTRightLeg :
          unionFindRootOf
              (stepCupArc (stepCapArc state (gap + positionLow)) positionLow).links
              (state.nextFresh + 2)
            = state.nextFresh + 2 :=
        stepCupArc_root_rightLeg (stepCapArc state (gap + positionLow)) positionLow
          freshCapMid forestCapMid
      have rootTEventNode :
          unionFindRootOf
              (stepCupArc (stepCapArc state (gap + positionLow)) positionLow).links
              (state.nextFresh + 3)
            = state.nextFresh + 2 :=
        stepCupArc_root_eventNode (stepCapArc state (gap + positionLow)) positionLow
          freshCapMid forestCapMid
      have rootSAtBase :
          unionFindRootOf
              (stepCapArc (stepCupArc state positionLow) (gap + 2 + positionLow)).links
              state.nextFresh
            = state.nextFresh + 1 :=
        cupCapSwapS_root_triple state fresh forest nfPos gap positionLow lowInRange
          state.nextFresh (stepCupArc_root_leftLeg state positionLow fresh forest)
      have rootSAtOne :
          unionFindRootOf
              (stepCapArc (stepCupArc state positionLow) (gap + 2 + positionLow)).links
              (state.nextFresh + 1)
            = state.nextFresh + 1 :=
        cupCapSwapS_root_triple state fresh forest nfPos gap positionLow lowInRange
          (state.nextFresh + 1) (stepCupArc_root_rightLeg state positionLow fresh forest)
      have rootSAtTwo :
          unionFindRootOf
              (stepCapArc (stepCupArc state positionLow) (gap + 2 + positionLow)).links
              (state.nextFresh + 2)
            = state.nextFresh + 1 :=
        cupCapSwapS_root_triple state fresh forest nfPos gap positionLow lowInRange
          (state.nextFresh + 2) (stepCupArc_root_eventNode state positionLow fresh forest)
      have rootSCapEvent :
          unionFindRootOf
              (stepCapArc (stepCupArc state positionLow) (gap + 2 + positionLow)).links
              (state.nextFresh + 3)
            = unionFindRootOf state.links
                (natListGetAt state.openWires (gap + positionLow + 1)) :=
        cupCapSwapS_root_capEvent state fresh forest nfPos gap positionLow lowInRange
      have rootTCapEvent :
          unionFindRootOf
              (stepCupArc (stepCapArc state (gap + positionLow)) positionLow).links
              state.nextFresh
            = unionFindRootOf state.links
                (natListGetAt state.openWires (gap + positionLow + 1)) :=
        cupCapSwapT_root_capEvent state fresh forest nfPos gap positionLow
      match offset with
      | 0 => rw [Nat.add_zero, sigmaFirstZero, rootTLeftLeg, rootSAtBase, sigmaFirstOne]
      | 1 => rw [sigmaFirstOne, rootTRightLeg, rootSAtOne, sigmaFirstOne]
      | 2 => rw [sigmaFirstTwo, rootTEventNode, rootSAtTwo, sigmaFirstOne]
      | 3 =>
          rw [sigmaSecondZero, rootTCapEvent, rootSCapEvent,
            arcFreshBlockTransposition_ofBelow state.nextFresh 3 1
              (unionFindRootOf state.links
                (natListGetAt state.openWires (gap + positionLow + 1)))
              rootRightBelow]
      | offsetRest + 4 =>
          have farAbove :
              state.nextFresh + 4 ≤ state.nextFresh + (offsetRest + 4) :=
            Nat.add_le_add_left (Nat.le_add_left 4 offsetRest) state.nextFresh
          have sigmaFixed :
              arcFreshBlockTransposition state.nextFresh 3 1
                  (state.nextFresh + (offsetRest + 4))
                = state.nextFresh + (offsetRest + 4) :=
            arcFreshBlockTransposition_ofAtOrAbove state.nextFresh 3 1
              (state.nextFresh + (offsetRest + 4)) farAbove
          rw [sigmaFixed,
            cupCapSwapT_root_above state fresh gap positionLow
              (state.nextFresh + (offsetRest + 4)) farAbove,
            cupCapSwapS_root_above state fresh gap positionLow
              (state.nextFresh + (offsetRest + 4)) farAbove,
            sigmaFixed]

/-- ★ **The per-root cup-event counts correspond across the transposition.**  Each order
pushes ONE cup event — `nextFresh + 2` in S (rooting at `nextFresh + 1`) and `nextFresh + 3`
in T (rooting at `nextFresh + 2`, the transposition's image) — so the head guards fire at
exactly corresponding roots; old counts collapse to the shared merged links; fresh tails
vanish. -/
theorem cupCapSwap_cupCorr (state : ArcWireState)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (nfPos : 0 < state.nextFresh) (gap positionLow : Nat)
    (positionBound : gap + positionLow + 2 ≤ state.openWires.length)
    (countRoot : Nat) :
    countEventsInRoot
        (stepCupArc (stepCapArc state (gap + positionLow)) positionLow).links
        (arcFreshBlockTransposition state.nextFresh 3 1 countRoot)
        (stepCupArc (stepCapArc state (gap + positionLow)) positionLow).cupEventNodes
      = countEventsInRoot
          (stepCapArc (stepCupArc state positionLow) (gap + 2 + positionLow)).links
          countRoot
          (stepCapArc (stepCupArc state positionLow) (gap + 2 + positionLow)).cupEventNodes
    := by
  have lowInRange : positionLow ≤ state.openWires.length :=
    Nat.le_trans (Nat.le_add_left positionLow gap)
      (Nat.le_trans (Nat.le_add_right (gap + positionLow) 2) positionBound)
  have freshCapMid : ArcStateFresh (stepCapArc state (gap + positionLow)) :=
    stepCapArc_arcStateFresh state (gap + positionLow) fresh
  have forestCapMid : isUnionFindForest (stepCapArc state (gap + positionLow)).links :=
    isUnionFindForest_stepCapArc state (gap + positionLow) forest
  have rootTEventNode :
      unionFindRootOf
          (stepCupArc (stepCapArc state (gap + positionLow)) positionLow).links
          (state.nextFresh + 3)
        = state.nextFresh + 2 :=
    stepCupArc_root_eventNode (stepCapArc state (gap + positionLow)) positionLow
      freshCapMid forestCapMid
  have rootSAtTwo :
      unionFindRootOf
          (stepCapArc (stepCupArc state positionLow) (gap + 2 + positionLow)).links
          (state.nextFresh + 2)
        = state.nextFresh + 1 :=
    cupCapSwapS_root_triple state fresh forest nfPos gap positionLow lowInRange
      (state.nextFresh + 2) (stepCupArc_root_eventNode state positionLow fresh forest)
  show (if unionFindRootOf
          (stepCupArc (stepCapArc state (gap + positionLow)) positionLow).links
          (state.nextFresh + 3)
        == arcFreshBlockTransposition state.nextFresh 3 1 countRoot then (1 : Nat) else 0)
      + countEventsInRoot
          (stepCupArc (stepCapArc state (gap + positionLow)) positionLow).links
          (arcFreshBlockTransposition state.nextFresh 3 1 countRoot) state.cupEventNodes
    = (if unionFindRootOf
          (stepCapArc (stepCupArc state positionLow) (gap + 2 + positionLow)).links
          (state.nextFresh + 2)
        == countRoot then (1 : Nat) else 0)
      + countEventsInRoot
          (stepCapArc (stepCupArc state positionLow) (gap + 2 + positionLow)).links
          countRoot state.cupEventNodes
  rw [rootTEventNode, rootSAtTwo]
  have sigmaFirstZero :
      arcFreshBlockTransposition state.nextFresh 3 1 state.nextFresh
        = state.nextFresh + 1 :=
    arcFreshBlockTransposition_onFirstBlock state.nextFresh 3 1 0 (by decide)
  have sigmaFirstOne :
      arcFreshBlockTransposition state.nextFresh 3 1 (state.nextFresh + 1)
        = state.nextFresh + 2 :=
    arcFreshBlockTransposition_onFirstBlock state.nextFresh 3 1 1 (by decide)
  have sigmaFirstTwo :
      arcFreshBlockTransposition state.nextFresh 3 1 (state.nextFresh + 2)
        = state.nextFresh + 3 :=
    arcFreshBlockTransposition_onFirstBlock state.nextFresh 3 1 2 (by decide)
  have sigmaSecondZero :
      arcFreshBlockTransposition state.nextFresh 3 1 (state.nextFresh + 3)
        = state.nextFresh :=
    arcFreshBlockTransposition_onSecondBlock state.nextFresh 3 1 0 (by decide)
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
  have guardTwoOne : ¬ (state.nextFresh + 2 == state.nextFresh + 1) = true :=
    fun isTrue => Bool.noConfusion (beq_false_of_lt oneBelowTwo ▸ isTrue)
  have guardOneBase : ¬ (state.nextFresh + 1 == state.nextFresh) = true :=
    fun isTrue => Bool.noConfusion (beq_false_of_lt baseBelowOne ▸ isTrue)
  have guardTwoThree : ¬ (state.nextFresh + 2 == state.nextFresh + 3) = true :=
    fun isTrue => Bool.noConfusion (beq_false_of_lt_left twoBelowThree ▸ isTrue)
  have guardOneTwo : ¬ (state.nextFresh + 1 == state.nextFresh + 2) = true :=
    fun isTrue => Bool.noConfusion (beq_false_of_lt_left oneBelowTwo ▸ isTrue)
  have guardTwoBase : ¬ (state.nextFresh + 2 == state.nextFresh) = true :=
    fun isTrue => Bool.noConfusion (beq_false_of_lt baseBelowTwo ▸ isTrue)
  have guardOneThree : ¬ (state.nextFresh + 1 == state.nextFresh + 3) = true :=
    fun isTrue => Bool.noConfusion (beq_false_of_lt_left oneBelowThree ▸ isTrue)
  have trueTwoTwo : (state.nextFresh + 2 == state.nextFresh + 2) = true :=
    decide_eq_true rfl
  have trueOneOne : (state.nextFresh + 1 == state.nextFresh + 1) = true :=
    decide_eq_true rfl
  cases Nat.lt_or_ge countRoot state.nextFresh with
  | inl rootBelow =>
      have guardTwoOld : ¬ (state.nextFresh + 2 == countRoot) = true :=
        fun isTrue =>
          Bool.noConfusion
            (beq_false_of_lt (Nat.lt_trans rootBelow baseBelowTwo) ▸ isTrue)
      have guardOneOld : ¬ (state.nextFresh + 1 == countRoot) = true :=
        fun isTrue =>
          Bool.noConfusion
            (beq_false_of_lt (Nat.lt_trans rootBelow baseBelowOne) ▸ isTrue)
      rw [arcFreshBlockTransposition_ofBelow state.nextFresh 3 1 countRoot rootBelow,
        if_neg guardTwoOld, if_neg guardOneOld,
        cupCapSwapT_countOld state fresh forest nfPos gap positionLow countRoot
          state.cupEventNodes fresh.2.2.1,
        cupCapSwapS_countOld state fresh forest nfPos gap positionLow lowInRange countRoot
          state.cupEventNodes fresh.2.2.1]
  | inr rootAtLeastBase =>
  cases Nat.lt_or_ge countRoot (state.nextFresh + 1) with
  | inl belowOne =>
      have rootIsBase : countRoot = state.nextFresh :=
        Nat.le_antisymm (Nat.le_of_lt_succ belowOne) rootAtLeastBase
      subst rootIsBase
      rw [sigmaFirstZero, if_neg guardTwoOne, if_neg guardOneBase,
        cupCapSwapT_countOld state fresh forest nfPos gap positionLow (state.nextFresh + 1)
          state.cupEventNodes fresh.2.2.1,
        cupCapSwapS_countOld state fresh forest nfPos gap positionLow lowInRange
          state.nextFresh state.cupEventNodes fresh.2.2.1,
        cupCapSwap_countMergedZero state fresh nfPos gap positionLow (state.nextFresh + 1)
          (Nat.le_add_right state.nextFresh 1) state.cupEventNodes fresh.2.2.1,
        cupCapSwap_countMergedZero state fresh nfPos gap positionLow state.nextFresh
          (Nat.le_refl state.nextFresh) state.cupEventNodes fresh.2.2.1]
  | inr rootAtLeastOne =>
  cases Nat.lt_or_ge countRoot (state.nextFresh + 2) with
  | inl belowTwo =>
      have rootIsOne : countRoot = state.nextFresh + 1 :=
        Nat.le_antisymm (Nat.le_of_lt_succ belowTwo) rootAtLeastOne
      subst rootIsOne
      rw [sigmaFirstOne, if_pos trueTwoTwo, if_pos trueOneOne,
        cupCapSwapT_countOld state fresh forest nfPos gap positionLow (state.nextFresh + 2)
          state.cupEventNodes fresh.2.2.1,
        cupCapSwapS_countOld state fresh forest nfPos gap positionLow lowInRange
          (state.nextFresh + 1) state.cupEventNodes fresh.2.2.1,
        cupCapSwap_countMergedZero state fresh nfPos gap positionLow (state.nextFresh + 2)
          (Nat.le_add_right state.nextFresh 2) state.cupEventNodes fresh.2.2.1,
        cupCapSwap_countMergedZero state fresh nfPos gap positionLow (state.nextFresh + 1)
          (Nat.le_add_right state.nextFresh 1) state.cupEventNodes fresh.2.2.1]
  | inr rootAtLeastTwo =>
  cases Nat.lt_or_ge countRoot (state.nextFresh + 3) with
  | inl belowThree =>
      have rootIsTwo : countRoot = state.nextFresh + 2 :=
        Nat.le_antisymm (Nat.le_of_lt_succ belowThree) rootAtLeastTwo
      subst rootIsTwo
      rw [sigmaFirstTwo, if_neg guardTwoThree, if_neg guardOneTwo,
        cupCapSwapT_countOld state fresh forest nfPos gap positionLow (state.nextFresh + 3)
          state.cupEventNodes fresh.2.2.1,
        cupCapSwapS_countOld state fresh forest nfPos gap positionLow lowInRange
          (state.nextFresh + 2) state.cupEventNodes fresh.2.2.1,
        cupCapSwap_countMergedZero state fresh nfPos gap positionLow (state.nextFresh + 3)
          (Nat.le_add_right state.nextFresh 3) state.cupEventNodes fresh.2.2.1,
        cupCapSwap_countMergedZero state fresh nfPos gap positionLow (state.nextFresh + 2)
          (Nat.le_add_right state.nextFresh 2) state.cupEventNodes fresh.2.2.1]
  | inr rootAtLeastThree =>
  cases Nat.lt_or_ge countRoot (state.nextFresh + 4) with
  | inl belowFour =>
      have rootIsThree : countRoot = state.nextFresh + 3 :=
        Nat.le_antisymm (Nat.le_of_lt_succ belowFour) rootAtLeastThree
      subst rootIsThree
      rw [sigmaSecondZero, if_neg guardTwoBase, if_neg guardOneThree,
        cupCapSwapT_countOld state fresh forest nfPos gap positionLow state.nextFresh
          state.cupEventNodes fresh.2.2.1,
        cupCapSwapS_countOld state fresh forest nfPos gap positionLow lowInRange
          (state.nextFresh + 3) state.cupEventNodes fresh.2.2.1,
        cupCapSwap_countMergedZero state fresh nfPos gap positionLow state.nextFresh
          (Nat.le_refl state.nextFresh) state.cupEventNodes fresh.2.2.1,
        cupCapSwap_countMergedZero state fresh nfPos gap positionLow (state.nextFresh + 3)
          (Nat.le_add_right state.nextFresh 3) state.cupEventNodes fresh.2.2.1]
  | inr rootAtLeastFour =>
      have sigmaFixed :
          arcFreshBlockTransposition state.nextFresh 3 1 countRoot = countRoot :=
        arcFreshBlockTransposition_ofAtOrAbove state.nextFresh 3 1 countRoot rootAtLeastFour
      have twoBelowRoot : state.nextFresh + 2 < countRoot :=
        Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by decide) state.nextFresh) rootAtLeastFour
      have oneBelowRoot : state.nextFresh + 1 < countRoot :=
        Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by decide) state.nextFresh) rootAtLeastFour
      have guardTwoHigh : ¬ (state.nextFresh + 2 == countRoot) = true :=
        fun isTrue => Bool.noConfusion (beq_false_of_lt_left twoBelowRoot ▸ isTrue)
      have guardOneHigh : ¬ (state.nextFresh + 1 == countRoot) = true :=
        fun isTrue => Bool.noConfusion (beq_false_of_lt_left oneBelowRoot ▸ isTrue)
      rw [sigmaFixed, if_neg guardTwoHigh, if_neg guardOneHigh,
        cupCapSwapT_countOld state fresh forest nfPos gap positionLow countRoot
          state.cupEventNodes fresh.2.2.1,
        cupCapSwapS_countOld state fresh forest nfPos gap positionLow lowInRange countRoot
          state.cupEventNodes fresh.2.2.1,
        cupCapSwap_countMergedZero state fresh nfPos gap positionLow countRoot
          (Nat.le_trans (Nat.le_add_right state.nextFresh 4) rootAtLeastFour)
          state.cupEventNodes fresh.2.2.1]

/-- ★ **The per-root cap-event counts correspond across the transposition.**  Both orders'
cap events root at the SAME old root (the right wire's), so the head guards agree wherever
the transposition acts; old tails collapse to the shared merged links; fresh tails vanish. -/
theorem cupCapSwap_capCorr (state : ArcWireState)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (nfPos : 0 < state.nextFresh) (gap positionLow : Nat)
    (positionBound : gap + positionLow + 2 ≤ state.openWires.length)
    (countRoot : Nat) :
    countEventsInRoot
        (stepCupArc (stepCapArc state (gap + positionLow)) positionLow).links
        (arcFreshBlockTransposition state.nextFresh 3 1 countRoot)
        (stepCupArc (stepCapArc state (gap + positionLow)) positionLow).capEventNodes
      = countEventsInRoot
          (stepCapArc (stepCupArc state positionLow) (gap + 2 + positionLow)).links
          countRoot
          (stepCapArc (stepCupArc state positionLow) (gap + 2 + positionLow)).capEventNodes
    := by
  have lowInRange : positionLow ≤ state.openWires.length :=
    Nat.le_trans (Nat.le_add_left positionLow gap)
      (Nat.le_trans (Nat.le_add_right (gap + positionLow) 2) positionBound)
  have linkParentsBelow : ∀ edge ∈ state.links, edge.2 < state.nextFresh :=
    fun edge edgeInLinks => (fresh.2.1 edge edgeInLinks).2
  have rootRightBelow :
      unionFindRootOf state.links (natListGetAt state.openWires (gap + positionLow + 1))
        < state.nextFresh :=
    unionFindRootOf_lt_of_fresh state.links state.nextFresh linkParentsBelow _
      (natListGetAt_lt state.nextFresh nfPos state.openWires (gap + positionLow + 1) fresh.1)
  have rootTCapEvent :
      unionFindRootOf
          (stepCupArc (stepCapArc state (gap + positionLow)) positionLow).links
          state.nextFresh
        = unionFindRootOf state.links
            (natListGetAt state.openWires (gap + positionLow + 1)) :=
    cupCapSwapT_root_capEvent state fresh forest nfPos gap positionLow
  have rootSCapEvent :
      unionFindRootOf
          (stepCapArc (stepCupArc state positionLow) (gap + 2 + positionLow)).links
          (state.nextFresh + 3)
        = unionFindRootOf state.links
            (natListGetAt state.openWires (gap + positionLow + 1)) :=
    cupCapSwapS_root_capEvent state fresh forest nfPos gap positionLow lowInRange
  show (if unionFindRootOf
          (stepCupArc (stepCapArc state (gap + positionLow)) positionLow).links
          state.nextFresh
        == arcFreshBlockTransposition state.nextFresh 3 1 countRoot then (1 : Nat) else 0)
      + countEventsInRoot
          (stepCupArc (stepCapArc state (gap + positionLow)) positionLow).links
          (arcFreshBlockTransposition state.nextFresh 3 1 countRoot) state.capEventNodes
    = (if unionFindRootOf
          (stepCapArc (stepCupArc state positionLow) (gap + 2 + positionLow)).links
          (state.nextFresh + 3)
        == countRoot then (1 : Nat) else 0)
      + countEventsInRoot
          (stepCapArc (stepCupArc state positionLow) (gap + 2 + positionLow)).links
          countRoot state.capEventNodes
  rw [rootTCapEvent, rootSCapEvent]
  cases Nat.lt_or_ge countRoot state.nextFresh with
  | inl rootBelow =>
      rw [arcFreshBlockTransposition_ofBelow state.nextFresh 3 1 countRoot rootBelow,
        cupCapSwapT_countOld state fresh forest nfPos gap positionLow countRoot
          state.capEventNodes fresh.2.2.2,
        cupCapSwapS_countOld state fresh forest nfPos gap positionLow lowInRange countRoot
          state.capEventNodes fresh.2.2.2]
  | inr rootAtOrAbove =>
      have sigmaImageAtOrAbove :
          state.nextFresh
            ≤ arcFreshBlockTransposition state.nextFresh 3 1 countRoot :=
        sigmaAtOrAbove_of_fixesBelow (arcFreshBlockTransposition state.nextFresh 3 1)
          (fun firstId secondId imagesEqual =>
            arcFreshBlockTransposition_injective state.nextFresh 3 1 firstId secondId
              imagesEqual)
          state.nextFresh
          (fun identifier isBelow =>
            arcFreshBlockTransposition_ofBelow state.nextFresh 3 1 identifier isBelow)
          countRoot rootAtOrAbove
      have guardSourceHigh :
          ¬ (unionFindRootOf state.links
              (natListGetAt state.openWires (gap + positionLow + 1))
            == countRoot) = true :=
        fun isTrue =>
          Bool.noConfusion
            (beq_false_of_lt_left (Nat.lt_of_lt_of_le rootRightBelow rootAtOrAbove)
              ▸ isTrue)
      have guardTargetHigh :
          ¬ (unionFindRootOf state.links
              (natListGetAt state.openWires (gap + positionLow + 1))
            == arcFreshBlockTransposition state.nextFresh 3 1 countRoot) = true :=
        fun isTrue =>
          Bool.noConfusion
            (beq_false_of_lt_left (Nat.lt_of_lt_of_le rootRightBelow sigmaImageAtOrAbove)
              ▸ isTrue)
      rw [if_neg guardTargetHigh, if_neg guardSourceHigh,
        cupCapSwapT_countOld state fresh forest nfPos gap positionLow
          (arcFreshBlockTransposition state.nextFresh 3 1 countRoot) state.capEventNodes
          fresh.2.2.2,
        cupCapSwapS_countOld state fresh forest nfPos gap positionLow lowInRange countRoot
          state.capEventNodes fresh.2.2.2,
        cupCapSwap_countMergedZero state fresh nfPos gap positionLow
          (arcFreshBlockTransposition state.nextFresh 3 1 countRoot) sigmaImageAtOrAbove
          state.capEventNodes fresh.2.2.2,
        cupCapSwap_countMergedZero state fresh nfPos gap positionLow countRoot rootAtOrAbove
          state.capEventNodes fresh.2.2.2]

/-! ## The assembled simulation -/

/-- ★ **The CUP x CAP two-step core simulation.**  Order S fires the low cup at `positionLow`
then the high cap at `gap + 2 + positionLow`; order T fires the high cap at
`gap + positionLow` then the low cup at `positionLow`.  The fresh-block transposition at
widths `3, 1` is an `ArcStepSimCount` between the results: both orders consume the same wire
values and build the same merged component; `openMap` is the iii-1a insert-below/remove-above
commutation; `loopsEq` is the same-component test's stability through the cup. -/
theorem arcStepSimCount_cupCapSwap (state : ArcWireState)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (nfPos : 0 < state.nextFresh)
    (gap positionLow : Nat)
    (positionBound : gap + positionLow + 2 ≤ state.openWires.length) :
    ArcStepSimCount (arcFreshBlockTransposition state.nextFresh 3 1)
      (stepCapArc (stepCupArc state positionLow) (gap + 2 + positionLow))
      (stepCupArc (stepCapArc state (gap + positionLow)) positionLow) where
  openMap := by
    have sigmaFirstZero :
        arcFreshBlockTransposition state.nextFresh 3 1 state.nextFresh
          = state.nextFresh + 1 :=
      arcFreshBlockTransposition_onFirstBlock state.nextFresh 3 1 0 (by decide)
    have sigmaFirstOne :
        arcFreshBlockTransposition state.nextFresh 3 1 (state.nextFresh + 1)
          = state.nextFresh + 2 :=
      arcFreshBlockTransposition_onFirstBlock state.nextFresh 3 1 1 (by decide)
    show natListInsertAt (natListRemoveTwoAt state.openWires (gap + positionLow)) positionLow
        [state.nextFresh + 1, state.nextFresh + 2]
      = (natListRemoveTwoAt
          (natListInsertAt state.openWires positionLow
            [state.nextFresh, state.nextFresh + 1])
          (gap + 2 + positionLow)).map (arcFreshBlockTransposition state.nextFresh 3 1)
    rw [natListRemoveTwoAt_map (arcFreshBlockTransposition state.nextFresh 3 1)
        (natListInsertAt state.openWires positionLow [state.nextFresh, state.nextFresh + 1])
        (gap + 2 + positionLow),
      natListInsertAt_map (arcFreshBlockTransposition state.nextFresh 3 1) state.openWires
        positionLow [state.nextFresh, state.nextFresh + 1],
      mapPairValues (arcFreshBlockTransposition state.nextFresh 3 1) state.nextFresh
        (state.nextFresh + 1),
      sigmaFirstZero, sigmaFirstOne,
      mapFixedOn (arcFreshBlockTransposition state.nextFresh 3 1) state.openWires
        (fun wire wireInList =>
          arcFreshBlockTransposition_ofBelow state.nextFresh 3 1 wire
            (fresh.1 wire wireInList)),
      natListInsertAt_removeAbove_commute state.openWires positionLow gap
        [state.nextFresh + 1, state.nextFresh + 2] positionBound]
    exact rfl
  nfEq := rfl
  rootComm := fun node =>
    cupCapSwap_rootComm state fresh forest nfPos gap positionLow positionBound node
  loopsEq := by
    have lowInRange : positionLow ≤ state.openWires.length :=
      Nat.le_trans (Nat.le_add_left positionLow gap)
        (Nat.le_trans (Nat.le_add_right (gap + positionLow) 2) positionBound)
    have linkParentsBelow : ∀ edge ∈ state.links, edge.2 < state.nextFresh :=
      fun edge edgeInLinks => (fresh.2.1 edge edgeInLinks).2
    have rootLeftBelow :
        unionFindRootOf state.links (natListGetAt state.openWires (gap + positionLow))
          < state.nextFresh :=
      unionFindRootOf_lt_of_fresh state.links state.nextFresh linkParentsBelow _
        (natListGetAt_lt state.nextFresh nfPos state.openWires (gap + positionLow) fresh.1)
    have rootRightBelow :
        unionFindRootOf state.links (natListGetAt state.openWires (gap + positionLow + 1))
          < state.nextFresh :=
      unionFindRootOf_lt_of_fresh state.links state.nextFresh linkParentsBelow _
        (natListGetAt_lt state.nextFresh nfPos state.openWires (gap + positionLow + 1)
          fresh.1)
    have collapseLeft :
        unionFindRootOf (stepCupArc state positionLow).links
            (natListGetAt state.openWires (gap + positionLow))
          = unionFindRootOf state.links (natListGetAt state.openWires (gap + positionLow))
        :=
      unionFindRootOf_stepCupArc_old state positionLow fresh forest _ rootLeftBelow
    have collapseRight :
        unionFindRootOf (stepCupArc state positionLow).links
            (natListGetAt state.openWires (gap + positionLow + 1))
          = unionFindRootOf state.links
              (natListGetAt state.openWires (gap + positionLow + 1)) :=
      unionFindRootOf_stepCupArc_old state positionLow fresh forest _ rootRightBelow
    have componentStable :
        isSameComponent (stepCupArc state positionLow).links
            (natListGetAt state.openWires (gap + positionLow))
            (natListGetAt state.openWires (gap + positionLow + 1))
          = isSameComponent state.links (natListGetAt state.openWires (gap + positionLow))
              (natListGetAt state.openWires (gap + positionLow + 1)) := by
      show (unionFindRootOf (stepCupArc state positionLow).links
            (natListGetAt state.openWires (gap + positionLow))
          == unionFindRootOf (stepCupArc state positionLow).links
              (natListGetAt state.openWires (gap + positionLow + 1)))
        = (unionFindRootOf state.links (natListGetAt state.openWires (gap + positionLow))
          == unionFindRootOf state.links
              (natListGetAt state.openWires (gap + positionLow + 1)))
      rw [collapseLeft, collapseRight]
    show (if isSameComponent state.links (natListGetAt state.openWires (gap + positionLow))
            (natListGetAt state.openWires (gap + positionLow + 1))
          then state.loops + 1 else state.loops)
      = (if isSameComponent (stepCupArc state positionLow).links
            (natListGetAt (natListInsertAt state.openWires positionLow
              [state.nextFresh, state.nextFresh + 1]) (gap + 2 + positionLow))
            (natListGetAt (natListInsertAt state.openWires positionLow
              [state.nextFresh, state.nextFresh + 1]) (gap + 2 + positionLow + 1))
          then state.loops + 1 else state.loops)
    rw [natListGetAt_pastInsertedPair state.openWires positionLow gap state.nextFresh
        (state.nextFresh + 1) lowInRange,
      natListGetAt_pastInsertedPair_succ state.openWires positionLow gap state.nextFresh
        (state.nextFresh + 1) lowInRange,
      componentStable]
  cupCorr := fun countRoot =>
    cupCapSwap_cupCorr state fresh forest nfPos gap positionLow positionBound countRoot
  capCorr := fun countRoot =>
    cupCapSwap_capCorr state fresh forest nfPos gap positionLow positionBound countRoot
  forestS :=
    isUnionFindForest_stepCapArc (stepCupArc state positionLow) (gap + 2 + positionLow)
      (isUnionFindForest_stepCupArc state positionLow forest)
  forestT :=
    isUnionFindForest_stepCupArc (stepCapArc state (gap + positionLow)) positionLow
      (isUnionFindForest_stepCapArc state (gap + positionLow) forest)

/-! ## Honesty marker -/

/-- **Honesty marker — the CUP x CAP two-step core simulation is SHIPPED (ARC-2b brick
iii-1d-beta2).**  `arcStepSimCount_cupCapSwap`: the two run orders of a cup-cap
disjoint-window swap are `ArcStepSimCount`-related by the fresh-block transposition at widths
`3, 1`.  The load-bearing fact: both orders consume the SAME wire values (the `pastBlock`
read collapse) and build the SAME merged component, so roots and counts reduce to the alpha1
cup atlas + the beta1 cap atlas + the shared merge; `openMap` rides the iii-1a
insert-below/remove-above commutation; `loopsEq` is the same-component test's stability
through the cup.  NOT yet shipped: the CAP x CUP mirror, the CAP x CAP case (with the
loop-transfer crossing analysis), and the dispatcher that reads the realized ii-b swap pair
into these position forms.  `= true`. -/
def fxMode_hasCupCapSwapSimulation : Bool := true

end FX1Poly.Polygraph
