import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapRenameable
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingComponentAlgebra

/-! # ArcFreshComponentInvisibility — fresh joins are transparent to old probes (peel campaign H, cup rung 2d-ii prep)

The census preservation steps need to read a step's component view THROUGH its event-node
bookkeeping: every cup/cap allocates a fresh event node and unions it into the arc's component,
but an event node is never a boundary end, so the census only ever probes OLD nodes.  This brick
ships the component-view surgery that peels those bookkeeping joins away:

  * a node at-or-above the freshness bound is its own root and shares no component with any
    bounded probe (`isSameComponent_offFreshNode`);
  * a join whose LEFT node is off both probes' components is transparent — the merged partition
    restricted to the two probes is the old partition (`isSameComponent_unionFindJoin_offProbes`);
  * hence a CAP step's component view at two old probes is exactly the view of the genuine wire
    join — the event join peels off (`isSameComponent_stepCapArc_oldProbes`);
  * and a CUP step's component view at two old probes is exactly the OLD view — both the leg
    join and the event join touch only fresh nodes (`isSameComponent_stepCupArc_oldProbes`).

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Fresh nodes are component-invisible -/

/-- ★ A node at-or-above the freshness bound shares no component with any bounded probe: the
fresh node is parentless (no edge's child reaches the bound), so it is its own root, while the
probe's root stays below the bound. -/
theorem isSameComponent_offFreshNode (links : List (Nat × Nat)) (bound : Nat)
    (childrenBelow : ∀ edge ∈ links, edge.1 < bound)
    (parentsBelow : ∀ edge ∈ links, edge.2 < bound)
    (freshNode probeNode : Nat) (freshAtLeast : bound ≤ freshNode)
    (probeBelow : probeNode < bound) :
    isSameComponent links freshNode probeNode = false := by
  have freshParentless : unionFindParent links freshNode = none :=
    unionFindParent_none_of_lt bound links childrenBelow freshNode freshAtLeast
  have freshIsRoot : unionFindRootOf links freshNode = freshNode :=
    unionFindRootOf_of_parentless links freshNode freshParentless
  have probeRootBelow : unionFindRootOf links probeNode < bound :=
    unionFindRootOf_lt_of_fresh links bound parentsBelow probeNode probeBelow
  have rootsDistinct : ¬ (freshNode = unionFindRootOf links probeNode) := fun rootsEqual =>
    absurd (Nat.lt_of_lt_of_le probeRootBelow
        (Nat.le_trans freshAtLeast (Nat.le_of_eq rootsEqual)))
      (Nat.lt_irrefl (unionFindRootOf links probeNode))
  have beqIsFalse : (freshNode == unionFindRootOf links probeNode) = false :=
    decide_eq_false rootsDistinct
  show (unionFindRootOf links freshNode == unionFindRootOf links probeNode) = false
  rw [freshIsRoot]
  exact beqIsFalse

/-- ★ A join whose LEFT node is off both probes' components is transparent: restricted to the
two probes, the merged partition is the old partition.  Through the flat-disjunction join
characterization both cross disjuncts die on the off facts. -/
theorem isSameComponent_unionFindJoin_offProbes (links : List (Nat × Nat))
    (forest : isUnionFindForest links) (joinLeft joinRight probeOne probeTwo : Nat)
    (offOne : isSameComponent links joinLeft probeOne = false)
    (offTwo : isSameComponent links joinLeft probeTwo = false) :
    isSameComponent (unionFindJoin links joinLeft joinRight) probeOne probeTwo
      = isSameComponent links probeOne probeTwo := by
  rw [isSameComponent_unionFindJoin links forest joinLeft joinRight probeOne probeTwo,
    offOne, offTwo]
  cases baseTest : isSameComponent links probeOne probeTwo with
  | true => rfl
  | false => rfl

/-! ## The step-level peels -/

/-- ★ **A CAP step's component view at two old probes is the genuine wire join's view.**  The
cap's links are the event join over the wire join; the event node sits at `nextFresh`, off every
old component, so it peels — exactly the shape the census token-surgery dispatches on. -/
theorem isSameComponent_stepCapArc_oldProbes (state : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (probeOne probeTwo : Nat)
    (probeOneBelow : probeOne < state.nextFresh) (probeTwoBelow : probeTwo < state.nextFresh) :
    isSameComponent (stepCapArc state position).links probeOne probeTwo
      = isSameComponent
          (unionFindJoin state.links (natListGetAt state.openWires position)
            (natListGetAt state.openWires (position + 1)))
          probeOne probeTwo := by
  obtain ⟨openBelow, linksBelow, _cupBelow, _capBelow⟩ := fresh
  have boundPositive : 0 < state.nextFresh :=
    Nat.lt_of_le_of_lt (Nat.zero_le probeOne) probeOneBelow
  have parentsBelow : ∀ edge ∈ state.links, edge.2 < state.nextFresh :=
    fun edge edgeInLinks => (linksBelow edge edgeInLinks).2
  have leftBelow : natListGetAt state.openWires position < state.nextFresh :=
    natListGetAt_lt state.nextFresh boundPositive state.openWires position openBelow
  have rightBelow : natListGetAt state.openWires (position + 1) < state.nextFresh :=
    natListGetAt_lt state.nextFresh boundPositive state.openWires (position + 1) openBelow
  have leftRootBelow :
      unionFindRootOf state.links (natListGetAt state.openWires position) < state.nextFresh :=
    unionFindRootOf_lt_of_fresh state.links state.nextFresh parentsBelow
      (natListGetAt state.openWires position) leftBelow
  have rightRootBelow :
      unionFindRootOf state.links (natListGetAt state.openWires (position + 1))
        < state.nextFresh :=
    unionFindRootOf_lt_of_fresh state.links state.nextFresh parentsBelow
      (natListGetAt state.openWires (position + 1)) rightBelow
  have wireJoinBelow :
      ∀ edge ∈ unionFindJoin state.links (natListGetAt state.openWires position)
          (natListGetAt state.openWires (position + 1)),
        edge.1 < state.nextFresh ∧ edge.2 < state.nextFresh :=
    unionFindJoin_all_lt state.nextFresh state.links (natListGetAt state.openWires position)
      (natListGetAt state.openWires (position + 1)) linksBelow leftRootBelow rightRootBelow
  have wireJoinForest :
      isUnionFindForest (unionFindJoin state.links (natListGetAt state.openWires position)
        (natListGetAt state.openWires (position + 1))) :=
    isUnionFindForest_unionFindJoin state.links (natListGetAt state.openWires position)
      (natListGetAt state.openWires (position + 1)) forest
  have offEventOne :
      isSameComponent (unionFindJoin state.links (natListGetAt state.openWires position)
          (natListGetAt state.openWires (position + 1))) state.nextFresh probeOne = false :=
    isSameComponent_offFreshNode _ state.nextFresh
      (fun edge edgeInJoin => (wireJoinBelow edge edgeInJoin).1)
      (fun edge edgeInJoin => (wireJoinBelow edge edgeInJoin).2)
      state.nextFresh probeOne (Nat.le_refl state.nextFresh) probeOneBelow
  have offEventTwo :
      isSameComponent (unionFindJoin state.links (natListGetAt state.openWires position)
          (natListGetAt state.openWires (position + 1))) state.nextFresh probeTwo = false :=
    isSameComponent_offFreshNode _ state.nextFresh
      (fun edge edgeInJoin => (wireJoinBelow edge edgeInJoin).1)
      (fun edge edgeInJoin => (wireJoinBelow edge edgeInJoin).2)
      state.nextFresh probeTwo (Nat.le_refl state.nextFresh) probeTwoBelow
  show isSameComponent
      (unionFindJoin (unionFindJoin state.links (natListGetAt state.openWires position)
          (natListGetAt state.openWires (position + 1)))
        state.nextFresh (natListGetAt state.openWires position))
      probeOne probeTwo
    = isSameComponent
        (unionFindJoin state.links (natListGetAt state.openWires position)
          (natListGetAt state.openWires (position + 1)))
        probeOne probeTwo
  exact isSameComponent_unionFindJoin_offProbes _ wireJoinForest state.nextFresh
    (natListGetAt state.openWires position) probeOne probeTwo offEventOne offEventTwo

/-- ★ **A CUP step's component view at two old probes is the OLD view.**  Both the leg join
(two fresh legs) and the event join (a fresh event node) touch only fresh nodes, so the whole
step is component-transparent below `nextFresh` — the cup only wires up its own new strand. -/
theorem isSameComponent_stepCupArc_oldProbes (state : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links)
    (probeOne probeTwo : Nat)
    (probeOneBelow : probeOne < state.nextFresh) (probeTwoBelow : probeTwo < state.nextFresh) :
    isSameComponent (stepCupArc state position).links probeOne probeTwo
      = isSameComponent state.links probeOne probeTwo := by
  obtain ⟨_openBelow, linksBelow, _cupBelow, _capBelow⟩ := fresh
  have childrenBelow : ∀ edge ∈ state.links, edge.1 < state.nextFresh :=
    fun edge edgeInLinks => (linksBelow edge edgeInLinks).1
  have parentsBelow : ∀ edge ∈ state.links, edge.2 < state.nextFresh :=
    fun edge edgeInLinks => (linksBelow edge edgeInLinks).2
  have offLegOne : isSameComponent state.links state.nextFresh probeOne = false :=
    isSameComponent_offFreshNode state.links state.nextFresh childrenBelow parentsBelow
      state.nextFresh probeOne (Nat.le_refl state.nextFresh) probeOneBelow
  have offLegTwo : isSameComponent state.links state.nextFresh probeTwo = false :=
    isSameComponent_offFreshNode state.links state.nextFresh childrenBelow parentsBelow
      state.nextFresh probeTwo (Nat.le_refl state.nextFresh) probeTwoBelow
  have legJoinTransparent :
      isSameComponent (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
          probeOne probeTwo
        = isSameComponent state.links probeOne probeTwo :=
    isSameComponent_unionFindJoin_offProbes state.links forest state.nextFresh
      (state.nextFresh + 1) probeOne probeTwo offLegOne offLegTwo
  have bumpTwo : state.nextFresh < state.nextFresh + 2 := Nat.lt_add_of_pos_right (by decide)
  have linksBelowBumped :
      ∀ edge ∈ state.links, edge.1 < state.nextFresh + 2 ∧ edge.2 < state.nextFresh + 2 :=
    fun edge edgeInLinks =>
      ⟨Nat.lt_trans (linksBelow edge edgeInLinks).1 bumpTwo,
        Nat.lt_trans (linksBelow edge edgeInLinks).2 bumpTwo⟩
  have parentsBelowBumped : ∀ edge ∈ state.links, edge.2 < state.nextFresh + 2 :=
    fun edge edgeInLinks => (linksBelowBumped edge edgeInLinks).2
  have leftLegRootBelow : unionFindRootOf state.links state.nextFresh < state.nextFresh + 2 :=
    unionFindRootOf_lt_of_fresh state.links (state.nextFresh + 2) parentsBelowBumped
      state.nextFresh bumpTwo
  have rightLegRootBelow :
      unionFindRootOf state.links (state.nextFresh + 1) < state.nextFresh + 2 :=
    unionFindRootOf_lt_of_fresh state.links (state.nextFresh + 2) parentsBelowBumped
      (state.nextFresh + 1) (Nat.add_lt_add_left (by decide) state.nextFresh)
  have legJoinBelow :
      ∀ edge ∈ unionFindJoin state.links state.nextFresh (state.nextFresh + 1),
        edge.1 < state.nextFresh + 2 ∧ edge.2 < state.nextFresh + 2 :=
    unionFindJoin_all_lt (state.nextFresh + 2) state.links state.nextFresh (state.nextFresh + 1)
      linksBelowBumped leftLegRootBelow rightLegRootBelow
  have legJoinForest :
      isUnionFindForest (unionFindJoin state.links state.nextFresh (state.nextFresh + 1)) :=
    isUnionFindForest_unionFindJoin state.links state.nextFresh (state.nextFresh + 1) forest
  have offEventOne :
      isSameComponent (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
        (state.nextFresh + 2) probeOne = false :=
    isSameComponent_offFreshNode _ (state.nextFresh + 2)
      (fun edge edgeInJoin => (legJoinBelow edge edgeInJoin).1)
      (fun edge edgeInJoin => (legJoinBelow edge edgeInJoin).2)
      (state.nextFresh + 2) probeOne (Nat.le_refl (state.nextFresh + 2))
      (Nat.lt_trans probeOneBelow bumpTwo)
  have offEventTwo :
      isSameComponent (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
        (state.nextFresh + 2) probeTwo = false :=
    isSameComponent_offFreshNode _ (state.nextFresh + 2)
      (fun edge edgeInJoin => (legJoinBelow edge edgeInJoin).1)
      (fun edge edgeInJoin => (legJoinBelow edge edgeInJoin).2)
      (state.nextFresh + 2) probeTwo (Nat.le_refl (state.nextFresh + 2))
      (Nat.lt_trans probeTwoBelow bumpTwo)
  have eventJoinTransparent :
      isSameComponent (unionFindJoin (unionFindJoin state.links state.nextFresh
            (state.nextFresh + 1))
          (state.nextFresh + 2) state.nextFresh) probeOne probeTwo
        = isSameComponent (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
            probeOne probeTwo :=
    isSameComponent_unionFindJoin_offProbes
      (unionFindJoin state.links state.nextFresh (state.nextFresh + 1)) legJoinForest
      (state.nextFresh + 2) state.nextFresh probeOne probeTwo offEventOne offEventTwo
  show isSameComponent (unionFindJoin (unionFindJoin state.links state.nextFresh
          (state.nextFresh + 1))
        (state.nextFresh + 2) state.nextFresh) probeOne probeTwo
    = isSameComponent state.links probeOne probeTwo
  exact eventJoinTransparent.trans legJoinTransparent

/-- **Honesty marker — the fresh-join transparency toolkit is SHIPPED (peel campaign H, cup
rung 2d-ii prep).**  Fresh nodes are component-invisible to bounded probes, off-probes joins are
transparent, a cap step's view at old probes is the genuine wire join's view, and a cup step's
view at old probes is the unchanged old view.  What this marker does NOT claim: the census
token-surgery preservation through the steps (rungs 2d-ii/iii proper) and the fold transport
(rung 2d-iv).  `= true`. -/
def fxMode_hasArcFreshComponentInvisibility : Bool := true

end FX1Poly.Polygraph
