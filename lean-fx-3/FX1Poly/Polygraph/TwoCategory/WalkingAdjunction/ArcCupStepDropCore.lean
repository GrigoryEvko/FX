import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapRenameable

/-! # ArcCupStepDropCore — a TOP-OF-STACK cup leaves the old ports' matching undisturbed (S3 core)

The whole top-of-stack cup-drop cancellation (`dropLastCup_arc_injective`, S3) rests on ONE core fact: a cup
fired LAST onto an arbitrary incoming state allocates a fresh, ISOLATED 3-node component and splices its two
legs into the open-wire list — so it leaves every OLD port's connected component untouched, merely shifting the
boundary positions at or beyond the insertion window up by two and adding the two fresh legs as a new disjoint
adjacent pair.

This file assembles the freshness / disjointness core the leg rounds need:

  * `stepCupArc_freshComponentRoot` — the three fresh nodes `nextFresh, nextFresh+1, nextFresh+2` all root to
    `nextFresh + 1` under the stepped links (the fresh cup component's single root), computed from the two nested
    `unionFindJoin`s via `unionFindRootOf_unionFindJoin` and the fresh-node parentless facts.
  * `stepCupArc_freshLeg_ne_oldRoot` — hence each fresh leg's stepped root is DISTINCT from the root of every OLD
    port (any node whose base root is below `nextFresh`): the boolean-equality test is `false`, the disjointness
    the punctured scan consumes to skip the two inserted leg candidates.
  * `cupCount_stepCupArc_succ` / `capCount_stepCupArc_eq` — the two trivial count legs: a cup conses one fresh
    cup-event node (`+1`) and leaves the cap-event list untouched.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The fresh cup component's single root under a top-of-stack cup -/

/-- ★ **The fresh cup component roots to `nextFresh + 1`.**  A top-of-stack cup builds
`links := unionFindJoin (unionFindJoin state.links nextFresh (nextFresh+1)) (nextFresh+2) nextFresh`.  In a fresh
forest the three legs `nextFresh, nextFresh+1, nextFresh+2` are each parentless in the base links, so the inner
join sends both `nextFresh` and `nextFresh+1` to root `nextFresh+1` and leaves `nextFresh+2` at `nextFresh+2`,
and the outer join then folds `nextFresh+2` onto `nextFresh`'s root `nextFresh+1` — so all three fresh nodes
share the single component root `nextFresh + 1`, which is at or above `nextFresh` and hence never the root of an
old port. -/
theorem stepCupArc_freshComponentRoot (state : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links) :
    unionFindRootOf (stepCupArc state position).links state.nextFresh = state.nextFresh + 1
      ∧ unionFindRootOf (stepCupArc state position).links (state.nextFresh + 1) = state.nextFresh + 1
      ∧ unionFindRootOf (stepCupArc state position).links (state.nextFresh + 2)
          = state.nextFresh + 1 := by
  have hLinks : (stepCupArc state position).links
      = unionFindJoin (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
          (state.nextFresh + 2) state.nextFresh := rfl
  -- the three legs are parentless in the base links (a fresh forest keeps every child below `nextFresh`)
  have baseRootNf : unionFindRootOf state.links state.nextFresh = state.nextFresh :=
    unionFindRootOf_of_parentless state.links state.nextFresh
      (unionFindParent_none_of_freshNode state fresh state.nextFresh (Nat.le_refl _))
  have baseRootNf1 : unionFindRootOf state.links (state.nextFresh + 1) = state.nextFresh + 1 :=
    unionFindRootOf_of_parentless state.links (state.nextFresh + 1)
      (unionFindParent_none_of_freshNode state fresh (state.nextFresh + 1) (Nat.le_add_right _ _))
  have baseRootNf2 : unionFindRootOf state.links (state.nextFresh + 2) = state.nextFresh + 2 :=
    unionFindRootOf_of_parentless state.links (state.nextFresh + 2)
      (unionFindParent_none_of_freshNode state fresh (state.nextFresh + 2) (Nat.le_add_right _ _))
  have forestL1 : isUnionFindForest (unionFindJoin state.links state.nextFresh (state.nextFresh + 1)) :=
    isUnionFindForest_unionFindJoin state.links state.nextFresh (state.nextFresh + 1) forest
  have hNf1LtNf2 : state.nextFresh + 1 < state.nextFresh + 2 := Nat.lt_succ_self _
  -- inner-join roots of the three legs
  have l1Nf : unionFindRootOf (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
      state.nextFresh = state.nextFresh + 1 := by
    rw [unionFindRootOf_unionFindJoin state.links state.nextFresh (state.nextFresh + 1) state.nextFresh forest,
      baseRootNf, baseRootNf1]
    cases hc : (state.nextFresh == state.nextFresh) with
    | true => rfl
    | false =>
        exact Bool.noConfusion
          ((decide_eq_true (rfl : state.nextFresh = state.nextFresh)).symm.trans hc)
  have l1Nf1 : unionFindRootOf (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
      (state.nextFresh + 1) = state.nextFresh + 1 := by
    rw [unionFindRootOf_unionFindJoin state.links state.nextFresh (state.nextFresh + 1)
      (state.nextFresh + 1) forest, baseRootNf1]
    cases hc : (unionFindRootOf state.links state.nextFresh == state.nextFresh + 1) with
    | true => rfl
    | false => rfl
  have l1Nf2 : unionFindRootOf (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
      (state.nextFresh + 2) = state.nextFresh + 2 := by
    rw [unionFindRootOf_unionFindJoin state.links state.nextFresh (state.nextFresh + 1)
      (state.nextFresh + 2) forest, baseRootNf, baseRootNf2]
    cases hc : (state.nextFresh == state.nextFresh + 2) with
    | true =>
        exact absurd (of_decide_eq_true hc)
          (Nat.ne_of_lt (Nat.lt_add_of_pos_right (by decide)))
    | false => rfl
  -- outer-join roots (the `nextFresh+2 -> nextFresh` fold) of the three legs
  refine ⟨?_, ?_, ?_⟩
  · rw [hLinks,
      unionFindRootOf_unionFindJoin (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
        (state.nextFresh + 2) state.nextFresh state.nextFresh forestL1, l1Nf2, l1Nf]
    cases hc : (state.nextFresh + 2 == state.nextFresh + 1) with
    | true => rfl
    | false => rfl
  · rw [hLinks,
      unionFindRootOf_unionFindJoin (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
        (state.nextFresh + 2) state.nextFresh (state.nextFresh + 1) forestL1, l1Nf2, l1Nf1]
    cases hc : (state.nextFresh + 2 == state.nextFresh + 1) with
    | true => exact absurd (of_decide_eq_true hc) (Nat.ne_of_gt hNf1LtNf2)
    | false => rfl
  · rw [hLinks,
      unionFindRootOf_unionFindJoin (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
        (state.nextFresh + 2) state.nextFresh (state.nextFresh + 2) forestL1, l1Nf2, l1Nf]
    cases hc : (state.nextFresh + 2 == state.nextFresh + 2) with
    | true => rfl
    | false =>
        exact Bool.noConfusion
          ((decide_eq_true (rfl : state.nextFresh + 2 = state.nextFresh + 2)).symm.trans hc)

/-! ## Disjointness of the fresh legs from every old port -/

/-- ★ **A fresh leg's stepped root is distinct from every old port's root.**  For an OLD node `y` whose base root
lies below `nextFresh`, neither the left leg `nextFresh` nor the right leg `nextFresh+1` shares `y`'s component
under the stepped links: both fresh legs root to `nextFresh + 1` (`stepCupArc_freshComponentRoot`), which lies
strictly above `y`'s root, so the boolean same-root test is `false`.  This is the disjointness the punctured
scan consumes to skip the two inserted leg candidates. -/
theorem stepCupArc_freshLeg_ne_oldRoot (state : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links) (y : Nat)
    (yBelowFresh : unionFindRootOf state.links y < state.nextFresh) :
    (unionFindRootOf (stepCupArc state position).links state.nextFresh
        == unionFindRootOf state.links y) = false
      ∧ (unionFindRootOf (stepCupArc state position).links (state.nextFresh + 1)
          == unionFindRootOf state.links y) = false := by
  obtain ⟨rootNf, rootNf1, _⟩ := stepCupArc_freshComponentRoot state position fresh forest
  have yBelowFresh1 : unionFindRootOf state.links y < state.nextFresh + 1 :=
    Nat.lt_succ_of_lt yBelowFresh
  refine ⟨?_, ?_⟩
  · rw [rootNf]; exact beq_false_of_lt yBelowFresh1
  · rw [rootNf1]; exact beq_false_of_lt yBelowFresh1

/-! ## The two trivial count legs -/

/-- ★ **A cup conses exactly one fresh cup-event node.**  `stepCupArc` prepends the event node `nextFresh+2`
to `cupEventNodes`, so the cup-event count rises by exactly one. -/
theorem cupCount_stepCupArc_succ (state : ArcWireState) (position : Nat) :
    (stepCupArc state position).cupEventNodes.length = state.cupEventNodes.length + 1 := rfl

/-- ★ **A cup leaves the cap-event list untouched.**  `stepCupArc` never allocates a cap event, so the
cap-event count is unchanged. -/
theorem capCount_stepCupArc_eq (state : ArcWireState) (position : Nat) :
    (stepCupArc state position).capEventNodes.length = state.capEventNodes.length := rfl

end FX1Poly.Polygraph
