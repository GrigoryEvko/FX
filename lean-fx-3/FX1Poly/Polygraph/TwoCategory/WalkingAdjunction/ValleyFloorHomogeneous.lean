import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.UnionFindFloorAbove
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ValleyAppendSplit

/-! # ValleyFloorHomogeneous — no valley edge crosses the floor; the two whole-valley root facts

The valley classification's two directions each need a union-find ROOT fact about the whole valley
`V = capBlock ++ cupBlock` run from the canonical seed at bottom count `bc`:

  * **N1** (below-floor / survivor direction): every old node `c < bc` keeps its root `< bc`.
  * **N2** (at-or-above-floor / cup-leg direction): every cup leg `v ≥ bc` keeps its root `≥ bc`.

Both reduce to a single structural invariant: no valley edge CROSSES the floor `bc`.  A cap edge joins two
old nodes (both `< bc`), a cup edge joins two fresh legs (both `≥ bc`).  So every edge is FLOOR-HOMOGENEOUS
— `bc ≤ child ↔ bc ≤ parent`, recorded here as the conjunction of the two one-way implications.  The cap
block establishes it (all endpoints `< bc`, `processSpine_links_below_ofAllCapArity_seed`); the cup block
preserves it because a cup only ever prepends the edge `(nextFresh, nextFresh + 1)` — both `≥ bc` once
`bc ≤ nextFresh`, established by the fresh legs being parentless (`WireStateFresh`).

  * `stepCup_links_freshCons` — a cup's links are exactly `(nextFresh, nextFresh+1) :: links` (fresh legs
    are their own roots).
  * `unionFindRootOf_lt_of_edgesBelowFloor` — the below-floor root dual (conditional-edge form).
  * `processSpine_edgesFloorHomogeneous_ofAllCupArity` — the cup-block fold of floor-homogeneity.
  * `valleyRootBelowFloor` (N1) and `valleyCupLegRootAboveFloor` (N2) — the two whole-valley root facts.

Raw Lean 4 + Init; structural on the edge list / `AllCupArity` recursion, no `omega` / `simp`-AC /
`WellFounded.fix`.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## A cup's links are a fresh-leg cons -/

/-- ★ **A cup prepends exactly the edge `(nextFresh, nextFresh + 1)`.**  Both fresh legs are parentless in
the pre-cup forest (`WireStateFresh` makes every edge child `< nextFresh`, so neither `nextFresh` nor
`nextFresh + 1` is any edge's child), hence each is its own root; the join's already-equal guard is `false`
(the two legs differ), so `unionFindJoin` prepends `(nextFresh, nextFresh + 1)`.  The concrete edge the
floor-homogeneity fold reasons about. -/
theorem stepCup_links_freshCons (state : WireState) (position : Nat) (fresh : WireStateFresh state) :
    (stepCup state position).links = (state.nextFresh, state.nextFresh + 1) :: state.links := by
  have childBelow : ∀ edge ∈ state.links, edge.1 < state.nextFresh :=
    fun edge edgeInLinks => (fresh.2 edge edgeInLinks).1
  have rootNf : unionFindRootOf state.links state.nextFresh = state.nextFresh :=
    unionFindRootOf_of_parentless _ _
      (unionFindParent_none_of_lt state.nextFresh state.links childBelow state.nextFresh (Nat.le_refl _))
  have rootNf1 : unionFindRootOf state.links (state.nextFresh + 1) = state.nextFresh + 1 :=
    unionFindRootOf_of_parentless _ _
      (unionFindParent_none_of_lt state.nextFresh state.links childBelow (state.nextFresh + 1)
        (Nat.le_succ _))
  rw [stepCup_links]
  show (if unionFindRootOf state.links state.nextFresh == unionFindRootOf state.links (state.nextFresh + 1)
      then state.links
      else (unionFindRootOf state.links state.nextFresh, unionFindRootOf state.links (state.nextFresh + 1))
        :: state.links) = (state.nextFresh, state.nextFresh + 1) :: state.links
  rw [rootNf, rootNf1,
    show (state.nextFresh == state.nextFresh + 1) = false from
      decide_eq_false (Nat.ne_of_lt (Nat.lt_succ_self state.nextFresh))]
  exact if_neg (fun falseEqTrue => Bool.noConfusion falseEqTrue)

/-! ## The below-floor root dual (conditional-edge form) -/

/-- One parent step from a below-floor node lands below the floor, when every edge whose child is `< floor`
has its parent `< floor`.  The conditional-edge dual of `unionFindParent_below`. -/
theorem unionFindParent_lt_of_edgesBelowFloor (floor : Nat) :
    (links : List (Nat × Nat)) → (∀ edge ∈ links, edge.1 < floor → edge.2 < floor) →
    (node parent : Nat) → node < floor → unionFindParent links node = some parent → parent < floor
  | [], _, node, parent, _, h => by
      rw [show unionFindParent ([] : List (Nat × Nat)) node = none from rfl] at h
      nomatch h
  | (child, par) :: rest, edgesBelow, node, parent, nodeLt, h => by
      have hh : (if child == node then some par else unionFindParent rest node) = some parent := h
      cases hcn : child == node with
      | true =>
          rw [hcn] at hh
          have childEqNode : child = node := of_decide_eq_true hcn
          have childLt : child < floor := childEqNode ▸ nodeLt
          rw [← Option.some.inj hh]
          exact edgesBelow (child, par) (List.Mem.head _) childLt
      | false =>
          rw [hcn] at hh
          exact unionFindParent_lt_of_edgesBelowFloor floor rest
            (fun edge edgeInRest => edgesBelow edge (List.Mem.tail _ edgeInRest)) node parent nodeLt hh

/-- Root-following stays below the floor under conditional below-floor edges (fuel induction). -/
theorem unionFindRoot_lt_of_edgesBelowFloor (links : List (Nat × Nat)) (floor : Nat)
    (edgesBelow : ∀ edge ∈ links, edge.1 < floor → edge.2 < floor) :
    (fuel node : Nat) → node < floor → unionFindRoot fuel links node < floor
  | 0, _, h => h
  | fuel + 1, node, h => by
      show (match unionFindParent links node with
            | none => node | some parent => unionFindRoot fuel links parent) < floor
      cases hp : unionFindParent links node with
      | none => exact h
      | some parent =>
          exact unionFindRoot_lt_of_edgesBelowFloor links floor edgesBelow fuel parent
            (unionFindParent_lt_of_edgesBelowFloor floor links edgesBelow node parent h hp)

/-- A below-floor node keeps its root below the floor (packaged form) under conditional below-floor edges. -/
theorem unionFindRootOf_lt_of_edgesBelowFloor (links : List (Nat × Nat)) (floor : Nat)
    (edgesBelow : ∀ edge ∈ links, edge.1 < floor → edge.2 < floor) (node : Nat) (h : node < floor) :
    unionFindRootOf links node < floor :=
  unionFindRoot_lt_of_edgesBelowFloor links floor edgesBelow (links.length + 1) node h

/-! ## The cup-block fold of floor-homogeneity -/

/-- **Floor-homogeneity of one edge** — its child and parent are on the same side of the floor (recorded as
the two one-way implications). -/
def edgeFloorHomogeneous (floor : Nat) (edge : Nat × Nat) : Prop :=
  (floor ≤ edge.1 → floor ≤ edge.2) ∧ (edge.1 < floor → edge.2 < floor)

/-- A cup step preserves floor-homogeneity of every edge, given the fresh legs are at or above the floor. -/
theorem stepCup_edgesFloorHomogeneous (state : WireState) (position floor : Nat)
    (fresh : WireStateFresh state) (floorLe : floor ≤ state.nextFresh)
    (baseHomog : ∀ edge ∈ state.links, edgeFloorHomogeneous floor edge) :
    ∀ edge ∈ (stepCup state position).links, edgeFloorHomogeneous floor edge := by
  rw [stepCup_links_freshCons state position fresh]
  intro edge edgeInCons
  cases edgeInCons with
  | head =>
      exact ⟨fun _ => Nat.le_trans floorLe (Nat.le_succ state.nextFresh),
        fun headLt => absurd headLt (Nat.not_lt.mpr floorLe)⟩
  | tail _ edgeInRest => exact baseHomog edge edgeInRest

/-- ★ **A pure-cup block preserves floor-homogeneity of every edge.**  Run from a state whose links are
already floor-homogeneous, whose fresh counter sits at or above the floor (`floor ≤ nextFresh`, only rising
under cups), and which is `WireStateFresh`, every cup prepends only the at-or-above-floor edge
`(nextFresh, nextFresh + 1)` (`stepCup_edgesFloorHomogeneous`), so the whole block's links stay
floor-homogeneous.  `AllCupArity` induction, threading `WireStateFresh` (`stepCup_wireStateFresh`) and the
monotone floor bound. -/
theorem processSpine_edgesFloorHomogeneous_ofAllCupArity
    {overallSource overallTarget : adjunctionGraph.Mode} (floor : Nat)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (pureCup : AllCupArity atoms) :
    (state : WireState) → WireStateFresh state → floor ≤ state.nextFresh →
    (∀ edge ∈ state.links, edgeFloorHomogeneous floor edge) →
    ∀ edge ∈ (processSpine state atoms).links, edgeFloorHomogeneous floor edge := by
  induction pureCup with
  | nil => intro state _ _ baseHomog; exact baseHomog
  | cons hasCupDomArity hasCupCodArity _restAllCup restHomog =>
      rename_i headAtom rest
      intro state fresh floorLe baseHomog
      show ∀ edge ∈ (processSpine (stepAtom state headAtom) rest).links, edgeFloorHomogeneous floor edge
      rw [stepAtom_ofCupArity state headAtom hasCupDomArity hasCupCodArity]
      refine restHomog (stepCup state headAtom.leftContext.length)
        (stepCup_wireStateFresh state headAtom.leftContext.length fresh) ?_
        (stepCup_edgesFloorHomogeneous state headAtom.leftContext.length floor fresh floorLe baseHomog)
      rw [stepCup_nextFresh]
      exact Nat.le_trans floorLe (Nat.le_add_right state.nextFresh 2)

/-! ## The two whole-valley root facts -/

/-- The whole-valley links are floor-homogeneous at the floor `bc`.  The cap block establishes the base (all
endpoints `< bc`, so both implications hold — the second directly, the first vacuously); the cup block
preserves it.  Bundles the seed instantiation of the cup fold. -/
theorem valleyEdgesFloorHomogeneous
    {overallSource overallMiddle overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (bottomPositive : 0 < bottomCount)
    (capAtoms : List (SpineAtom adjunctionModeSignature overallSource overallMiddle))
    (cupAtoms : List (SpineAtom adjunctionModeSignature overallMiddle overallTarget))
    (pureCap : AllCapArity capAtoms) (pureCup : AllCupArity cupAtoms) :
    ∀ edge ∈ (processSpine (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capAtoms)
        cupAtoms).links, edgeFloorHomogeneous bottomCount edge := by
  have capFresh : WireStateFresh (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capAtoms) :=
    processSpine_wireStateFresh capAtoms ⟨List.range bottomCount, [], bottomCount, 0⟩
      (wireStateFresh_initial bottomCount) bottomPositive
  have capNextFresh :
      (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capAtoms).nextFresh = bottomCount :=
    processSpine_nextFresh_ofAllCapArity_seed bottomCount capAtoms pureCap
  have capBase : ∀ edge ∈ (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capAtoms).links,
      edgeFloorHomogeneous bottomCount edge := by
    intro edge edgeInLinks
    have belowBoth := processSpine_links_below_ofAllCapArity_seed bottomCount bottomPositive capAtoms
      pureCap edge edgeInLinks
    exact ⟨fun floorLeChild => absurd floorLeChild (Nat.not_le.mpr belowBoth.1),
      fun _ => belowBoth.2⟩
  exact processSpine_edgesFloorHomogeneous_ofAllCupArity bottomCount cupAtoms pureCup
    (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capAtoms) capFresh
    (Nat.le_of_eq capNextFresh.symm) capBase

/-- ★ **N1 — every below-floor node keeps its whole-valley root below the floor.**  From floor-homogeneity
(`valleyEdgesFloorHomogeneous`) an old node `c < bc` root-follows only within the below-`bc` zone
(`unionFindRootOf_lt_of_edgesBelowFloor`).  So a cap-block through-strand's bottom end has a below-floor
root — the survivor (below-floor) classification direction's front-hit ingredient. -/
theorem valleyRootBelowFloor
    {overallSource overallMiddle overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (bottomPositive : 0 < bottomCount)
    (capAtoms : List (SpineAtom adjunctionModeSignature overallSource overallMiddle))
    (cupAtoms : List (SpineAtom adjunctionModeSignature overallMiddle overallTarget))
    (pureCap : AllCapArity capAtoms) (pureCup : AllCupArity cupAtoms)
    (node : Nat) (nodeBelow : node < bottomCount) :
    unionFindRootOf (processSpine (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩ capAtoms)
        cupAtoms).links node < bottomCount :=
  unionFindRootOf_lt_of_edgesBelowFloor _ bottomCount
    (fun edge edgeInLinks => (valleyEdgesFloorHomogeneous bottomCount bottomPositive capAtoms cupAtoms
      pureCap pureCup edge edgeInLinks).2) node nodeBelow

/-- ★ **N2 — every at-or-above-floor node keeps its whole-valley root at or above the floor.**  From
floor-homogeneity (`valleyEdgesFloorHomogeneous`) a cup leg `v ≥ bc` root-follows only within the
at-or-above-`bc` zone (`unionFindRootOf_ge_of_edgesPreserveFloor`).  So a top-top cup arc's leg has an
at-or-above-floor root, disjoint from every below-`bc` bottom root — the cup-leg classification direction's
front-miss ingredient (the hard N2). -/
theorem valleyCupLegRootAboveFloor
    {overallSource overallMiddle overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (bottomPositive : 0 < bottomCount)
    (capAtoms : List (SpineAtom adjunctionModeSignature overallSource overallMiddle))
    (cupAtoms : List (SpineAtom adjunctionModeSignature overallMiddle overallTarget))
    (pureCap : AllCapArity capAtoms) (pureCup : AllCupArity cupAtoms)
    (node : Nat) (nodeAbove : bottomCount ≤ node) :
    bottomCount ≤ unionFindRootOf (processSpine (processSpine ⟨List.range bottomCount, [], bottomCount, 0⟩
        capAtoms) cupAtoms).links node :=
  unionFindRootOf_ge_of_edgesPreserveFloor _ bottomCount
    (fun edge edgeInLinks => (valleyEdgesFloorHomogeneous bottomCount bottomPositive capAtoms cupAtoms
      pureCap pureCup edge edgeInLinks).1) node nodeAbove

/-! ## Honesty marker -/

/-- **Honesty marker — the whole-valley floor-homogeneity invariant + BOTH root facts (N1, N2) are
SHIPPED.**  Landed here, all zero-axiom:

  * `stepCup_links_freshCons` — a cup prepends exactly `(nextFresh, nextFresh + 1)` (fresh legs are their
    own roots).
  * `unionFindParent_lt_of_edgesBelowFloor` / `unionFindRoot_lt_of_edgesBelowFloor` /
    `unionFindRootOf_lt_of_edgesBelowFloor` — the conditional-edge below-floor root dual.
  * `processSpine_edgesFloorHomogeneous_ofAllCupArity` — the cup-block fold of floor-homogeneity
    (`WireStateFresh` + the monotone floor bound threaded through the shipped invariants).
  * `valleyEdgesFloorHomogeneous` — no whole-valley edge crosses the floor `bc` (cap edges both `< bc`, cup
    edges both `≥ bc`).
  * ★ `valleyRootBelowFloor` (N1) and `valleyCupLegRootAboveFloor` (N2) — a below-`bc` node keeps its root
    `< bc`; a cup leg (`≥ bc`) keeps its root `≥ bc`.  Together: a cup leg's root is disjoint from every
    bottom root — the fresh-root separation the classification's two directions each consume.

This completes the union-find HALF of the classification (with brick 2's floor kernel and brick 1's scan
localization).  What this marker does NOT itself close: the classification lemma proper
(`isSurvivorTop (matchingOf bc V) (bc+p) = decide (finalOpen[p] < bc)`), which assembles these root facts
with the boundary reads / partner-scan split, and the downstream surjectivity / F-G reconstruction /
`valleyAppend_split` / `valleysWithEqualMatching_spineTraceEquiv`.  No gate flag is flipped.  `= true`. -/
def fxMode_hasValleyFloorHomogeneous : Bool := true

end FX1Poly.Polygraph
