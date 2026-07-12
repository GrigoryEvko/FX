import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcTwoCupGodementSwapWires
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.MatchingCupSwapRootComm

/-! # mode-3 floor — the pure two-CUP Godement swap: the `rootComm` union-find automorphism + the full count-bundle

This file closes the residual-(2) HEART of the pure cup × cup Godement block swap on the arc reader
(`ArcWireState` / `stepCupArc`, `SpineTraceDecision`): the `rootComm` field of a full `ArcStepSimCount`, i.e. the
statement that the fresh block rotation `σ = blockRotate state.nextFresh 3 3` is a union-find AUTOMORPHISM of the
ONE shared two-cup forest.  Combined with the two shipped legs (`ArcTwoCupGodementSwapWires`: the LINKS
byte-identity and the OPEN-WIRE block transform) and the count fields (which ride on `rootComm` via the shipped
`countEventsInRoot_rootComm`), it assembles the literal full 8-field `ArcStepSimCount` bundle for the cup × cup
interchange — the delivery that flips `fxMode_hasArcTwoCupGodementSwapSim`.

## The design (nominal-sets equivariance, verified-UF-first)

`root(σ x) = σ(root x)` is the printed EQUIVARIANCE identity `f(g·x) = g·f(x)` (Gabbay–Pitts / Pitts, *Nominal
Sets* 2013): `root` is an equivariant map of the `Perm(NodeId)`-action, and `σ` is a finite-support transposition
of two support-blocks.  The verified union-find literature (Conchon–Filliâtre, Charguéraud–Pottier, Lammich,
Guttmann) proves representative-correctness and amortized complexity but states NO find-equivariance /
graph-automorphism-invariance lemma — this machine-checked statement appears to be new in that corpus.

Concretely (probe-confirmed): two cups over a fresh forest `orig` produce the byte-identical shared forest

  `L' = (nf+5, nf+4) :: (nf+3, nf+4) :: (nf+2, nf+1) :: (nf, nf+1) :: orig`

with two three-id components — block1 `{nf, nf+1, nf+2}` rooted at `nf+1`, block2 `{nf+3, nf+4, nf+5}` rooted at
`nf+4` — that `σ = blockRotate nf 3 3` swaps (`nf+1 ↔ nf+4`), fixing base and tail.  This is the 4-edge port of the
matching-route twin `MatchingCupSwapRootComm.blockSwap_rootComm` (2-edge), and it is the field the matching
keystone could not supply for the refuted CAP case (`MatchingSwapObstruction`) — TRUE for the cup restriction
because cups allocate FRESH legs.

## C1 — the localization: the concrete two-cup shared forest

`unionFindJoin_cons_of_roots` reduces a join whose two roots are known and distinct to a single cons; iterated
four times over the freshness-derived parentless facts it gives `stepCupArc_links_cons` (one cup) and
`twoCupArcLinks_cons` (two cups) — the concrete `L'`.  Fresh joins never move base roots; the two block roots
compute to `nf+1` / `nf+4`.

Raw Lean 4 + Init; structural / fuel recursion, `decide`-form `Nat` equality, no `omega` / `simp`-AC /
`WellFounded.fix` / `propext` / `Quot.sound`.  Per-declaration `#assert_no_axioms` + independent `#print axioms`
in the audit twins. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## C1 — the localization lemmas: the concrete two-cup shared forest -/

/-- ★ **A union-find JOIN with known distinct roots is a single cons.**  When `unionFindRootOf links firstNode` and
`unionFindRootOf links secondNode` are the given `firstRoot` / `secondRoot` and those differ, `unionFindJoin`
prepends the one edge `(firstRoot, secondRoot)`.  The atom that turns the two-cup join tower into the concrete
`L'` cons form. -/
theorem unionFindJoin_cons_of_roots (links : List (Nat × Nat)) (firstNode secondNode firstRoot secondRoot : Nat)
    (hfr : unionFindRootOf links firstNode = firstRoot) (hsr : unionFindRootOf links secondNode = secondRoot)
    (distinct : ¬ (firstRoot == secondRoot) = true) :
    unionFindJoin links firstNode secondNode = (firstRoot, secondRoot) :: links := by
  show (if unionFindRootOf links firstNode == unionFindRootOf links secondNode then links
        else (unionFindRootOf links firstNode, unionFindRootOf links secondNode) :: links)
      = (firstRoot, secondRoot) :: links
  rw [hfr, hsr, if_neg distinct]

/-- ★ **One CUP's union-find links, in concrete cons form** (fresh forest).  A cup joins its two fresh legs
(`nf, nf+1`) then joins the event node (`nf+2`) onto the left leg, whose root is now `nf+1` — so the edge list is
`(nf+2, nf+1) :: (nf, nf+1) :: orig`, a two-edge tree rooted at `nf+1`.  Proven by two
`unionFindJoin_cons_of_roots`, the second's `nf → nf+1` root via `unionFindRootOf_consJoin`. -/
theorem stepCupArc_links_cons (state : ArcWireState) (position : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links) :
    (stepCupArc state position).links
      = (state.nextFresh + 2, state.nextFresh + 1) :: (state.nextFresh, state.nextFresh + 1) :: state.links := by
  show unionFindJoin (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
        (state.nextFresh + 2) state.nextFresh
      = (state.nextFresh + 2, state.nextFresh + 1) :: (state.nextFresh, state.nextFresh + 1) :: state.links
  have childrenBelow : ∀ edge ∈ state.links, edge.1 < state.nextFresh := fun edge he => (fresh.2.1 edge he).1
  have plNf : unionFindParent state.links state.nextFresh = none :=
    unionFindParent_none_of_lt state.nextFresh state.links childrenBelow state.nextFresh (Nat.le_refl _)
  have plNf1 : unionFindParent state.links (state.nextFresh + 1) = none :=
    unionFindParent_none_of_lt state.nextFresh state.links childrenBelow (state.nextFresh + 1)
      (Nat.le_add_right _ _)
  have rootNf : unionFindRootOf state.links state.nextFresh = state.nextFresh :=
    unionFindRootOf_of_parentless state.links state.nextFresh plNf
  have rootNf1 : unionFindRootOf state.links (state.nextFresh + 1) = state.nextFresh + 1 :=
    unionFindRootOf_of_parentless state.links (state.nextFresh + 1) plNf1
  have distinctNf01 : ¬ (state.nextFresh == state.nextFresh + 1) = true :=
    natBeqNeTrue (Nat.ne_of_lt (Nat.lt_add_of_pos_right (by decide)))
  have inner : unionFindJoin state.links state.nextFresh (state.nextFresh + 1)
      = (state.nextFresh, state.nextFresh + 1) :: state.links :=
    unionFindJoin_cons_of_roots state.links state.nextFresh (state.nextFresh + 1) state.nextFresh
      (state.nextFresh + 1) rootNf rootNf1 distinctNf01
  rw [inner]
  -- roots over `M1 = (nf, nf+1) :: orig`
  have childrenBelowM1 : ∀ edge ∈ (state.nextFresh, state.nextFresh + 1) :: state.links,
      edge.1 < state.nextFresh + 1 := by
    intro edge he
    cases he with
    | head => exact Nat.lt_add_of_pos_right (by decide)
    | tail _ heRest => exact Nat.lt_trans (childrenBelow edge heRest) (Nat.lt_add_of_pos_right (by decide))
  have plNf2M1 : unionFindParent ((state.nextFresh, state.nextFresh + 1) :: state.links) (state.nextFresh + 2)
      = none :=
    unionFindParent_none_of_lt (state.nextFresh + 1) _ childrenBelowM1 (state.nextFresh + 2)
      (Nat.add_le_add_left (by decide) state.nextFresh)
  have rootNf2M1 : unionFindRootOf ((state.nextFresh, state.nextFresh + 1) :: state.links) (state.nextFresh + 2)
      = state.nextFresh + 2 :=
    unionFindRootOf_of_parentless _ (state.nextFresh + 2) plNf2M1
  have rootNfM1 : unionFindRootOf ((state.nextFresh, state.nextFresh + 1) :: state.links) state.nextFresh
      = state.nextFresh + 1 := by
    rw [unionFindRootOf_consJoin state.links state.nextFresh (state.nextFresh + 1) forest plNf plNf1 distinctNf01
      state.nextFresh, rootNf, if_pos (natBeqSelf state.nextFresh)]
  have distinctNf2Nf1 : ¬ (state.nextFresh + 2 == state.nextFresh + 1) = true :=
    natBeqNeTrue (Nat.ne_of_gt (Nat.add_lt_add_left (by decide) state.nextFresh))
  exact unionFindJoin_cons_of_roots _ (state.nextFresh + 2) state.nextFresh (state.nextFresh + 2)
    (state.nextFresh + 1) rootNf2M1 rootNfM1 distinctNf2Nf1

/-- ★ **The two-cup shared forest, in concrete cons form.**  Firing the low cup then the high cup (positions
irrelevant to the links, `stepCupArc_links_positionFree`) over a fresh forest `orig` yields

  `(nf+5, nf+4) :: (nf+3, nf+4) :: (nf+2, nf+1) :: (nf, nf+1) :: orig`

— two disjoint three-id trees rooted at `nf+1` (block1) and `nf+4` (block2), byte-identical between the two
Godement run orders (`stepCupArc_stepCupArc_links_eq`).  This is the `L'` the block rotation is an automorphism
OF.  Proven by `stepCupArc_links_cons` for the inner cup, then two more `unionFindJoin_cons_of_roots` for the
outer cup's legs (the outer event's `nf+3 → nf+4` root via `unionFindRootOf_consJoin` over the inner forest). -/
theorem twoCupArcLinks_cons (state : ArcWireState) (lowPosition gap : Nat)
    (fresh : ArcStateFresh state) (forest : isUnionFindForest state.links) :
    (stepCupArc (stepCupArc state lowPosition) (gap + 2 + lowPosition)).links
      = (state.nextFresh + 5, state.nextFresh + 4) :: (state.nextFresh + 3, state.nextFresh + 4)
        :: (state.nextFresh + 2, state.nextFresh + 1) :: (state.nextFresh, state.nextFresh + 1)
        :: state.links := by
  -- the inner cup's links in cons form, and its freshness / forest for the outer computations
  have innerLinks : (stepCupArc state lowPosition).links
      = (state.nextFresh + 2, state.nextFresh + 1) :: (state.nextFresh, state.nextFresh + 1) :: state.links :=
    stepCupArc_links_cons state lowPosition fresh forest
  have innerFreshEdges : ∀ edge ∈ (stepCupArc state lowPosition).links,
      edge.1 < (stepCupArc state lowPosition).nextFresh :=
    fun edge he => ((stepCupArc_arcStateFresh state lowPosition fresh).2.1 edge he).1
  have innerForest : isUnionFindForest (stepCupArc state lowPosition).links :=
    isUnionFindForest_stepCupArc state lowPosition forest
  -- the outer cup's links unfolded over the inner state (nextFresh = nf + 3)
  show unionFindJoin (unionFindJoin (stepCupArc state lowPosition).links (state.nextFresh + 3)
        (state.nextFresh + 3 + 1)) (state.nextFresh + 3 + 2) (state.nextFresh + 3)
      = (state.nextFresh + 5, state.nextFresh + 4) :: (state.nextFresh + 3, state.nextFresh + 4)
        :: (state.nextFresh + 2, state.nextFresh + 1) :: (state.nextFresh, state.nextFresh + 1)
        :: state.links
  rw [innerLinks]
  -- children of the inner forest `M2 = (nf+2, nf+1) :: (nf, nf+1) :: orig` are all `< nf + 3`
  have childrenBelowM2 : ∀ edge ∈ (state.nextFresh + 2, state.nextFresh + 1)
        :: (state.nextFresh, state.nextFresh + 1) :: state.links, edge.1 < state.nextFresh + 3 := by
    intro edge he
    cases he with
    | head => exact Nat.add_lt_add_left (by decide) state.nextFresh
    | tail _ heRest =>
        cases heRest with
        | head => exact Nat.lt_add_of_pos_right (by decide)
        | tail _ heRest2 =>
            exact Nat.lt_trans ((fresh.2.1 edge heRest2).1) (Nat.lt_add_of_pos_right (by decide))
  have forestM2 : isUnionFindForest ((state.nextFresh + 2, state.nextFresh + 1)
      :: (state.nextFresh, state.nextFresh + 1) :: state.links) := innerLinks ▸ innerForest
  -- inner-outer join J3: unionFindJoin M2 (nf+3) (nf+4) = (nf+3, nf+4) :: M2
  have plNf3M2 : unionFindParent ((state.nextFresh + 2, state.nextFresh + 1)
      :: (state.nextFresh, state.nextFresh + 1) :: state.links) (state.nextFresh + 3) = none :=
    unionFindParent_none_of_lt (state.nextFresh + 3) _ childrenBelowM2 (state.nextFresh + 3) (Nat.le_refl _)
  have plNf4M2 : unionFindParent ((state.nextFresh + 2, state.nextFresh + 1)
      :: (state.nextFresh, state.nextFresh + 1) :: state.links) (state.nextFresh + 4) = none :=
    unionFindParent_none_of_lt (state.nextFresh + 3) _ childrenBelowM2 (state.nextFresh + 4)
      (Nat.add_le_add_left (by decide) state.nextFresh)
  have rootNf3M2 : unionFindRootOf ((state.nextFresh + 2, state.nextFresh + 1)
      :: (state.nextFresh, state.nextFresh + 1) :: state.links) (state.nextFresh + 3) = state.nextFresh + 3 :=
    unionFindRootOf_of_parentless _ (state.nextFresh + 3) plNf3M2
  have rootNf4M2 : unionFindRootOf ((state.nextFresh + 2, state.nextFresh + 1)
      :: (state.nextFresh, state.nextFresh + 1) :: state.links) (state.nextFresh + 4) = state.nextFresh + 4 :=
    unionFindRootOf_of_parentless _ (state.nextFresh + 4) plNf4M2
  have distinctNf3Nf4 : ¬ (state.nextFresh + 3 == state.nextFresh + 4) = true :=
    natBeqNeTrue (Nat.ne_of_lt (Nat.add_lt_add_left (by decide) state.nextFresh))
  have joinThree : unionFindJoin ((state.nextFresh + 2, state.nextFresh + 1)
        :: (state.nextFresh, state.nextFresh + 1) :: state.links) (state.nextFresh + 3) (state.nextFresh + 3 + 1)
      = (state.nextFresh + 3, state.nextFresh + 4) :: (state.nextFresh + 2, state.nextFresh + 1)
        :: (state.nextFresh, state.nextFresh + 1) :: state.links :=
    unionFindJoin_cons_of_roots _ (state.nextFresh + 3) (state.nextFresh + 3 + 1) (state.nextFresh + 3)
      (state.nextFresh + 4) rootNf3M2 rootNf4M2 distinctNf3Nf4
  rw [joinThree]
  -- outer event join J4: unionFindJoin M3 (nf+5) (nf+3) = (nf+5, nf+4) :: M3, event's nf+3 → nf+4
  have childrenBelowM3 : ∀ edge ∈ (state.nextFresh + 3, state.nextFresh + 4)
        :: (state.nextFresh + 2, state.nextFresh + 1) :: (state.nextFresh, state.nextFresh + 1) :: state.links,
      edge.1 < state.nextFresh + 4 := by
    intro edge he
    cases he with
    | head => exact Nat.add_lt_add_left (by decide) state.nextFresh
    | tail _ heRest => exact Nat.lt_trans (childrenBelowM2 edge heRest) (Nat.add_lt_add_left (by decide) state.nextFresh)
  have plNf5M3 : unionFindParent ((state.nextFresh + 3, state.nextFresh + 4)
      :: (state.nextFresh + 2, state.nextFresh + 1) :: (state.nextFresh, state.nextFresh + 1) :: state.links)
      (state.nextFresh + 5) = none :=
    unionFindParent_none_of_lt (state.nextFresh + 4) _ childrenBelowM3 (state.nextFresh + 5)
      (Nat.add_le_add_left (by decide) state.nextFresh)
  have rootNf5M3 : unionFindRootOf ((state.nextFresh + 3, state.nextFresh + 4)
      :: (state.nextFresh + 2, state.nextFresh + 1) :: (state.nextFresh, state.nextFresh + 1) :: state.links)
      (state.nextFresh + 5) = state.nextFresh + 5 :=
    unionFindRootOf_of_parentless _ (state.nextFresh + 5) plNf5M3
  -- the event node `nf+3`'s root in M3 is `nf+4` (M3 head edge `nf+3 → nf+4`, then `nf+4` parentless)
  have forestM3 : isUnionFindForest ((state.nextFresh + 3, state.nextFresh + 4)
      :: (state.nextFresh + 2, state.nextFresh + 1) :: (state.nextFresh, state.nextFresh + 1) :: state.links) :=
    ⟨plNf3M2, plNf4M2, distinctNf3Nf4, forestM2⟩
  have rootNf3M3 : unionFindRootOf ((state.nextFresh + 3, state.nextFresh + 4)
      :: (state.nextFresh + 2, state.nextFresh + 1) :: (state.nextFresh, state.nextFresh + 1) :: state.links)
      (state.nextFresh + 3) = state.nextFresh + 4 := by
    rw [unionFindRootOf_consJoin ((state.nextFresh + 2, state.nextFresh + 1)
        :: (state.nextFresh, state.nextFresh + 1) :: state.links) (state.nextFresh + 3) (state.nextFresh + 4)
        forestM2 plNf3M2 plNf4M2 distinctNf3Nf4 (state.nextFresh + 3), rootNf3M2,
      if_pos (natBeqSelf (state.nextFresh + 3))]
  have distinctNf5Nf4 : ¬ (state.nextFresh + 5 == state.nextFresh + 4) = true :=
    natBeqNeTrue (Nat.ne_of_gt (Nat.add_lt_add_left (by decide) state.nextFresh))
  exact unionFindJoin_cons_of_roots _ (state.nextFresh + 3 + 2) (state.nextFresh + 3) (state.nextFresh + 5)
    (state.nextFresh + 4) rootNf5M3 rootNf3M3 distinctNf5Nf4

end FX1Poly.Polygraph
