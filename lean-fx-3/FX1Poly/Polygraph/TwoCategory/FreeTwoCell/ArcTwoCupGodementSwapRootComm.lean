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

/-! ## C2 — the `rootComm` union-find automorphism of the two-cup shared forest

`blockRotate nf 3 3` — the swap of block1 `[nf, nf+3)` with block2 `[nf+3, nf+6)`, fixing base and tail — is a
union-find automorphism of `L' = (nf+5, nf+4) :: (nf+3, nf+4) :: (nf+2, nf+1) :: (nf, nf+1) :: orig`.  The 4-edge
port of `MatchingCupSwapRootComm.blockSwap_rootComm`: the four nested `unionFindRootOf_consJoin` give the closed
root table (block1 ⇒ `nf+1`, block2 ⇒ `nf+4`, base/tail unchanged), and the finite case analysis on where `x`
sits relative to `nf … nf+5` discharges the equivariance `root(σ x) = σ(root x)` in every zone using the
block-rotation read-offs. -/

/-- ★ **The cup-restricted `rootComm` (the residual-(2) heart), general form.**  Over a fresh forest `orig`
(every edge endpoint `< nf`), the block rotation `blockRotate nf 3 3` is a union-find automorphism of the two-cup
shared forest `L' = (nf+5, nf+4) :: (nf+3, nf+4) :: (nf+2, nf+1) :: (nf, nf+1) :: orig`:

  `unionFindRootOf L' (blockRotate nf 3 3 x) = blockRotate nf 3 3 (unionFindRootOf L' x)`.

This is the CUP restriction of the machine-refuted general `MatchingGodementCoreSwapSim.rootComm` (the cap MERGE
flips a merged root with the join order); TRUE here because cups allocate FRESH legs, so `σ` swaps the two
disjoint fresh three-id blocks (roots `nf+1 ↔ nf+4`) and fixes base and tail.  The printed
equivariance-of-a-definable-map identity `f(g·x) = g·f(x)` (Nominal Sets), instantiated by `f = root`, `g = σ`. -/
theorem twoCupGodement_rootComm (nf : Nat) (orig : List (Nat × Nat))
    (origBelow : ∀ edge ∈ orig, edge.1 < nf ∧ edge.2 < nf)
    (origForest : isUnionFindForest orig) :
    ∀ x, unionFindRootOf ((nf + 5, nf + 4) :: (nf + 3, nf + 4) :: (nf + 2, nf + 1) :: (nf, nf + 1) :: orig)
        (blockRotate nf 3 3 x)
       = blockRotate nf 3 3 (unionFindRootOf ((nf + 5, nf + 4) :: (nf + 3, nf + 4) :: (nf + 2, nf + 1)
          :: (nf, nf + 1) :: orig) x) := by
  have childrenBelow : ∀ edge ∈ orig, edge.1 < nf := fun edge he => (origBelow edge he).1
  have parentsBelow : ∀ edge ∈ orig, edge.2 < nf := fun edge he => (origBelow edge he).2
  -- children-below bounds up the tower
  have childrenBelowL1 : ∀ edge ∈ (nf, nf + 1) :: orig, edge.1 < nf + 1 := by
    intro edge he
    cases he with
    | head => exact Nat.lt_add_of_pos_right (by decide)
    | tail _ heRest => exact Nat.lt_trans (childrenBelow edge heRest) (Nat.lt_add_of_pos_right (by decide))
  have childrenBelowL2 : ∀ edge ∈ (nf + 2, nf + 1) :: (nf, nf + 1) :: orig, edge.1 < nf + 3 := by
    intro edge he
    cases he with
    | head => exact Nat.add_lt_add_left (by decide) nf
    | tail _ heRest =>
        cases heRest with
        | head => exact Nat.lt_add_of_pos_right (by decide)
        | tail _ heRest2 => exact Nat.lt_trans (childrenBelow edge heRest2) (Nat.lt_add_of_pos_right (by decide))
  have childrenBelowL3 : ∀ edge ∈ (nf + 3, nf + 4) :: (nf + 2, nf + 1) :: (nf, nf + 1) :: orig, edge.1 < nf + 4 := by
    intro edge he
    cases he with
    | head => exact Nat.add_lt_add_left (by decide) nf
    | tail _ heRest => exact Nat.lt_trans (childrenBelowL2 edge heRest) (Nat.add_lt_add_left (by decide) nf)
  -- parentless facts at each level
  have plNf : unionFindParent orig nf = none :=
    unionFindParent_none_of_lt nf orig childrenBelow nf (Nat.le_refl _)
  have plNf1 : unionFindParent orig (nf + 1) = none :=
    unionFindParent_none_of_lt nf orig childrenBelow (nf + 1) (Nat.le_add_right _ _)
  have plNf1L1 : unionFindParent ((nf, nf + 1) :: orig) (nf + 1) = none :=
    unionFindParent_none_of_lt (nf + 1) _ childrenBelowL1 (nf + 1) (Nat.le_refl _)
  have plNf2L1 : unionFindParent ((nf, nf + 1) :: orig) (nf + 2) = none :=
    unionFindParent_none_of_lt (nf + 1) _ childrenBelowL1 (nf + 2) (Nat.add_le_add_left (by decide) nf)
  have plNf3L2 : unionFindParent ((nf + 2, nf + 1) :: (nf, nf + 1) :: orig) (nf + 3) = none :=
    unionFindParent_none_of_lt (nf + 3) _ childrenBelowL2 (nf + 3) (Nat.le_refl _)
  have plNf4L2 : unionFindParent ((nf + 2, nf + 1) :: (nf, nf + 1) :: orig) (nf + 4) = none :=
    unionFindParent_none_of_lt (nf + 3) _ childrenBelowL2 (nf + 4) (Nat.add_le_add_left (by decide) nf)
  have plNf5L2 : unionFindParent ((nf + 2, nf + 1) :: (nf, nf + 1) :: orig) (nf + 5) = none :=
    unionFindParent_none_of_lt (nf + 3) _ childrenBelowL2 (nf + 5) (Nat.add_le_add_left (by decide) nf)
  have plNf4L3 : unionFindParent ((nf + 3, nf + 4) :: (nf + 2, nf + 1) :: (nf, nf + 1) :: orig) (nf + 4) = none :=
    unionFindParent_none_of_lt (nf + 4) _ childrenBelowL3 (nf + 4) (Nat.le_refl _)
  have plNf5L3 : unionFindParent ((nf + 3, nf + 4) :: (nf + 2, nf + 1) :: (nf, nf + 1) :: orig) (nf + 5) = none :=
    unionFindParent_none_of_lt (nf + 4) _ childrenBelowL3 (nf + 5) (Nat.add_le_add_left (by decide) nf)
  -- distinctness facts (¬ (a == b) = true)
  have dNf01 : ¬ (nf == nf + 1) = true := natBeqNeTrue (Nat.ne_of_lt (Nat.lt_add_of_pos_right (by decide)))
  have dNf02 : ¬ (nf == nf + 2) = true := natBeqNeTrue (Nat.ne_of_lt (Nat.lt_add_of_pos_right (by decide)))
  have dNf21 : ¬ (nf + 2 == nf + 1) = true := natBeqNeTrue (Nat.ne_of_gt (Nat.add_lt_add_left (by decide) nf))
  have dNf31 : ¬ (nf + 3 == nf + 1) = true := natBeqNeTrue (Nat.ne_of_gt (Nat.add_lt_add_left (by decide) nf))
  have dNf34 : ¬ (nf + 3 == nf + 4) = true := natBeqNeTrue (Nat.ne_of_lt (Nat.add_lt_add_left (by decide) nf))
  have dNf35 : ¬ (nf + 3 == nf + 5) = true := natBeqNeTrue (Nat.ne_of_lt (Nat.add_lt_add_left (by decide) nf))
  have dNf51 : ¬ (nf + 5 == nf + 1) = true := natBeqNeTrue (Nat.ne_of_gt (Nat.add_lt_add_left (by decide) nf))
  have dNf54 : ¬ (nf + 5 == nf + 4) = true := natBeqNeTrue (Nat.ne_of_gt (Nat.add_lt_add_left (by decide) nf))
  -- forests up the tower
  have forestL1 : isUnionFindForest ((nf, nf + 1) :: orig) := ⟨plNf, plNf1, dNf01, origForest⟩
  have forestL2 : isUnionFindForest ((nf + 2, nf + 1) :: (nf, nf + 1) :: orig) :=
    ⟨plNf2L1, plNf1L1, dNf21, forestL1⟩
  have forestL3 : isUnionFindForest ((nf + 3, nf + 4) :: (nf + 2, nf + 1) :: (nf, nf + 1) :: orig) :=
    ⟨plNf3L2, plNf4L2, dNf34, forestL2⟩
  -- the four consJoin root laws
  have rootL1 : ∀ node, unionFindRootOf ((nf, nf + 1) :: orig) node
      = if nf == unionFindRootOf orig node then nf + 1 else unionFindRootOf orig node := fun node =>
    unionFindRootOf_consJoin orig nf (nf + 1) origForest plNf plNf1 dNf01 node
  have rootL2 : ∀ node, unionFindRootOf ((nf + 2, nf + 1) :: (nf, nf + 1) :: orig) node
      = if nf + 2 == unionFindRootOf ((nf, nf + 1) :: orig) node then nf + 1
        else unionFindRootOf ((nf, nf + 1) :: orig) node := fun node =>
    unionFindRootOf_consJoin ((nf, nf + 1) :: orig) (nf + 2) (nf + 1) forestL1 plNf2L1 plNf1L1 dNf21 node
  have rootL3 : ∀ node, unionFindRootOf ((nf + 3, nf + 4) :: (nf + 2, nf + 1) :: (nf, nf + 1) :: orig) node
      = if nf + 3 == unionFindRootOf ((nf + 2, nf + 1) :: (nf, nf + 1) :: orig) node then nf + 4
        else unionFindRootOf ((nf + 2, nf + 1) :: (nf, nf + 1) :: orig) node := fun node =>
    unionFindRootOf_consJoin ((nf + 2, nf + 1) :: (nf, nf + 1) :: orig) (nf + 3) (nf + 4) forestL2 plNf3L2 plNf4L2
      dNf34 node
  have rootL4 : ∀ node,
      unionFindRootOf ((nf + 5, nf + 4) :: (nf + 3, nf + 4) :: (nf + 2, nf + 1) :: (nf, nf + 1) :: orig) node
      = if nf + 5 == unionFindRootOf ((nf + 3, nf + 4) :: (nf + 2, nf + 1) :: (nf, nf + 1) :: orig) node then nf + 4
        else unionFindRootOf ((nf + 3, nf + 4) :: (nf + 2, nf + 1) :: (nf, nf + 1) :: orig) node := fun node =>
    unionFindRootOf_consJoin ((nf + 3, nf + 4) :: (nf + 2, nf + 1) :: (nf, nf + 1) :: orig) (nf + 5) (nf + 4)
      forestL3 plNf5L3 plNf4L3 dNf54 node
  -- base / tail roots
  have rootOrigGe : ∀ node, nf ≤ node → unionFindRootOf orig node = node := fun node hle =>
    unionFindRootOf_of_parentless orig node (unionFindParent_none_of_lt nf orig childrenBelow node hle)
  have rootOrigLt : ∀ node, node < nf → unionFindRootOf orig node < nf := fun node hlt =>
    unionFindRootOf_lt_of_fresh orig nf parentsBelow node hlt
  -- block1 root chain (nf, nf+1, nf+2 → nf+1)
  have rootL1_nf : unionFindRootOf ((nf, nf + 1) :: orig) nf = nf + 1 := by
    rw [rootL1 nf, rootOrigGe nf (Nat.le_refl _), if_pos (natBeqSelf nf)]
  have rootL1_nf1 : unionFindRootOf ((nf, nf + 1) :: orig) (nf + 1) = nf + 1 := by
    rw [rootL1 (nf + 1), rootOrigGe (nf + 1) (Nat.le_add_right _ _), if_neg dNf01]
  have rootL1_nf2 : unionFindRootOf ((nf, nf + 1) :: orig) (nf + 2) = nf + 2 := by
    rw [rootL1 (nf + 2), rootOrigGe (nf + 2) (Nat.le_add_right _ _), if_neg dNf02]
  have rootL2_nf : unionFindRootOf ((nf + 2, nf + 1) :: (nf, nf + 1) :: orig) nf = nf + 1 := by
    rw [rootL2 nf, rootL1_nf, if_neg dNf21]
  have rootL2_nf1 : unionFindRootOf ((nf + 2, nf + 1) :: (nf, nf + 1) :: orig) (nf + 1) = nf + 1 := by
    rw [rootL2 (nf + 1), rootL1_nf1, if_neg dNf21]
  have rootL2_nf2 : unionFindRootOf ((nf + 2, nf + 1) :: (nf, nf + 1) :: orig) (nf + 2) = nf + 1 := by
    rw [rootL2 (nf + 2), rootL1_nf2, if_pos (natBeqSelf (nf + 2))]
  -- block2 roots in L2 (parentless: fresh above)
  have rootL2_nf3 : unionFindRootOf ((nf + 2, nf + 1) :: (nf, nf + 1) :: orig) (nf + 3) = nf + 3 :=
    unionFindRootOf_of_parentless _ (nf + 3) plNf3L2
  have rootL2_nf4 : unionFindRootOf ((nf + 2, nf + 1) :: (nf, nf + 1) :: orig) (nf + 4) = nf + 4 :=
    unionFindRootOf_of_parentless _ (nf + 4) plNf4L2
  have rootL2_nf5 : unionFindRootOf ((nf + 2, nf + 1) :: (nf, nf + 1) :: orig) (nf + 5) = nf + 5 :=
    unionFindRootOf_of_parentless _ (nf + 5) plNf5L2
  -- L3 adds edge (nf+3, nf+4): block1 stays nf+1, block2 collapses nf+3 → nf+4
  have rootL3_nf : unionFindRootOf ((nf + 3, nf + 4) :: (nf + 2, nf + 1) :: (nf, nf + 1) :: orig) nf = nf + 1 := by
    rw [rootL3 nf, rootL2_nf, if_neg dNf31]
  have rootL3_nf1 : unionFindRootOf ((nf + 3, nf + 4) :: (nf + 2, nf + 1) :: (nf, nf + 1) :: orig) (nf + 1)
      = nf + 1 := by rw [rootL3 (nf + 1), rootL2_nf1, if_neg dNf31]
  have rootL3_nf2 : unionFindRootOf ((nf + 3, nf + 4) :: (nf + 2, nf + 1) :: (nf, nf + 1) :: orig) (nf + 2)
      = nf + 1 := by rw [rootL3 (nf + 2), rootL2_nf2, if_neg dNf31]
  have rootL3_nf3 : unionFindRootOf ((nf + 3, nf + 4) :: (nf + 2, nf + 1) :: (nf, nf + 1) :: orig) (nf + 3)
      = nf + 4 := by rw [rootL3 (nf + 3), rootL2_nf3, if_pos (natBeqSelf (nf + 3))]
  have rootL3_nf4 : unionFindRootOf ((nf + 3, nf + 4) :: (nf + 2, nf + 1) :: (nf, nf + 1) :: orig) (nf + 4)
      = nf + 4 := by rw [rootL3 (nf + 4), rootL2_nf4, if_neg dNf34]
  have rootL3_nf5 : unionFindRootOf ((nf + 3, nf + 4) :: (nf + 2, nf + 1) :: (nf, nf + 1) :: orig) (nf + 5)
      = nf + 5 := by rw [rootL3 (nf + 5), rootL2_nf5, if_neg dNf35]
  -- L' adds edge (nf+5, nf+4): block2's nf+5 collapses to nf+4, block1 unchanged
  have rootLp_nf : unionFindRootOf ((nf + 5, nf + 4) :: (nf + 3, nf + 4) :: (nf + 2, nf + 1) :: (nf, nf + 1) :: orig)
      nf = nf + 1 := by rw [rootL4 nf, rootL3_nf, if_neg dNf51]
  have rootLp_nf1 : unionFindRootOf ((nf + 5, nf + 4) :: (nf + 3, nf + 4) :: (nf + 2, nf + 1) :: (nf, nf + 1)
      :: orig) (nf + 1) = nf + 1 := by rw [rootL4 (nf + 1), rootL3_nf1, if_neg dNf51]
  have rootLp_nf2 : unionFindRootOf ((nf + 5, nf + 4) :: (nf + 3, nf + 4) :: (nf + 2, nf + 1) :: (nf, nf + 1)
      :: orig) (nf + 2) = nf + 1 := by rw [rootL4 (nf + 2), rootL3_nf2, if_neg dNf51]
  have rootLp_nf3 : unionFindRootOf ((nf + 5, nf + 4) :: (nf + 3, nf + 4) :: (nf + 2, nf + 1) :: (nf, nf + 1)
      :: orig) (nf + 3) = nf + 4 := by rw [rootL4 (nf + 3), rootL3_nf3, if_neg dNf54]
  have rootLp_nf4 : unionFindRootOf ((nf + 5, nf + 4) :: (nf + 3, nf + 4) :: (nf + 2, nf + 1) :: (nf, nf + 1)
      :: orig) (nf + 4) = nf + 4 := by rw [rootL4 (nf + 4), rootL3_nf4, if_neg dNf54]
  have rootLp_nf5 : unionFindRootOf ((nf + 5, nf + 4) :: (nf + 3, nf + 4) :: (nf + 2, nf + 1) :: (nf, nf + 1)
      :: orig) (nf + 5) = nf + 4 := by rw [rootL4 (nf + 5), rootL3_nf5, if_pos (natBeqSelf (nf + 5))]
  -- the block-rotation per-id read-offs (block1 shifts up by 3, block2 shifts down by 3)
  have sig0 : blockRotate nf 3 3 nf = nf + 3 :=
    blockRotate_firstBlock nf 3 3 nf (Nat.le_refl _) (Nat.lt_add_of_pos_right (by decide))
  have sig1 : blockRotate nf 3 3 (nf + 1) = nf + 4 :=
    blockRotate_firstBlock nf 3 3 (nf + 1) (Nat.le_add_right _ _) (Nat.add_lt_add_left (by decide) nf)
  have sig2 : blockRotate nf 3 3 (nf + 2) = nf + 5 :=
    blockRotate_firstBlock nf 3 3 (nf + 2) (Nat.le_add_right _ _) (Nat.add_lt_add_left (by decide) nf)
  have sig3 : blockRotate nf 3 3 (nf + 3) = nf := by
    rw [blockRotate_secondBlock nf 3 3 (nf + 3) (Nat.le_refl _) (Nat.lt_add_of_pos_right (by decide))]
    exact addSubCancelRight nf 3
  have sig4 : blockRotate nf 3 3 (nf + 4) = nf + 1 := by
    have hlo : nf + 3 ≤ nf + 4 := Nat.add_le_add_left (by decide) nf
    have hhi : nf + 4 < nf + 3 + 3 := by show nf + 4 < nf + 6; exact Nat.add_lt_add_left (by decide) nf
    rw [blockRotate_secondBlock nf 3 3 (nf + 4) hlo hhi]
    exact addSubCancelRight (nf + 1) 3
  have sig5 : blockRotate nf 3 3 (nf + 5) = nf + 2 := by
    have hlo : nf + 3 ≤ nf + 5 := Nat.add_le_add_left (by decide) nf
    have hhi : nf + 5 < nf + 3 + 3 := by show nf + 5 < nf + 6; exact Nat.add_lt_add_left (by decide) nf
    rw [blockRotate_secondBlock nf 3 3 (nf + 5) hlo hhi]
    exact addSubCancelRight (nf + 2) 3
  -- the main equivariance case analysis on where `x` sits among nf … nf+5
  intro x
  cases hbNf : x == nf with
  | true => rw [of_decide_eq_true hbNf, rootLp_nf, sig0, rootLp_nf3, sig1]
  | false =>
    cases hbNf1 : x == nf + 1 with
    | true => rw [of_decide_eq_true hbNf1, rootLp_nf1, sig1, rootLp_nf4]
    | false =>
      cases hbNf2 : x == nf + 2 with
      | true => rw [of_decide_eq_true hbNf2, rootLp_nf2, sig2, rootLp_nf5, sig1]
      | false =>
        cases hbNf3 : x == nf + 3 with
        | true => rw [of_decide_eq_true hbNf3, rootLp_nf3, sig3, rootLp_nf, sig4]
        | false =>
          cases hbNf4 : x == nf + 4 with
          | true => rw [of_decide_eq_true hbNf4, rootLp_nf4, sig4, rootLp_nf1]
          | false =>
            cases hbNf5 : x == nf + 5 with
            | true => rw [of_decide_eq_true hbNf5, rootLp_nf5, sig5, rootLp_nf2, sig4]
            | false =>
              cases Nat.lt_or_ge x nf with
              | inl hlt =>
                  have hRx : unionFindRootOf orig x < nf := rootOrigLt x hlt
                  have hL1x : unionFindRootOf ((nf, nf + 1) :: orig) x = unionFindRootOf orig x := by
                    rw [rootL1 x, if_neg (natBeqNeTrue (Nat.ne_of_gt hRx))]
                  have hL2x : unionFindRootOf ((nf + 2, nf + 1) :: (nf, nf + 1) :: orig) x
                      = unionFindRootOf orig x := by
                    rw [rootL2 x, hL1x,
                      if_neg (natBeqNeTrue (Nat.ne_of_gt (Nat.lt_of_lt_of_le hRx (Nat.le_add_right nf 2))))]
                  have hL3x : unionFindRootOf ((nf + 3, nf + 4) :: (nf + 2, nf + 1) :: (nf, nf + 1) :: orig) x
                      = unionFindRootOf orig x := by
                    rw [rootL3 x, hL2x,
                      if_neg (natBeqNeTrue (Nat.ne_of_gt (Nat.lt_of_lt_of_le hRx (Nat.le_add_right nf 3))))]
                  have hLpx : unionFindRootOf ((nf + 5, nf + 4) :: (nf + 3, nf + 4) :: (nf + 2, nf + 1)
                      :: (nf, nf + 1) :: orig) x = unionFindRootOf orig x := by
                    rw [rootL4 x, hL3x,
                      if_neg (natBeqNeTrue (Nat.ne_of_gt (Nat.lt_of_lt_of_le hRx (Nat.le_add_right nf 5))))]
                  rw [blockRotate_below nf 3 3 x hlt, hLpx, blockRotate_below nf 3 3 (unionFindRootOf orig x) hRx]
              | inr hge =>
                  have ge1 : nf + 1 ≤ x := Nat.lt_of_le_of_ne hge (neOfBeqFalse hbNf).symm
                  have ge2 : nf + 2 ≤ x := Nat.lt_of_le_of_ne ge1 (neOfBeqFalse hbNf1).symm
                  have ge3 : nf + 3 ≤ x := Nat.lt_of_le_of_ne ge2 (neOfBeqFalse hbNf2).symm
                  have ge4 : nf + 4 ≤ x := Nat.lt_of_le_of_ne ge3 (neOfBeqFalse hbNf3).symm
                  have ge5 : nf + 5 ≤ x := Nat.lt_of_le_of_ne ge4 (neOfBeqFalse hbNf4).symm
                  have ge6 : nf + 6 ≤ x := Nat.lt_of_le_of_ne ge5 (neOfBeqFalse hbNf5).symm
                  have hσx : blockRotate nf 3 3 x = x := blockRotate_above nf 3 3 x ge6
                  have hRx : unionFindRootOf orig x = x := rootOrigGe x hge
                  have hL1x : unionFindRootOf ((nf, nf + 1) :: orig) x = x := by
                    rw [rootL1 x, hRx, if_neg (natBeqNeTrue (fun h => (neOfBeqFalse hbNf) h.symm))]
                  have hL2x : unionFindRootOf ((nf + 2, nf + 1) :: (nf, nf + 1) :: orig) x = x := by
                    rw [rootL2 x, hL1x, if_neg (natBeqNeTrue (fun h => (neOfBeqFalse hbNf2) h.symm))]
                  have hL3x : unionFindRootOf ((nf + 3, nf + 4) :: (nf + 2, nf + 1) :: (nf, nf + 1) :: orig) x
                      = x := by rw [rootL3 x, hL2x, if_neg (natBeqNeTrue (fun h => (neOfBeqFalse hbNf3) h.symm))]
                  have hLpx : unionFindRootOf ((nf + 5, nf + 4) :: (nf + 3, nf + 4) :: (nf + 2, nf + 1)
                      :: (nf, nf + 1) :: orig) x = x := by
                    rw [rootL4 x, hL3x, if_neg (natBeqNeTrue (fun h => (neOfBeqFalse hbNf5) h.symm))]
                  rw [hσx, hLpx, hσx]

/-! ## C3 — the count fields ride on `rootComm`, and the full `ArcStepSimCount` bundle

The per-root cup/cap COUNT fields fall out of C2 via the shipped `countEventsInRoot_rootComm`: `σ` permutes the two
freshly-allocated cup events (`nf+2 ↔ nf+5`) and fixes the pre-existing cup/cap events (all `< nf`).  The cup
side needs one head-swap (the two fresh events are consed in the opposite order the `σ`-image lands them); the cap
side is direct (cups add no cap events, so `σ` fixes the whole cap-event list).  Assembling these with the two
shipped legs (open-wire block transform + link byte-identity companions) and the forest-preservation lemmas gives
the literal full 8-field `ArcStepSimCount` for the pure cup × cup Godement interchange. -/

/-- The per-root event count is BLIND to swapping the first two events (they add independently; `Nat.add_left_comm`
on the two indicator contributions).  The exact difference between `E_cup` and its `σ`-image for the two-cup swap. -/
theorem countEventsInRoot_swap_head (links : List (Nat × Nat)) (rootHere a b : Nat) (rest : List Nat) :
    countEventsInRoot links rootHere (a :: b :: rest) = countEventsInRoot links rootHere (b :: a :: rest) := by
  show (if unionFindRootOf links a == rootHere then 1 else 0)
        + ((if unionFindRootOf links b == rootHere then 1 else 0) + countEventsInRoot links rootHere rest)
     = (if unionFindRootOf links b == rootHere then 1 else 0)
        + ((if unionFindRootOf links a == rootHere then 1 else 0) + countEventsInRoot links rootHere rest)
  rw [Nat.add_left_comm]

/-- ★ **The FULL pure cup × cup Godement swap `ArcStepSimCount` bundle** — all eight fields at general parameters
(`state`, `lowPosition`, `gap`) under the freshness / disjoint-window / forest side-conditions.  `openMap` is the
shipped open-wire block transform; `nfEq` / `loopsEq` and the count fields' links are the shipped byte-identity
companions; `rootComm` is the C2 automorphism (`twoCupGodement_rootComm` on the C1 concrete forest); `cupCorr` /
`capCorr` ride on `rootComm` through `countEventsInRoot_rootComm` (cup: one head-swap for the two fresh events;
cap: `σ` fixes the whole list); `forestS` / `forestT` from the cup-step forest preservation.  This is the literal
delivery that discharges the residual-(2) heart and flips `fxMode_hasArcTwoCupGodementSwapSim`. -/
theorem twoCupGodement_arcStepSimCount (state : ArcWireState) (lowPosition gap : Nat)
    (fresh : ArcStateFresh state) (window : gap + lowPosition ≤ state.openWires.length)
    (forest : isUnionFindForest state.links) :
    ArcStepSimCount (blockRotate state.nextFresh 3 3)
      (stepCupArc (stepCupArc state lowPosition) (gap + 2 + lowPosition))
      (stepCupArc (stepCupArc state (gap + lowPosition)) lowPosition) := by
  have hlinksRedex : (stepCupArc (stepCupArc state lowPosition) (gap + 2 + lowPosition)).links
      = (state.nextFresh + 5, state.nextFresh + 4) :: (state.nextFresh + 3, state.nextFresh + 4)
        :: (state.nextFresh + 2, state.nextFresh + 1) :: (state.nextFresh, state.nextFresh + 1) :: state.links :=
    twoCupArcLinks_cons state lowPosition gap fresh forest
  have hlinksReduct : (stepCupArc (stepCupArc state (gap + lowPosition)) lowPosition).links
      = (state.nextFresh + 5, state.nextFresh + 4) :: (state.nextFresh + 3, state.nextFresh + 4)
        :: (state.nextFresh + 2, state.nextFresh + 1) :: (state.nextFresh, state.nextFresh + 1) :: state.links :=
    (stepCupArc_stepCupArc_links_eq state lowPosition gap).symm.trans hlinksRedex
  have hRootLp := twoCupGodement_rootComm state.nextFresh state.links fresh.2.1 forest
  have hσinj := blockRotate_inj state.nextFresh 3 3
  have hEcup : (stepCupArc (stepCupArc state lowPosition) (gap + 2 + lowPosition)).cupEventNodes
      = (state.nextFresh + 5) :: (state.nextFresh + 2) :: state.cupEventNodes := rfl
  have hEcap : (stepCupArc (stepCupArc state lowPosition) (gap + 2 + lowPosition)).capEventNodes
      = state.capEventNodes := rfl
  -- the two fresh cup events map to each other; the pre-existing ones are fixed
  have s2 : blockRotate state.nextFresh 3 3 (state.nextFresh + 2) = state.nextFresh + 5 :=
    blockRotate_firstBlock state.nextFresh 3 3 (state.nextFresh + 2) (Nat.le_add_right _ _)
      (Nat.add_lt_add_left (by decide) state.nextFresh)
  have s5 : blockRotate state.nextFresh 3 3 (state.nextFresh + 5) = state.nextFresh + 2 := by
    have hlo : state.nextFresh + 3 ≤ state.nextFresh + 5 := Nat.add_le_add_left (by decide) state.nextFresh
    have hhi : state.nextFresh + 5 < state.nextFresh + 3 + 3 := by
      show state.nextFresh + 5 < state.nextFresh + 6; exact Nat.add_lt_add_left (by decide) state.nextFresh
    rw [blockRotate_secondBlock state.nextFresh 3 3 (state.nextFresh + 5) hlo hhi]
    exact addSubCancelRight (state.nextFresh + 2) 3
  have hEcupMap : ((state.nextFresh + 5) :: (state.nextFresh + 2) :: state.cupEventNodes).map
        (blockRotate state.nextFresh 3 3)
      = (state.nextFresh + 2) :: (state.nextFresh + 5) :: state.cupEventNodes := by
    show blockRotate state.nextFresh 3 3 (state.nextFresh + 5)
        :: blockRotate state.nextFresh 3 3 (state.nextFresh + 2)
        :: state.cupEventNodes.map (blockRotate state.nextFresh 3 3)
      = (state.nextFresh + 2) :: (state.nextFresh + 5) :: state.cupEventNodes
    rw [s5, s2, mapFixedOn (blockRotate state.nextFresh 3 3) state.cupEventNodes
      (fun node hn => blockRotate_fixesBelow state.nextFresh 3 3 node (fresh.2.2.1 node hn))]
  have hCapFix : state.capEventNodes.map (blockRotate state.nextFresh 3 3) = state.capEventNodes :=
    mapFixedOn (blockRotate state.nextFresh 3 3) state.capEventNodes
      (fun node hn => blockRotate_fixesBelow state.nextFresh 3 3 node (fresh.2.2.2 node hn))
  exact
    { openMap := stepCupArc_stepCupArc_openWires_blockSwap state lowPosition gap fresh window
      nfEq := stepCupArc_stepCupArc_nextFresh_eq state lowPosition gap
      rootComm := fun x => by rw [hlinksReduct, hlinksRedex]; exact hRootLp x
      loopsEq := (stepCupArc_stepCupArc_loops_eq state lowPosition gap).symm
      cupCorr := fun r => by
        rw [hlinksReduct, hlinksRedex, (stepCupArc_stepCupArc_cupEventNodes_eq state lowPosition gap).symm, hEcup]
        have key := countEventsInRoot_rootComm (blockRotate state.nextFresh 3 3) hσinj
          ((state.nextFresh + 5, state.nextFresh + 4) :: (state.nextFresh + 3, state.nextFresh + 4)
            :: (state.nextFresh + 2, state.nextFresh + 1) :: (state.nextFresh, state.nextFresh + 1) :: state.links)
          _ r hRootLp ((state.nextFresh + 5) :: (state.nextFresh + 2) :: state.cupEventNodes)
        rw [hEcupMap] at key
        rw [countEventsInRoot_swap_head _ (blockRotate state.nextFresh 3 3 r) (state.nextFresh + 5)
          (state.nextFresh + 2) state.cupEventNodes]
        exact key
      capCorr := fun r => by
        rw [hlinksReduct, hlinksRedex, (stepCupArc_stepCupArc_capEventNodes_eq state lowPosition gap).symm, hEcap]
        have key := countEventsInRoot_rootComm (blockRotate state.nextFresh 3 3) hσinj
          ((state.nextFresh + 5, state.nextFresh + 4) :: (state.nextFresh + 3, state.nextFresh + 4)
            :: (state.nextFresh + 2, state.nextFresh + 1) :: (state.nextFresh, state.nextFresh + 1) :: state.links)
          _ r hRootLp state.capEventNodes
        rw [hCapFix] at key
        exact key
      forestS := isUnionFindForest_stepCupArc (stepCupArc state lowPosition) (gap + 2 + lowPosition)
        (isUnionFindForest_stepCupArc state lowPosition forest)
      forestT := isUnionFindForest_stepCupArc (stepCupArc state (gap + lowPosition)) lowPosition
        (isUnionFindForest_stepCupArc state (gap + lowPosition) forest) }

/-! ## Non-vacuity — a concrete full bundle at the width-6 re-probe seed -/

/-- The concrete two-cup seed (width 6, `nextFresh = 6`) — the re-probe's seed, matching `ArcTwoCupGodementSwapWires`. -/
private def twoCupBundleSeed : ArcWireState := ArcWireState.mk (List.range 6) [] 6 0 [] []

/-- ★ Non-vacuity of the full bundle: at the concrete width-6 seed with the low cup at `1` and the high cup gap `2`
the eight-field `ArcStepSimCount` for `blockRotate 6 3 3` is inhabited — confirming the general theorem is not
vacuous. -/
theorem twoCupBundle_concrete :
    ArcStepSimCount (blockRotate 6 3 3)
      (stepCupArc (stepCupArc twoCupBundleSeed 1) 5) (stepCupArc (stepCupArc twoCupBundleSeed 3) 1) :=
  twoCupGodement_arcStepSimCount twoCupBundleSeed 1 2 (arcStateFresh_initial 6) (by decide) isUnionFindForest_nil

/-! ## Honesty markers -/

/-- **Honesty marker — the FULL pure-cup swap `ArcStepSimCount` bundle IS shipped (residual-(2) heart CLOSED).**
`twoCupGodement_arcStepSimCount` delivers all eight fields of `ArcStepSimCount (blockRotate state.nextFresh 3 3)
redex reduct` at general parameters (under freshness / disjoint-window / forest side-conditions): `rootComm` is the
union-find automorphism of the two-cup shared forest (`twoCupGodement_rootComm`, the C2 heart), and `cupCorr` /
`capCorr` ride on it via `countEventsInRoot_rootComm`.  Non-vacuous (`twoCupBundle_concrete`).  This is the literal
full-bundle delivery that flips `fxMode_hasArcTwoCupGodementSwapSim`.  `= true`. -/
def fxMode_hasArcTwoCupGodementSwapCountBundle : Bool := true

/-- **Honesty pin — the general keystone `:545` stays false FOREVER.** -/
theorem arcGodementSamePartitionFreshProof_staysFalse_rootComm :
    fxMode_hasArcGodementSamePartitionFreshProof = false := rfl

/-- **Honesty pin — the peel-general signature `:137` stays false FOREVER.** -/
theorem arcPeelGeneralSignature_staysFalse_rootComm : fxMode_hasArcPeelGeneralSignature = false := rfl

/-- **Honesty pin — residual (2)'s renameable-level marker `:3046` stays false FOREVER.**  The count-level bundle
above (`ArcStepSimCount`) is the LIVE vehicle; the refuted `renameState`-EQUALITY route
(`fxMode_hasArcGodementSwapRenameableProof2`) stays walled (the cap MERGE flips a merged root with the join order —
`MatchingSwapObstruction`), so the general Godement swap over cap-involving pairs is NOT clean. -/
theorem arcGodementSwapRenameableProof2_staysFalse_rootComm :
    fxMode_hasArcGodementSwapRenameableProof2 = false := rfl

end FX1Poly.Polygraph
