import FX1Poly.Polygraph.TwoCategory.WalkingString.StringFussCatalanFreshness

/-! # WalkingString — the union-find FOREST invariant + the FUEL NORMALIZATION (FC-3b, residual (i) CLOSED)

`fxString_hasCupPreservationFromFreshness` (in `StringFussCatalanFreshness`) named the exact remaining site of the CUP
half of `preserves`: the freshness kit ships `unionFindRoot_cons_freshAbove` as a MATCHED-fuel fact, but
`isSameComponent` reads `unionFindRootOf`, which pins the fuel to `links.length + 1`, so comparing a root under the
extended `((fc,fp)::links)` (fuel `links.length + 2`) to the root under `links` (fuel `links.length + 1`) needs one
extra fuel step to be harmless — TRUE only because the union-find is a FOREST (acyclic).  That acyclicity is the
un-ported `ArcNonCrossingFold` / forest invariant.  This file PORTS the forest kit over the bare `WireState` (the
`ArcSwapRenameable` chain re-stated over the shared `unionFindParent` / `unionFindJoin`, `string`-prefixed to avoid
the D2a names), and CLOSES the fuel normalization:

  * the forest predicate `stringIsUnionFindForest` (every edge's endpoints are roots in the tail, endpoints distinct),
    with the empty-list base and the JOIN-preservation chain (`stringUnionFindForest_stepCup` / `_stepCap` /
    `_stepAtom` / `_processSpine`) — so every reachable fold state has acyclic `links`;
  * ★ the FUEL-SPLIT lemma `stringUnionFindRoot_fuelSplit` (`unionFindRoot (extraFuel + baseFuel) = unionFindRoot
    extraFuel ∘ unionFindRoot baseFuel`) and the FUEL-BUMP on a forest (`stringUnionFindRoot_fuelBump_of_forest`:
    fuel `links.length + 2` gives the same root as `links.length + 1`, because the root at `links.length + 1` is
    already parentless);
  * ★★ the COMPOSITE `stringIsSameComponent_cons_freshAbove_forest` — on a forest, adding a fresh edge whose child
    sits at/above a bound changes NO `isSameComponent` between two below-bound nodes.  This is exactly the "a fresh
    cup pair changes no old `isSameComponent`" fact the FC-3b residual (i) named, now at the `isSameComponent` fuel
    (`links.length + 1`), NOT merely at matched fuel.

Raw Lean 4 + Init; the forest chain is structural fuel/list recursion (ported from the shipped `ArcSwapRenameable`
proofs, re-derived over the shared union-find), the fuel-split is a clean structural recursion, the fuel-bump feeds
the shipped `unionFindRoot_of_parentNone`.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free
(the one commutation is `Nat.add_comm`, propext-clean); per-declaration `#assert_no_axioms` gated in the audit
twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The union-find FOREST predicate (re-stated over the bare `WireState`, `string`-prefixed) -/

/-- ★ **The union-find edge list forms a forest.**  Read head-to-tail, every edge's child AND parent are roots in the
edges strictly below it (parentless in the tail), and the two endpoints differ.  This is precisely the shape
`unionFindJoin` maintains — it only ever prepends a `root → root` edge between two distinct roots — and it is strong
enough to make every root chain settle.  Structural recursion on the edge list; propext-clean, reduces definitionally
on `cons`.  (The string port of the shipped `isUnionFindForest`.) -/
def stringIsUnionFindForest : List (Nat × Nat) → Prop
  | [] => True
  | edge :: rest =>
      unionFindParent rest edge.1 = none ∧ unionFindParent rest edge.2 = none
        ∧ ¬ (edge.1 == edge.2) = true ∧ stringIsUnionFindForest rest

/-- The empty edge list is a forest — the fold's initial `links`. -/
theorem stringIsUnionFindForest_nil : stringIsUnionFindForest ([] : List (Nat × Nat)) := trivial

/-! ## Root-following after prepending a disjoint root→root edge (the fuel-parametric base) -/

/-- ★ **Root-following after prepending a disjoint root→root edge**, conditional on the root-chain settling within
the fuel.  With `p`, `q` both parentless in `links` and `p ≠ q`, following `x` in `(p, q) :: links` lands on `q`
exactly when it lands on `p` in `links`, else unchanged.  Induction on `fuel`, casing the parent of `x`; the
`p`-collision case discharges via `unionFindRoot_of_parentNone`, the descent threads the inductive hypothesis.  (The
string port of the shipped `unionFindRoot_consJoin`.) -/
theorem stringUnionFindRoot_consJoin (links : List (Nat × Nat)) (p q : Nat)
    (pParentless : unionFindParent links p = none) (qParentless : unionFindParent links q = none)
    (distinct : ¬ (p == q) = true) :
    (fuel : Nat) → (x : Nat) → unionFindParent links (unionFindRoot fuel links x) = none →
    unionFindRoot (fuel + 1) ((p, q) :: links) x
      = (if p == unionFindRoot fuel links x then q else unionFindRoot fuel links x)
  | 0, x, settles => by
      show (match (if p == x then some q else unionFindParent links x) with
            | none => x | some parent => unionFindRoot 0 ((p, q) :: links) parent)
         = (if p == x then q else x)
      rw [show unionFindParent links x = none from settles]
      cases p == x with
      | true => rfl
      | false => rfl
  | fuel + 1, x, settles => by
      cases hpx : unionFindParent links x with
      | none =>
          rw [show unionFindRoot (fuel + 1) links x = x from
            unionFindRoot_of_parentNone links x hpx (fuel + 1)]
          show (match (if p == x then some q else unionFindParent links x) with
                | none => x | some parent => unionFindRoot (fuel + 1) ((p, q) :: links) parent)
             = (if p == x then q else x)
          rw [hpx]
          cases p == x with
          | true =>
              have hqParentlessCons : unionFindParent ((p, q) :: links) q = none := by
                show (if p == q then some q else unionFindParent links q) = none
                cases hpqc : p == q with
                | true => exact absurd hpqc distinct
                | false => exact qParentless
              exact unionFindRoot_of_parentNone ((p, q) :: links) q hqParentlessCons (fuel + 1)
          | false => rfl
      | some par =>
          have hxRoot : unionFindRoot (fuel + 1) links x = unionFindRoot fuel links par := by
            show (match unionFindParent links x with
                  | none => x | some parent => unionFindRoot fuel links parent)
               = unionFindRoot fuel links par
            rw [hpx]
          have settlesPar : unionFindParent links (unionFindRoot fuel links par) = none := by
            rw [← hxRoot]; exact settles
          show (match (if p == x then some q else unionFindParent links x) with
                | none => x | some parent => unionFindRoot (fuel + 1) ((p, q) :: links) parent)
             = (if p == unionFindRoot (fuel + 1) links x then q else unionFindRoot (fuel + 1) links x)
          rw [hpx, hxRoot]
          cases hpxc : p == x with
          | true =>
              have hpeqx : p = x := of_decide_eq_true hpxc
              rw [hpeqx] at pParentless
              rw [pParentless] at hpx
              nomatch hpx
          | false =>
              exact stringUnionFindRoot_consJoin links p q pParentless qParentless distinct fuel par settlesPar

/-! ## A forest settles: every node's root is parentless -/

/-- ★ **A forest settles: every node's root is parentless** — the acyclicity content.  Structural induction on the
edge list, the inductive hypothesis discharging the `settles` obligation of `stringUnionFindRoot_consJoin`.  (The
string port of the shipped `unionFindRootOf_parentless_of_forest`.) -/
theorem stringUnionFindRootOf_parentless_of_forest :
    (links : List (Nat × Nat)) → stringIsUnionFindForest links → (x : Nat) →
    unionFindParent links (unionFindRootOf links x) = none
  | [], _, _ => rfl
  | edge :: rest, hforest, x => by
      have hchild : unionFindParent rest edge.1 = none := hforest.1
      have hparent : unionFindParent rest edge.2 = none := hforest.2.1
      have hdistinct : ¬ (edge.1 == edge.2) = true := hforest.2.2.1
      have hrest : stringIsUnionFindForest rest := hforest.2.2.2
      have ih : unionFindParent rest (unionFindRootOf rest x) = none :=
        stringUnionFindRootOf_parentless_of_forest rest hrest x
      have key : unionFindRootOf (edge :: rest) x
          = (if edge.1 == unionFindRootOf rest x then edge.2 else unionFindRootOf rest x) :=
        stringUnionFindRoot_consJoin rest edge.1 edge.2 hchild hparent hdistinct (rest.length + 1) x ih
      rw [key]
      cases hcond : edge.1 == unionFindRootOf rest x with
      | true =>
          show (if edge.1 == edge.2 then some edge.2 else unionFindParent rest edge.2) = none
          cases hpair : edge.1 == edge.2 with
          | true => exact absurd hpair hdistinct
          | false => exact hparent
      | false =>
          show (if edge.1 == unionFindRootOf rest x then some edge.2
                  else unionFindParent rest (unionFindRootOf rest x)) = none
          cases hcond2 : edge.1 == unionFindRootOf rest x with
          | true => rw [hcond] at hcond2; exact Bool.noConfusion hcond2
          | false => exact ih

/-! ## The forest invariant is preserved by every fold step -/

/-- ★ **The union-find JOIN preserves the forest invariant.**  When already joined the links are returned verbatim;
otherwise the prepended edge `(rootFirst, rootSecond)` has both endpoints parentless
(`stringUnionFindRootOf_parentless_of_forest`) and distinct (the else-branch test).  (The string port of
`isUnionFindForest_unionFindJoin`.) -/
theorem stringUnionFindForest_unionFindJoin (links : List (Nat × Nat)) (firstNode secondNode : Nat)
    (hforest : stringIsUnionFindForest links) :
    stringIsUnionFindForest (unionFindJoin links firstNode secondNode) := by
  show stringIsUnionFindForest
      (if unionFindRootOf links firstNode == unionFindRootOf links secondNode then links
        else (unionFindRootOf links firstNode, unionFindRootOf links secondNode) :: links)
  cases hcond : unionFindRootOf links firstNode == unionFindRootOf links secondNode with
  | true => exact hforest
  | false =>
      show unionFindParent links (unionFindRootOf links firstNode) = none
        ∧ unionFindParent links (unionFindRootOf links secondNode) = none
        ∧ ¬ (unionFindRootOf links firstNode == unionFindRootOf links secondNode) = true
        ∧ stringIsUnionFindForest links
      refine ⟨stringUnionFindRootOf_parentless_of_forest links hforest firstNode,
        stringUnionFindRootOf_parentless_of_forest links hforest secondNode, ?_, hforest⟩
      intro htrue
      rw [hcond] at htrue
      exact Bool.noConfusion htrue

/-- A CUP step preserves the forest invariant — its `links` is a single `unionFindJoin` over `state.links`. -/
theorem stringUnionFindForest_stepCup (state : WireState) (position : Nat)
    (hforest : stringIsUnionFindForest state.links) :
    stringIsUnionFindForest (stepCup state position).links := by
  show stringIsUnionFindForest (unionFindJoin state.links state.nextFresh (state.nextFresh + 1))
  exact stringUnionFindForest_unionFindJoin state.links state.nextFresh (state.nextFresh + 1) hforest

/-- A CAP step preserves the forest invariant — its `links` is unchanged (loop branch) or a single `unionFindJoin`. -/
theorem stringUnionFindForest_stepCap (state : WireState) (position : Nat)
    (hforest : stringIsUnionFindForest state.links) :
    stringIsUnionFindForest (stepCap state position).links := by
  dsimp only [stepCap]
  split
  · exact hforest
  · exact stringUnionFindForest_unionFindJoin state.links
      (natListGetAt state.openWires position) (natListGetAt state.openWires (position + 1)) hforest

/-- ★ **One atom preserves the forest invariant** — cup / cap via the join lemmas, a generic box leaves `links`
untouched. -/
theorem stringUnionFindForest_stepAtom {sourceMode targetMode : AdjointTripleMode}
    (state : WireState) (atom : SpineAtom adjointTripleModeSignature sourceMode targetMode)
    (hforest : stringIsUnionFindForest state.links) :
    stringIsUnionFindForest (stepAtom state atom).links := by
  dsimp only [stepAtom]
  split
  · exact stringUnionFindForest_stepCup state _ hforest
  · exact stringUnionFindForest_stepCap state _ hforest
  · exact hforest

/-- ★ **The whole fold preserves the forest invariant** — structural recursion on the spine, threading
`stringUnionFindForest_stepAtom` through each atom. -/
theorem stringUnionFindForest_processSpine {sourceMode targetMode : AdjointTripleMode} :
    (atoms : List (SpineAtom adjointTripleModeSignature sourceMode targetMode)) → (state : WireState) →
    stringIsUnionFindForest state.links → stringIsUnionFindForest (processSpine state atoms).links
  | [], _, hforest => hforest
  | atom :: rest, state, hforest => by
      show stringIsUnionFindForest (processSpine (stepAtom state atom) rest).links
      exact stringUnionFindForest_processSpine rest (stepAtom state atom)
        (stringUnionFindForest_stepAtom state atom hforest)

/-- ★ **The fresh seed is a forest** — the initial `links` is empty. -/
theorem stringInitialWireState_isUnionFindForest (bottomCount : Nat) :
    stringIsUnionFindForest (stringInitialWireState bottomCount).links :=
  trivial

/-- ★ **Every reachable fold state (from the fresh seed) has acyclic `links`.**  The forest invariant is the base
`stringInitialWireState_isUnionFindForest`, threaded through the fold by `stringUnionFindForest_processSpine`. -/
theorem stringProcessSpine_isUnionFindForest_fromSeed {sourceMode targetMode : AdjointTripleMode}
    (bottomCount : Nat) (atoms : List (SpineAtom adjointTripleModeSignature sourceMode targetMode)) :
    stringIsUnionFindForest (processSpine (stringInitialWireState bottomCount) atoms).links :=
  stringUnionFindForest_processSpine atoms (stringInitialWireState bottomCount)
    (stringInitialWireState_isUnionFindForest bottomCount)

/-! ## ★ The FUEL NORMALIZATION — residual (i), CLOSED on a forest -/

/-- ★★ **The FUEL-SPLIT lemma.**  Running `unionFindRoot` with `extraFuel + baseFuel` steps equals running `baseFuel`
steps then `extraFuel` more from the result: `unionFindRoot (extraFuel + baseFuel) links x = unionFindRoot extraFuel
links (unionFindRoot baseFuel links x)`.  Structural recursion on `baseFuel` (matching `Nat.add`'s recursion on its
second summand, so the base is a clean `rfl`); the parentless case invokes `unionFindRoot_of_parentNone`, the descent
threads the inductive hypothesis through the shared parent.  Unconditional — no forest needed. -/
theorem stringUnionFindRoot_fuelSplit (extraFuel : Nat) (links : List (Nat × Nat)) :
    (baseFuel x : Nat) →
    unionFindRoot (extraFuel + baseFuel) links x
      = unionFindRoot extraFuel links (unionFindRoot baseFuel links x)
  | 0, x => by
      show unionFindRoot (extraFuel + 0) links x = unionFindRoot extraFuel links x
      rfl
  | baseFuel + 1, x => by
      cases hpx : unionFindParent links x with
      | none =>
          have rootBaseSucc : unionFindRoot (baseFuel + 1) links x = x := by
            show (match unionFindParent links x with
                  | none => x | some parent => unionFindRoot baseFuel links parent) = x
            rw [hpx]
          have rootBig : unionFindRoot (extraFuel + (baseFuel + 1)) links x = x := by
            show (match unionFindParent links x with
                  | none => x | some parent => unionFindRoot (extraFuel + baseFuel) links parent) = x
            rw [hpx]
          rw [rootBig, rootBaseSucc]
          exact (unionFindRoot_of_parentNone links x hpx extraFuel).symm
      | some par =>
          have rootBaseSucc : unionFindRoot (baseFuel + 1) links x = unionFindRoot baseFuel links par := by
            show (match unionFindParent links x with
                  | none => x | some parent => unionFindRoot baseFuel links parent)
               = unionFindRoot baseFuel links par
            rw [hpx]
          have rootBig : unionFindRoot (extraFuel + (baseFuel + 1)) links x
              = unionFindRoot (extraFuel + baseFuel) links par := by
            show (match unionFindParent links x with
                  | none => x | some parent => unionFindRoot (extraFuel + baseFuel) links parent)
               = unionFindRoot (extraFuel + baseFuel) links par
            rw [hpx]
          rw [rootBig, rootBaseSucc]
          exact stringUnionFindRoot_fuelSplit extraFuel links baseFuel par

/-- ★★ **The FUEL-BUMP on a forest.**  On a forest, one extra fuel step past `links.length + 1` changes no root:
`unionFindRoot (links.length + 2) links x = unionFindRoot (links.length + 1) links x`.  By the fuel-split (extra 1 on
top of `links.length + 1`) and the fact that the root at `links.length + 1` is already parentless
(`stringUnionFindRootOf_parentless_of_forest`), so the extra step is idempotent (`unionFindRoot_of_parentNone`). -/
theorem stringUnionFindRoot_fuelBump_of_forest (links : List (Nat × Nat))
    (hforest : stringIsUnionFindForest links) (x : Nat) :
    unionFindRoot (links.length + 2) links x = unionFindRoot (links.length + 1) links x := by
  have fuelEq : links.length + 2 = 1 + (links.length + 1) := (Nat.add_comm 1 (links.length + 1)).symm
  rw [fuelEq, stringUnionFindRoot_fuelSplit 1 links (links.length + 1) x]
  exact unionFindRoot_of_parentNone links (unionFindRoot (links.length + 1) links x)
    (stringUnionFindRootOf_parentless_of_forest links hforest x) 1

/-- ★★ **A fresh edge preserves every below-bound ROOT on a forest** (at the `isSameComponent` fuel).  Combining the
matched-fuel cons-invariance (`unionFindRoot_cons_freshAbove` at fuel `links.length + 2`) with the fuel-bump
(`links.length + 2 ↦ links.length + 1`), prepending `(freshChild, freshParent)` leaves `unionFindRootOf` unchanged on
any below-bound node.  This is the fuel-NORMALIZED form the FC-3b residual (i) named — no longer at matched fuel but
at the exact fuel `unionFindRootOf` pins. -/
theorem stringUnionFindRootOf_cons_freshAbove_forest (freshChild freshParent bound : Nat)
    (links : List (Nat × Nat))
    (parentsBounded : ∀ parent ∈ links.map Prod.snd, parent < bound) (boundLeFresh : bound ≤ freshChild)
    (hforest : stringIsUnionFindForest links) (node : Nat) (nodeBelow : node < bound) :
    unionFindRootOf ((freshChild, freshParent) :: links) node = unionFindRootOf links node := by
  show unionFindRoot (links.length + 2) ((freshChild, freshParent) :: links) node
    = unionFindRoot (links.length + 1) links node
  rw [unionFindRoot_cons_freshAbove freshChild freshParent bound links parentsBounded boundLeFresh
      (links.length + 2) node nodeBelow]
  exact stringUnionFindRoot_fuelBump_of_forest links hforest node

/-- ★★ **A fresh edge changes NO below-bound `isSameComponent` on a forest** (residual (i), the consumed form).
`isSameComponent` is the `unionFindRootOf`-equality, and both roots are preserved by
`stringUnionFindRootOf_cons_freshAbove_forest` — so a fresh cup edge is invisible to the connectivity of any two old
(below-bound) wires.  This is exactly "a fresh cup pair changes no old `isSameComponent`", CLOSED. -/
theorem stringIsSameComponent_cons_freshAbove_forest (freshChild freshParent bound : Nat)
    (links : List (Nat × Nat))
    (parentsBounded : ∀ parent ∈ links.map Prod.snd, parent < bound) (boundLeFresh : bound ≤ freshChild)
    (hforest : stringIsUnionFindForest links) (nodeA nodeB : Nat)
    (nodeABelow : nodeA < bound) (nodeBBelow : nodeB < bound) :
    isSameComponent ((freshChild, freshParent) :: links) nodeA nodeB = isSameComponent links nodeA nodeB := by
  show (unionFindRootOf ((freshChild, freshParent) :: links) nodeA
        == unionFindRootOf ((freshChild, freshParent) :: links) nodeB)
     = (unionFindRootOf links nodeA == unionFindRootOf links nodeB)
  rw [stringUnionFindRootOf_cons_freshAbove_forest freshChild freshParent bound links parentsBounded
        boundLeFresh hforest nodeA nodeABelow,
      stringUnionFindRootOf_cons_freshAbove_forest freshChild freshParent bound links parentsBounded
        boundLeFresh hforest nodeB nodeBBelow]

/-! ## Honesty markers -/

/-- **★ ESTABLISHED — the union-find FOREST invariant is ported and the FUEL NORMALIZATION (residual (i)) is CLOSED.**
The forest predicate `stringIsUnionFindForest` is re-stated over the bare `WireState` (the `ArcSwapRenameable` chain
re-derived over the shared `unionFindParent` / `unionFindJoin`), with the empty-list base
(`stringIsUnionFindForest_nil`), the settling lemma (`stringUnionFindRootOf_parentless_of_forest`), the JOIN
preservation (`stringUnionFindForest_unionFindJoin`), and the whole-fold chain (`stringUnionFindForest_stepCup` /
`_stepCap` / `_stepAtom` / `_processSpine`, from the fresh seed via `stringProcessSpine_isUnionFindForest_fromSeed`) —
so every reachable fold state has acyclic `links`.  The FUEL-SPLIT (`stringUnionFindRoot_fuelSplit`) + the FUEL-BUMP
on a forest (`stringUnionFindRoot_fuelBump_of_forest`) then normalize the fuel, and the COMPOSITE
`stringIsSameComponent_cons_freshAbove_forest` proves a fresh edge changes NO below-bound `isSameComponent` — the
exact fuel-normalized "a fresh cup pair changes no old `isSameComponent`" fact FC-3b's residual (i) named as needing
the forest/acyclicity invariant.  All UNCONDITIONAL (given the forest, which the fold discharges), zero-axiom.
`= true`. -/
def fxString_hasForestFuelNormalization : Bool := true

end FX1Poly.Polygraph
