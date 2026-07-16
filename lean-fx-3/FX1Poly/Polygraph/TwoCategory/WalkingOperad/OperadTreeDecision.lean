import FX1Poly.Polygraph.TwoCategory.WalkingOperad.OperadTreeArity

/-! # WalkingOperad/OperadTreeDecision — the arity-generic RIGHT-COMB normal form: the walking monoid operad word problem, DECIDED

Brick 2 of WP-OPERAD.  Brick 1 (`OperadTreeSeed` / `OperadTreeArity`) ships the SIGNATURE, the total-arity map
`arityOf : OperadTree → Nat`, and SOUNDNESS (`arityOf_congr_of_conv`: tree-pasting-convertible trees have equal
total arity — the NO-direction).  Here the missing COMPLETENESS and hence the TOTAL word-problem DECISION land.

For THIS operad — the unital-associative operad `Ass_unital`, where `operad(n)` is a single point for every
`n ≥ 0` — total arity is in fact a COMPLETE invariant: every equal-arity pair IS convertible, via a canonical
RIGHT-COMB normal form.  So this file closes the completeness half the brick-1 marker deferred, mirroring the
walking cyclic-3 decider exactly, with `arityOf : OperadTree → Nat` playing the role of `cyclicThreeResidueOf`,
`Nat` (+ `Nat.decEq`) the role of the `Z/3` residue type, and the right-comb builder `reify : Nat → OperadTree`
the role of `residueNF`.

## The right-comb normal form

`reify n` is the canonical arity-`n` operation: a right-nested product of `n` input slots capped by the unit —
`reify 0 = unitOp`, `reify (n+1) = m(leaf, reify n)`.  So `reify 1 = m(leaf, unitOp)`, `reify 2 =
m(leaf, m(leaf, unitOp))`, and `arityOf (reify n) = n` (`arityOf_reify`), i.e. `reify` is a section of `arityOf`.
The normalizer is `operadNF tree := reify (arityOf tree)` — a composition of two structural folds (`arityOf`
shipped, `reify` new), NO `WellFounded.fix`.  Two trees share a normal form exactly when they share an arity,
because `reify` is injective (invert via `arityOf_reify`).

## The two directions

  * **SOUNDNESS (NO-direction)** is FREE: `operadNF_congr_of_conv` is `congrArg reify` applied to the shipped
    `arityOf_congr_of_conv`.  Nothing to re-derive.
  * **COMPLETENESS (YES-direction)** is the reconstruction `conv_toReify : tree ≈ reify (arityOf tree)`, built
    move-by-move from the monoid-law conv generators.  The crux is `reify_mulOp_append`: grafting two right-combs
    concatenates them (`m(reify a, reify b) ≈ reify (a + b)`), proved by induction on `a` using exactly the
    normalizer's moves — associativity pushes each head leaf out, the unit absorbs at the base.  Then
    `conv_toReify` is a direct STRUCTURAL induction on the (un-indexed) tree: `leaf ≈ m(leaf, unitOp)` by
    right-unit, `unitOp ≈ unitOp` by refl, and `m(l, r)` rewrites both children by their IHs then concatenates
    via `reify_mulOp_append`.

## Why the un-indexed carrier makes this clean

Because `OperadTree` is UN-INDEXED (see `OperadTreeSeed`), `induction tree` and the folds `reify` / `conv_toReify`
never refine an inductive index — so there is no length-generalization and none of the index-refining `propext`
leak the `ModalityPath`-based walkers must dodge.  `reify` is structural `Nat` recursion (no `WellFounded.fix`);
`operadNF` is fold∘fold.  The only arithmetic is `Nat.zero_add` / `Nat.add_assoc` (already used-and-audited in
the arity file), plus `Nat.succ_add` (in `reify_mulOp_append`) and `Nat.add_comm` (in `arityOf_reify`), all
propext-clean.  The decider compares arities in `Nat` via `Nat.decEq`, so the whole NO-branch reuses the shipped,
already-audited `arityOf_congr_of_conv`.

## Road not taken

A pure-tree normal form via a `spineOnto`-style fold (no `Nat` arithmetic) is possible but was rejected: it
forces a fresh `operadNF_congr_of_conv` soundness proof (needs fold-fusion + first-argument congruence) plus a
recursive manual `DecidableEq OperadTree`, and discards the shipped arity soundness.  The arity route is strictly
less new code with maximal reuse.

## Scope honesty

For this `Ass_unital` operad arity is a COMPLETE invariant (right-comb NF), so this is a genuine FULL decision.
For the arity-GENERIC free operad on an arbitrary signature (many arity-2 generators) leaf-count is INCOMPLETE;
brick 2 decides the fixed `{m, e}` presentation, and the arity-generic seed's decision is a later rung.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin, with an independent `#print
axioms` cross-check on the completeness theorem and the decider.  Free of `propext`, `Quot.sound`, `Classical`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1Poly.Polygraph

/-! ## The right-comb builder: the canonical arity-`n` operation -/

/-- ★ The **right-comb builder** `reify n` — the canonical arity-`n` operation of the walking monoid operad: a
right-nested product of `n` input slots capped by the nullary unit.  `reify 0 = unitOp`, and each successor
grafts one more `leaf` on the left: `reify (n+1) = m(leaf, reify n)`.  A structural `Nat` fold whose defining
equations reduce DEFINITIONALLY (no `WellFounded.fix`), and a section of `arityOf` (`arityOf_reify`).  The
operad analog of the cyclic-3 `residueNF`. -/
def reify : Nat → OperadTree
  | 0 => OperadTree.unitOp
  | count + 1 => OperadTree.mulOp OperadTree.leaf (reify count)

/-- The defining equation on `0` — the arity-0 canonical operation is the nullary unit. -/
theorem reify_zero : reify 0 = OperadTree.unitOp := rfl

/-- The defining equation on a successor — grafting one more input slot on the left. -/
theorem reify_succ (count : Nat) :
    reify (count + 1) = OperadTree.mulOp OperadTree.leaf (reify count) := rfl

/-- Smoke: the canonical arity-1 operation is `m(leaf, unitOp)` — the right-unit law's tree. -/
theorem reify_one : reify 1 = OperadTree.mulOp OperadTree.leaf OperadTree.unitOp := rfl

/-- Smoke: the canonical arity-2 operation is the right-comb `m(leaf, m(leaf, unitOp))`. -/
theorem reify_two :
    reify 2 = OperadTree.mulOp OperadTree.leaf (OperadTree.mulOp OperadTree.leaf OperadTree.unitOp) := rfl

/-- ★ **`reify` is a section of `arityOf`**: the canonical arity-`n` operation has total arity `n`.  By
induction on `n`: the successor step is `arityOf (m(leaf, reify n)) = 1 + arityOf (reify n) = 1 + n = n + 1`
(`arityOf_mulOp` / `arityOf_leaf` / IH / `Nat.add_comm`).  This inverts `reify`, so `reify` is injective and
`operadNF` classifies exactly the arity. -/
theorem arityOf_reify (count : Nat) : arityOf (reify count) = count := by
  induction count with
  | zero => rfl
  | succ predecessor inductiveHypothesis =>
      rw [reify_succ, arityOf_mulOp, arityOf_leaf, inductiveHypothesis, Nat.add_comm predecessor 1]

/-! ## The normalizer: fold ∘ fold -/

/-- ★ The **operad normalizer**: send a tree to the canonical right-comb of its total arity —
`operadNF tree := reify (arityOf tree)`.  A composition of two structural folds (`arityOf` from brick 1, `reify`
new), so NO `WellFounded.fix`.  Two trees share a normal form exactly when they share an arity (`reify`
injective), and every tree is convertible to its normal form (`conv_toReify`), so `operadNF` decides the word
problem. -/
def operadNF (tree : OperadTree) : OperadTree := reify (arityOf tree)

/-- The defining equation of the normalizer. -/
theorem operadNF_eq (tree : OperadTree) : operadNF tree = reify (arityOf tree) := rfl

/-- Smoke: an input slot normalizes to the canonical arity-1 operation `m(leaf, unitOp)`. -/
theorem operadNF_leaf : operadNF OperadTree.leaf = OperadTree.mulOp OperadTree.leaf OperadTree.unitOp := rfl

/-- Smoke: the nullary unit normalizes to itself (the canonical arity-0 operation). -/
theorem operadNF_unitOp : operadNF OperadTree.unitOp = OperadTree.unitOp := rfl

/-! ## SOUNDNESS (NO-direction) — free reuse of brick 1 -/

/-- ★ **Soundness in normal-form shape**: convertible trees have EQUAL normal form.  A one-liner reuse of the
shipped `arityOf_congr_of_conv` (convertible ⟹ equal arity) under `congrArg reify`.  This is the NO-direction —
distinct normal form ⟹ not convertible. -/
theorem operadNF_congr_of_conv
    {tree1 tree2 : OperadTree} (conv : OperadTreeConv tree1 tree2) :
    operadNF tree1 = operadNF tree2 :=
  congrArg reify (arityOf_congr_of_conv conv)

/-! ## COMPLETENESS (YES-direction) — the right-comb reconstruction -/

/-- ★ **Grafting two right-combs concatenates them**: `m(reify a, reify b) ≈ reify (a + b)`.  The crux of
completeness, by induction on `a` using EXACTLY the normalizer's moves.  `a = 0`: `reify 0 = unitOp`, so the
left-unit law fires (`m(unitOp, reify b) ≈ reify b`, and `0 + b = b`).  `a = k+1`: `reify (k+1) = m(leaf,
reify k)`, so associativity pushes the head `leaf` out (`m(m(leaf, reify k), reify b) ≈ m(leaf, m(reify k,
reify b))`), then `mulCongr (refl leaf) (ih b)` recurses on the tail (`m(reify k, reify b) ≈ reify (k + b)`), and
`(k+1) + b = (k + b) + 1` (`Nat.succ_add`) exposes the target right-comb `m(leaf, reify (k + b))`. -/
theorem reify_mulOp_append (leftArity rightArity : Nat) :
    OperadTreeConv (OperadTree.mulOp (reify leftArity) (reify rightArity)) (reify (leftArity + rightArity)) := by
  induction leftArity with
  | zero =>
      rw [Nat.zero_add]
      exact OperadTreeConv.unitLeft (reify rightArity)
  | succ predecessor inductiveHypothesis =>
      rw [Nat.succ_add]
      exact OperadTreeConv.trans
        (OperadTreeConv.assoc OperadTree.leaf (reify predecessor) (reify rightArity))
        (OperadTreeConv.mulCongr (OperadTreeConv.refl OperadTree.leaf) inductiveHypothesis)

/-- ★ **The reconstruction**: every tree is convertible to the right-comb normal form of its arity —
`tree ≈ reify (arityOf tree)`.  A direct STRUCTURAL induction on the un-indexed `OperadTree` (no
length-generalization, no index refinement).  `leaf ≈ m(leaf, unitOp)` by right-unit (`reify 1 = m(leaf, unitOp)`
definitionally); `unitOp ≈ unitOp` by refl; and `m(left, right)` rewrites both children by their IHs
(`mulCongr`) then concatenates the two right-combs via `reify_mulOp_append`. -/
theorem conv_toReify (tree : OperadTree) :
    OperadTreeConv tree (reify (arityOf tree)) := by
  induction tree with
  | leaf => exact OperadTreeConv.symm (OperadTreeConv.unitRight OperadTree.leaf)
  | unitOp => exact OperadTreeConv.refl OperadTree.unitOp
  | mulOp left right inductiveHypothesisLeft inductiveHypothesisRight =>
      exact OperadTreeConv.trans
        (OperadTreeConv.mulCongr inductiveHypothesisLeft inductiveHypothesisRight)
        (reify_mulOp_append (arityOf left) (arityOf right))

/-- ★ **Completeness via the common normal form**: trees with EQUAL total arity are convertible.  Route both
through their shared right-comb: `w1 ≈ reify (arityOf w1) = reify (arityOf w2) ≈ w2` (the `=` is the hypothesis
under `congrArg reify`).  The YES-direction of the decision (the reconstruction). -/
theorem operadTreeConv_of_arity_eq
    {tree1 tree2 : OperadTree} (aritiesEqual : arityOf tree1 = arityOf tree2) :
    OperadTreeConv tree1 tree2 := by
  have reductionOne : OperadTreeConv tree1 (reify (arityOf tree2)) := by
    rw [← aritiesEqual]; exact conv_toReify tree1
  exact OperadTreeConv.trans reductionOne (OperadTreeConv.symm (conv_toReify tree2))

/-- ★ **Completeness in normal-form shape**: trees with EQUAL normal form are convertible.  Invert `reify`
(apply `arityOf` to both sides and rewrite by `arityOf_reify`) to recover equal arity, then reconstruct via
`operadTreeConv_of_arity_eq`. -/
theorem conv_of_operadNF_eq
    {tree1 tree2 : OperadTree} (normalFormsEqual : operadNF tree1 = operadNF tree2) :
    OperadTreeConv tree1 tree2 := by
  have aritiesEqual : arityOf tree1 = arityOf tree2 := by
    have congruence : arityOf (reify (arityOf tree1)) = arityOf (reify (arityOf tree2)) :=
      congrArg arityOf normalFormsEqual
    rw [arityOf_reify, arityOf_reify] at congruence
    exact congruence
  exact operadTreeConv_of_arity_eq aritiesEqual

/-- ★ **The word problem as a normal-form equality**: two trees are convertible iff they share a normal form —
`operadNF_congr_of_conv` (⟹) paired with `conv_of_operadNF_eq` (⟸).  The complete characterization of the
walking monoid operad word problem. -/
theorem operadConv_iff_nf_eq (tree1 tree2 : OperadTree) :
    OperadTreeConv tree1 tree2 ↔ operadNF tree1 = operadNF tree2 :=
  ⟨operadNF_congr_of_conv, conv_of_operadNF_eq⟩

/-! ## The TOTAL decision -/

/-- ★ **Decide walking monoid operad tree-pasting convertibility** — TOTAL.  Compare the two trees' total
arities in `Nat`: equal arity ⟹ `isTrue` (completeness `operadTreeConv_of_arity_eq`); distinct arity ⟹ `isFalse`
(soundness `arityOf_congr_of_conv` would force them equal).  The whole NO-branch reuses the shipped, audited
arity soundness; both branches discharged — the operad word problem is genuinely decided. -/
def decideOperadTreeConv (tree1 tree2 : OperadTree) : Decidable (OperadTreeConv tree1 tree2) :=
  match (inferInstance : Decidable (arityOf tree1 = arityOf tree2)) with
  | isTrue aritiesEqual => isTrue (operadTreeConv_of_arity_eq aritiesEqual)
  | isFalse aritiesDiffer =>
      isFalse (fun conv => aritiesDiffer (arityOf_congr_of_conv conv))

/-- The walking monoid operad's tree-pasting convertibility as a `Decidable` instance (so `decide` fires on
it). -/
instance instDecidableOperadTreeConv (tree1 tree2 : OperadTree) :
    Decidable (OperadTreeConv tree1 tree2) :=
  decideOperadTreeConv tree1 tree2

/-! ## Concrete non-canonical sample trees -/

/-- A mixed-unit arity-2 tree `m(leaf, m(unitOp, leaf))` — total arity `1 + (0 + 1) = 2`, convertible to
`m(leaf, leaf)` (arity 2) ONLY through completeness (the inner left-unit is not a `rfl`, it must fire the
law). -/
def operadMixedUnitTree : OperadTree :=
  OperadTree.mulOp OperadTree.leaf (OperadTree.mulOp OperadTree.unitOp OperadTree.leaf)

/-- The arity-2 right-nested pure-leaf product `m(leaf, leaf)` — the completeness target of
`operadMixedUnitTree`. -/
def operadTwoLeaves : OperadTree :=
  OperadTree.mulOp OperadTree.leaf OperadTree.leaf

/-! ## Non-vacuity smokes — the decider genuinely discriminates -/

/-- Positive witness (completeness): `m(leaf, m(unitOp, leaf)) ≈ m(leaf, leaf)` — same arity (2), convertible
ONLY via the reconstruction (an inner unit must be absorbed by the law). -/
theorem operadConv_mixedUnit_twoLeaves :
    OperadTreeConv operadMixedUnitTree operadTwoLeaves :=
  operadTreeConv_of_arity_eq rfl

/-- ★ Non-vacuity by the DECIDER (positive, associativity): `decide` on the convertible associativity pair
`m(m(leaf, leaf), leaf) ≈ m(leaf, m(leaf, leaf))` (arity 3 both) returns `true`. -/
theorem operadDecide_true_on_assoc :
    decide (OperadTreeConv operadAssocLeftTree operadAssocRightTree) = true := rfl

/-- ★ Non-vacuity by the DECIDER (positive, left unit): `decide` on `m(unitOp, leaf) ≈ leaf` (arity 1 both)
returns `true`. -/
theorem operadDecide_true_on_unitLeft :
    decide (OperadTreeConv operadUnitLeftTree OperadTree.leaf) = true := rfl

/-- ★ Non-vacuity by the DECIDER (positive, right unit): `decide` on `m(leaf, unitOp) ≈ leaf` (arity 1 both)
returns `true`. -/
theorem operadDecide_true_on_unitRight :
    decide (OperadTreeConv operadUnitRightTree OperadTree.leaf) = true := rfl

/-- ★ Non-vacuity by the DECIDER (positive, mixed unit): `decide` on `m(leaf, m(unitOp, leaf)) ≈ m(leaf, leaf)`
returns `true` — a pair convertible ONLY through completeness (the inner unit fires the law), so this witnesses
the reconstruction genuinely, not a `rfl` coincidence. -/
theorem operadDecide_true_on_mixedUnit :
    decide (OperadTreeConv operadMixedUnitTree operadTwoLeaves) = true := rfl

/-- ★ Non-vacuity by the DECIDER (negative, grafting vs slot): `decide` on `m(leaf, leaf) ≟ leaf` (arity 2 vs 1)
returns `false`. -/
theorem operadDecide_false_on_twoLeaves_leaf :
    decide (OperadTreeConv operadTwoLeaves OperadTree.leaf) = false := rfl

/-- ★ Non-vacuity by the DECIDER (negative, unit vs slot): `decide` on `unitOp ≟ leaf` (arity 0 vs 1) returns
`false`. -/
theorem operadDecide_false_on_unitOp_leaf :
    decide (OperadTreeConv OperadTree.unitOp OperadTree.leaf) = false := rfl

/-! ## Honesty marker -/

/-- **ESTABLISHED.**  The walking monoid operad tree-pasting word problem (`Ass_unital`, the free planar
`{m : arity 2, e : arity 0}` operad modulo associativity + left/right unit) is DECIDED via the RIGHT-COMB normal
form, zero-axiom and non-vacuously.  The normalizer `operadNF = reify ∘ arityOf` is SOUND
(`operadNF_congr_of_conv`, a free reuse of brick 1's `arityOf_congr_of_conv`) and COMPLETE
(`operadTreeConv_of_arity_eq` / `conv_of_operadNF_eq`, via the reconstruction `conv_toReify` whose crux
`reify_mulOp_append` grafts two right-combs by the associativity + unit moves), giving the characterization
`operadConv_iff_nf_eq`.  The total decider `decideOperadTreeConv` accepts the convertible pairs
`m(m(leaf,leaf),leaf) ≈ m(leaf,m(leaf,leaf))` (`operadDecide_true_on_assoc`), `m(unitOp,leaf) ≈ leaf`
(`operadDecide_true_on_unitLeft`), `m(leaf,unitOp) ≈ leaf` (`operadDecide_true_on_unitRight`), and the
completeness-only pair `m(leaf,m(unitOp,leaf)) ≈ m(leaf,leaf)` (`operadDecide_true_on_mixedUnit`), and rejects the
separated pairs `m(leaf,leaf) ≟ leaf` (`operadDecide_false_on_twoLeaves_leaf`) and `unitOp ≟ leaf`
(`operadDecide_false_on_unitOp_leaf`).  This is WP-OPERAD BRICK 2 — the completeness half brick 1's
`fxOperad_hasWordProblemDecided` marker deferred; for the arity-generic free operad (arbitrary signature)
leaf-count is incomplete and its decision is a later rung.  `= true`. -/
def fxOperad_hasRightCombDecision : Bool := true

end FX1Poly.Polygraph
