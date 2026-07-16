import FX1Poly.Polygraph.TwoCategory.WalkingOperad.OperadTreeSeed

/-! # WalkingOperad/OperadTreeArity — the total-arity (leaf-count) invariant + SOUNDNESS

The soundness half of the walking monoid operad: the total-arity map `arityOf : OperadTree → Nat` counting the
input slots (`leaf ↦ 1`, `unitOp ↦ 0`, `mulOp t₁ t₂ ↦ arityOf t₁ + arityOf t₂`), and the SOUNDNESS theorem
`arityOf_congr_of_conv` — tree-pasting-convertible trees have EQUAL total arity.  This is the tree-pasting
soundness invariant: distinct arity ⟹ not convertible.

## The invariant — a genuine `Nat` structural fold

Because the carrier `OperadTree` is UN-INDEXED (see `OperadTreeSeed`), `arityOf` is an honest structural
recursion whose defining equations reduce by `rfl`, and its preservation under the three monoid laws is pure
`Nat` arithmetic: associativity ↦ `Nat.add_assoc`, left unit ↦ `Nat.zero_add`, right unit ↦ `rfl`
(`n + 0 = n` definitionally).  Exactly the braid-permutation / cyclic-residue analogy.

## ★ Honesty boundary — SOUNDNESS ONLY, and a nuance on completeness (see the markers)

Brick 1 ships the SOUNDNESS direction (`arityOf_congr_of_conv`) plus non-vacuity (a law fires; a non-convertible
pair separates by arity).  The full DECISION (completeness / a word-problem decider) is deferred to BRICK 2
(right-comb normal form).

The honesty nuance: for THIS particular tiny operad — the unital-associative operad `Ass_unital`, where
`operad(n)` is a single point for every `n ≥ 0` — total arity is actually a COMPLETE invariant (every equal-arity
pair IS convertible, via the right-comb normal form).  So, unlike the braid's `S_3` map, a NON-injectivity
honesty witness does NOT exist here (claiming one would be false).  This rung resembles cyclic-3 (invariant
secretly complete, completeness merely not yet BUILT) rather than the braid (invariant genuinely incomplete).
The "arity is an invariant, not a decision" framing is honest specifically for the arity-GENERIC free operad
(arbitrary signature, many arity-2 generators) that later bricks target — there leaf-count is obviously
incomplete.

## Propext-cleanliness

`arityOf` is DATA-valued (`Nat`) and folds by `casesOn` on the tree constructor (no index refinement) — clean.
All matches are full-enumeration; the soundness induction uses only `Nat.add_assoc` / `Nat.zero_add` / `rfl` /
`rw` (all propext-clean and audited elsewhere in this repo); the negatives route through soundness +
`Nat.noConfusion`.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## The total-arity (leaf-count) invariant -/

/-- ★ The **total-arity map** of the walking monoid operad: fold a tree into its number of input slots —
`leaf ↦ 1`, `unitOp ↦ 0`, and a grafting `mulOp` sums the children's arities.  DATA-valued structural recursion
on the un-indexed `OperadTree`, so the defining equations reduce DEFINITIONALLY.  The tree-pasting soundness
invariant (the braid-permutation / cyclic-residue analog). -/
def arityOf : OperadTree → Nat
  | .leaf => 1
  | .unitOp => 0
  | .mulOp left right => arityOf left + arityOf right

/-- The defining equation on `leaf` — an input slot has arity 1. -/
theorem arityOf_leaf : arityOf OperadTree.leaf = 1 := rfl

/-- The defining equation on `unitOp` — the nullary unit has arity 0. -/
theorem arityOf_unitOp : arityOf OperadTree.unitOp = 0 := rfl

/-- The defining equation on `mulOp` — a grafting sums the children's arities.  Holds DEFINITIONALLY (the fold's
`mulOp` arm). -/
theorem arityOf_mulOp (left right : OperadTree) :
    arityOf (OperadTree.mulOp left right) = arityOf left + arityOf right := rfl

/-- Smoke: the associativity law's left tree `m(m(leaf, leaf), leaf)` has total arity 3. -/
theorem arityOf_assocLeftTree : arityOf operadAssocLeftTree = 3 := rfl

/-- Smoke: the associativity law's right tree `m(leaf, m(leaf, leaf))` has total arity 3 — the SAME as the left
tree (associativity preserves arity DEFINITIONALLY, both reduce to `1 + 1 + 1`). -/
theorem arityOf_assocRightTree : arityOf operadAssocRightTree = 3 := rfl

/-- Smoke: the left-unit law's tree `m(unitOp, leaf)` has total arity 1 — the SAME as `leaf` (the unit
contributes 0, `0 + 1 = 1`). -/
theorem arityOf_unitLeftTree : arityOf operadUnitLeftTree = 1 := rfl

/-! ## SOUNDNESS: convertible trees have equal total arity -/

/-- ★ **Soundness of the arity invariant**: tree-pasting-convertible trees have EQUAL total arity.  By induction
on the convertibility: associativity is `Nat.add_assoc`, left unit is `Nat.zero_add`, right unit is `rfl`
(`n + 0 = n`), the tree-congruence `mulCongr` rewrites both children by their IHs, and `refl` / `symm` / `trans`
are the equivalence closure.  This is the NO-direction of the (undecided-here) word problem: distinct arity ⟹ not
convertible.  Mirrors `braidThreePermutationOf_congr_of_conv`. -/
theorem arityOf_congr_of_conv
    {tree1 tree2 : OperadTree} (conv : OperadTreeConv tree1 tree2) :
    arityOf tree1 = arityOf tree2 := by
  induction conv with
  | assoc left middle right =>
      exact Nat.add_assoc (arityOf left) (arityOf middle) (arityOf right)
  | unitLeft subtree => exact Nat.zero_add (arityOf subtree)
  | unitRight subtree => rfl
  | mulCongr _ _ ihLeft ihRight =>
      rw [arityOf_mulOp, arityOf_mulOp, ihLeft, ihRight]
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ## Non-vacuity — the invariant genuinely discriminates -/

/-- Positive witness: `m(m(leaf, leaf), leaf) ≈ m(leaf, m(leaf, leaf))` (the associativity move is a convertible
pair). -/
theorem operadConv_assocLeft_assocRight :
    OperadTreeConv operadAssocLeftTree operadAssocRightTree :=
  operadAssocHolds

/-- Positive witness: soundness applied to the left-unit law — `arityOf (m(unitOp, leaf)) = arityOf leaf` — via
`arityOf_congr_of_conv operadUnitLeftHolds` (the invariant IS preserved by a genuine law firing, not merely by
`rfl`). -/
theorem arityOf_unitLeftTree_eq_leaf_via_soundness :
    arityOf operadUnitLeftTree = arityOf OperadTree.leaf :=
  arityOf_congr_of_conv operadUnitLeftHolds

/-- Negative witness: `m(leaf, leaf)` (total arity 2) is NOT convertible to `leaf` (total arity 1) — via
soundness, since `2 = 1` is impossible (`Nat.noConfusion`).  A grafting of two input slots is a genuinely
different operad operation from a single input slot. -/
theorem operadNotConv_mulLeafLeaf_leaf :
    ¬ OperadTreeConv (OperadTree.mulOp OperadTree.leaf OperadTree.leaf) OperadTree.leaf := by
  intro conv
  have aritiesEqual :
      arityOf (OperadTree.mulOp OperadTree.leaf OperadTree.leaf) = arityOf OperadTree.leaf :=
    arityOf_congr_of_conv conv
  have twoEqualsOne : (2 : Nat) = 1 := aritiesEqual
  exact Nat.noConfusion twoEqualsOne (fun oneEqualsZero => Nat.noConfusion oneEqualsZero)

/-- Negative witness: `unitOp` (total arity 0) is NOT convertible to `leaf` (total arity 1) — via soundness,
since `0 = 1` is impossible (`Nat.noConfusion`).  The nullary unit is a genuinely different operad operation
from an input slot. -/
theorem operadNotConv_unitOp_leaf :
    ¬ OperadTreeConv OperadTree.unitOp OperadTree.leaf := by
  intro conv
  have aritiesEqual : arityOf OperadTree.unitOp = arityOf OperadTree.leaf :=
    arityOf_congr_of_conv conv
  have zeroEqualsOne : (0 : Nat) = 1 := aritiesEqual
  exact Nat.noConfusion zeroEqualsOne

/-! ## Markers -/

/-- **ESTABLISHED.**  The walking monoid operad (free planar `{m : arity 2, e : arity 0}` operad, relations
associativity + left/right unit) has its SIGNATURE and a total-arity (leaf-count) invariant with SOUNDNESS
(`arityOf_congr_of_conv`: convertible trees have equal total arity), zero-axiom and non-vacuously (positive
`operadAssocHolds` / `operadUnitLeftHolds` / `operadUnitRightHolds`; negatives `operadNotConv_mulLeafLeaf_leaf`,
`operadNotConv_unitOp_leaf`).  `= true`. -/
def fxOperad_hasSignatureAndArityInvariant : Bool := true

/-- Alias of `fxOperad_hasSignatureAndArityInvariant` naming the soundness content: brick 1 ships the operad
signature (fixed `{m, e}` generators + the three monoid-law tree-pasting conv generators), the total-arity map,
and the soundness theorem.  `= true`. -/
def fxOperad_hasSignatureAndAritySoundness : Bool := true

/-- **NOT ESTABLISHED (brick boundary).**  The operad WORD PROBLEM is NOT decided here.  For this tiny
unital-associative operad total arity is in fact a COMPLETE invariant, but the DECISION (a right-comb normal
form / decider) is not BUILT — that is WP-OPERAD BRICK 2.  For the arity-GENERIC free operad (arbitrary
signature) targeted by later bricks, arity is genuinely incomplete.  Either way this rung does NOT enter the
"decided" enumeration.  `= false`. -/
def fxOperad_hasWordProblemDecided : Bool := false

end FX1Poly.Polygraph
