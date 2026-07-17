/-! # WalkingCommutativeMonoid/CommutativeMonoidSeed — the walking commutative monoid: signature, tree-pasting relation, and the FULL single-generator decision

The presentation of the free **commutative** monoid on one generating input slot, as a signature plus a
tree-pasting convertibility: the binary multiplication `m : arity 2`, the nullary unit `e : arity 0`, and
the operad identity `id ∈ operad(1)` (an input slot), with the FOUR relations of a commutative monoid —
associativity, left unit, right unit, and **commutativity** `m(x,y) ≈ m(y,x)`.

## ★ Why this walker is FULLY DECIDED (not just seeded)

The sibling planar `WalkingOperad` (associative monoid) seeded the signature and walled the decision.  The
commutative monoid on a SINGLE generating slot is sharper: because there is exactly one generator kind
(`leaf`), the free commutative monoid it presents is `(ℕ, +, 0)` — a tree's class is determined entirely by
its **leaf count**.  So the word problem is not merely bounded by a soundness invariant; the leaf count is a
COMPLETE invariant, and `CommMonoidTreeConv a b ↔ leafCount a = leafCount b` decides convertibility by a
`Nat` equality.  This file ships:

* **soundness** — convertible trees have equal leaf count (`commMonoidTreeConv_sound`);
* **normalization** — every tree reduces to the right-comb of its leaf count (`commMonoidTreeReducesToComb`);
* **completeness** — equal leaf count ⟹ convertible (`commMonoidTreeConv_complete`);
* **the decision** — the convertibility ⟺ `Nat`-equality biconditional (`commMonoidTreeConv_iff_leafCount`).

## ★ The honest wall

The MULTI-generator (coloured) free commutative monoid is NOT ℕ — it is the free commutative monoid on the
generator set, i.e. the finite MULTISETS of generators, decided by multiset (sorted-list) equality rather
than a single `Nat`.  That decision needs a multiset/sorted-list normal form and is the successor rung; it is
NOT attempted here.  This file is the single-generator instance, complete.

Raw Lean 4 + Init; the convertibility is an inductive `Prop`; per-declaration `#assert_no_axioms` gated in the
audit twin.  Free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega` — the only
arithmetic used is `Nat.add_assoc` / `Nat.add_comm` / `Nat.add_zero` (all propext-clean). -/

namespace FX1Poly.Polygraph

/-! ## The commutative-monoid tree carrier -/

/-- ★ The **tree carrier** of the walking commutative monoid: an un-indexed planar tree over the two monoid
generators.  `leaf` is an arity-1 input slot (the operad identity); `unitOp` is the nullary generator `e`;
`mulOp` grafts two subtrees under the binary generator `m`.  A closed `CommMonoidTree`'s number of `leaf`s is
its total arity — and, for the single-generator commutative monoid, its complete convertibility invariant. -/
inductive CommMonoidTree where
  /-- An arity-1 input slot — the operad identity `id ∈ operad(1)`. -/
  | leaf
  /-- The nullary generator `e : arity 0` (the monoid unit). -/
  | unitOp
  /-- The binary generator `m : arity 2` grafting the left and right subtrees (`m(left, right)`). -/
  | mulOp : CommMonoidTree → CommMonoidTree → CommMonoidTree

/-! ## The soundness invariant: leaf count -/

/-- The **leaf count** of a tree — the total number of arity-1 input slots.  `leaf ↦ 1`, `unitOp ↦ 0`,
`mulOp l r ↦ leafCount l + leafCount r`.  A full-enumeration structural fold (no wildcard), propext-clean.
For the single-generator commutative monoid this is the COMPLETE convertibility invariant (the value of the
tree in the free commutative monoid `ℕ`). -/
def leafCount : CommMonoidTree → Nat
  | .leaf => 1
  | .unitOp => 0
  | .mulOp left right => leafCount left + leafCount right

/-- Smoke: a single input slot has leaf count 1. -/
theorem leafCount_leaf : leafCount CommMonoidTree.leaf = 1 := rfl

/-- Smoke: the unit has leaf count 0. -/
theorem leafCount_unit : leafCount CommMonoidTree.unitOp = 0 := rfl

/-- Smoke: `m(m(leaf, leaf), leaf)` has leaf count 3. -/
theorem leafCount_threeSlot :
    leafCount (CommMonoidTree.mulOp (CommMonoidTree.mulOp CommMonoidTree.leaf CommMonoidTree.leaf)
      CommMonoidTree.leaf) = 3 := rfl

/-! ## The commutative-monoid tree-pasting convertibility -/

/-- ★ The **tree-pasting convertibility** of the walking commutative monoid — the free-operad convertibility
of the `{m, e}` signature closed under the four commutative-monoid laws (associativity, left unit, right
unit, and **commutativity**), the full tree-congruence `mulCongr`, and `refl` / `symm` / `trans`.  Two trees
denote the same element of the free commutative monoid exactly when they are `CommMonoidTreeConv`-related. -/
inductive CommMonoidTreeConv : CommMonoidTree → CommMonoidTree → Prop where
  /-- **Associativity** `m(m(left, middle), right) ≈ m(left, m(middle, right))`. -/
  | assoc (left middle right : CommMonoidTree) :
      CommMonoidTreeConv
        (CommMonoidTree.mulOp (CommMonoidTree.mulOp left middle) right)
        (CommMonoidTree.mulOp left (CommMonoidTree.mulOp middle right))
  /-- **Left unit** `m(unitOp, subtree) ≈ subtree`. -/
  | unitLeft (subtree : CommMonoidTree) :
      CommMonoidTreeConv (CommMonoidTree.mulOp CommMonoidTree.unitOp subtree) subtree
  /-- **Right unit** `m(subtree, unitOp) ≈ subtree`. -/
  | unitRight (subtree : CommMonoidTree) :
      CommMonoidTreeConv (CommMonoidTree.mulOp subtree CommMonoidTree.unitOp) subtree
  /-- **Commutativity** `m(left, right) ≈ m(right, left)` — the relation the planar monoid operad lacks. -/
  | commSwap (left right : CommMonoidTree) :
      CommMonoidTreeConv (CommMonoidTree.mulOp left right) (CommMonoidTree.mulOp right left)
  /-- **Congruence under a grafting node** — into BOTH children. -/
  | mulCongr {leftOld leftNew rightOld rightNew : CommMonoidTree} :
      CommMonoidTreeConv leftOld leftNew → CommMonoidTreeConv rightOld rightNew →
      CommMonoidTreeConv (CommMonoidTree.mulOp leftOld rightOld) (CommMonoidTree.mulOp leftNew rightNew)
  /-- Reflexivity. -/
  | refl (tree : CommMonoidTree) : CommMonoidTreeConv tree tree
  /-- Symmetry. -/
  | symm {tree1 tree2 : CommMonoidTree} : CommMonoidTreeConv tree1 tree2 → CommMonoidTreeConv tree2 tree1
  /-- Transitivity. -/
  | trans {tree1 tree2 tree3 : CommMonoidTree} :
      CommMonoidTreeConv tree1 tree2 → CommMonoidTreeConv tree2 tree3 → CommMonoidTreeConv tree1 tree3

/-! ## Soundness: convertible ⟹ equal leaf count -/

/-- `0 + n = n`, propext-clean (via `add_comm` + the definitional `add_zero`, avoiding any leaky lemma). -/
theorem commMonoidNatZeroAdd (value : Nat) : 0 + value = value :=
  (Nat.add_comm 0 value).trans (Nat.add_zero value)

/-- ★ **Soundness** — convertible trees have equal leaf count.  Each law preserves the count: associativity by
`Nat.add_assoc`, left unit by `0 + n = n`, right unit by the definitional `n + 0 = n`, commutativity by
`Nat.add_comm`, and the congruence by the inductive hypotheses.  All arithmetic is propext-clean. -/
theorem commMonoidTreeConv_sound {source target : CommMonoidTree}
    (conv : CommMonoidTreeConv source target) : leafCount source = leafCount target := by
  induction conv with
  | assoc left middle right => exact Nat.add_assoc (leafCount left) (leafCount middle) (leafCount right)
  | unitLeft subtree => exact commMonoidNatZeroAdd (leafCount subtree)
  | unitRight subtree => exact rfl
  | commSwap left right => exact Nat.add_comm (leafCount left) (leafCount right)
  | mulCongr _ _ ihLeft ihRight =>
      exact (congrArg (fun leftCount => leftCount + _) ihLeft).trans
        (congrArg (fun rightCount => _ + rightCount) ihRight)
  | refl tree => exact rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ## Normalization: every tree reduces to the right-comb of its leaf count -/

/-- The **right-comb** of a given leaf count: `combOf 0 = unitOp` and `combOf (n+1) = m(leaf, combOf n)`, the
canonical `n`-slot tree.  The normal form of the single-generator commutative monoid. -/
def combOf : Nat → CommMonoidTree
  | 0 => CommMonoidTree.unitOp
  | Nat.succ predecessor => CommMonoidTree.mulOp CommMonoidTree.leaf (combOf predecessor)

/-- Grafting two right-combs is convertible to the right-comb of their summed length: `m(combOf a, combOf b)
≈ combOf (b + a)`.  Induction on `a`; the base uses left unit, the step uses associativity + the inductive
hypothesis, and the index arithmetic `b + (a+1) = (b + a) + 1` is definitional (right-recursive `Nat.add`). -/
theorem combAppend (leftLength rightLength : Nat) :
    CommMonoidTreeConv
      (CommMonoidTree.mulOp (combOf leftLength) (combOf rightLength))
      (combOf (rightLength + leftLength)) := by
  induction leftLength with
  | zero => exact CommMonoidTreeConv.unitLeft (combOf rightLength)
  | succ predecessor ih =>
      exact CommMonoidTreeConv.trans
        (CommMonoidTreeConv.assoc CommMonoidTree.leaf (combOf predecessor) (combOf rightLength))
        (CommMonoidTreeConv.mulCongr (CommMonoidTreeConv.refl CommMonoidTree.leaf) ih)

/-- ★ **Normalization** — every tree is convertible to the right-comb of its own leaf count.  Induction on the
tree: `leaf` reduces via right unit, `unitOp` is already `combOf 0`, and `mulOp` grafts the two normalized
children and re-associates (via `combAppend`), transporting the summed index by `Nat.add_comm`. -/
theorem commMonoidTreeReducesToComb (tree : CommMonoidTree) :
    CommMonoidTreeConv tree (combOf (leafCount tree)) := by
  induction tree with
  | leaf => exact CommMonoidTreeConv.symm (CommMonoidTreeConv.unitRight CommMonoidTree.leaf)
  | unitOp => exact CommMonoidTreeConv.refl CommMonoidTree.unitOp
  | mulOp left right ihLeft ihRight =>
      have combined : CommMonoidTreeConv (CommMonoidTree.mulOp left right)
          (combOf (leafCount right + leafCount left)) :=
        CommMonoidTreeConv.trans
          (CommMonoidTreeConv.mulCongr ihLeft ihRight)
          (combAppend (leafCount left) (leafCount right))
      have indexEq : leafCount right + leafCount left = leafCount (CommMonoidTree.mulOp left right) :=
        Nat.add_comm (leafCount right) (leafCount left)
      exact indexEq ▸ combined

/-! ## Completeness and the decision -/

/-- ★ **Completeness** — equal leaf count implies convertibility.  Both trees normalize to the right-comb of
their (equal) leaf count, so they are convertible through that common normal form. -/
theorem commMonoidTreeConv_complete {source target : CommMonoidTree}
    (countEq : leafCount source = leafCount target) : CommMonoidTreeConv source target := by
  have sourceReduces : CommMonoidTreeConv source (combOf (leafCount source)) :=
    commMonoidTreeReducesToComb source
  have targetReduces : CommMonoidTreeConv target (combOf (leafCount target)) :=
    commMonoidTreeReducesToComb target
  have combEq : combOf (leafCount source) = combOf (leafCount target) := congrArg combOf countEq
  exact CommMonoidTreeConv.trans sourceReduces (combEq.symm ▸ CommMonoidTreeConv.symm targetReduces)

/-- ★ **The decision** — convertibility in the walking commutative monoid (single generator) is exactly `Nat`
equality of leaf counts.  Since `leafCount source = leafCount target` is decidable (`Nat.decEq`), this
biconditional decides the word problem. -/
theorem commMonoidTreeConv_iff_leafCount (source target : CommMonoidTree) :
    CommMonoidTreeConv source target ↔ leafCount source = leafCount target :=
  ⟨commMonoidTreeConv_sound, commMonoidTreeConv_complete⟩

/-- ★ **The decider** — a shipped `Decidable` for the walking commutative monoid's convertibility, built
from the leaf-count decision: match on `Nat.decEq` of the leaf counts, discharging `isTrue` by completeness
and `isFalse` by soundness.  A genuine decider (not `decidable_of_iff`), propext-free. -/
def decideCommMonoidTreeConv (source target : CommMonoidTree) :
    Decidable (CommMonoidTreeConv source target) :=
  match Nat.decEq (leafCount source) (leafCount target) with
  | isTrue countEq => isTrue (commMonoidTreeConv_complete countEq)
  | isFalse countNe => isFalse (fun conv => countNe (commMonoidTreeConv_sound conv))

/-! ## Groundings -/

/-- ★ **Associativity holds** at the three input slots. -/
theorem commMonoidAssocHolds :
    CommMonoidTreeConv
      (CommMonoidTree.mulOp (CommMonoidTree.mulOp CommMonoidTree.leaf CommMonoidTree.leaf) CommMonoidTree.leaf)
      (CommMonoidTree.mulOp CommMonoidTree.leaf (CommMonoidTree.mulOp CommMonoidTree.leaf CommMonoidTree.leaf)) :=
  CommMonoidTreeConv.assoc CommMonoidTree.leaf CommMonoidTree.leaf CommMonoidTree.leaf

/-- ★ **Commutativity does real work** — `m(leaf, m(leaf, leaf)) ≈ m(m(leaf, leaf), leaf)`: swapping a slot
past a two-slot subtree, a move UNAVAILABLE in the planar `WalkingOperad`. -/
theorem commMonoidCommHolds :
    CommMonoidTreeConv
      (CommMonoidTree.mulOp CommMonoidTree.leaf (CommMonoidTree.mulOp CommMonoidTree.leaf CommMonoidTree.leaf))
      (CommMonoidTree.mulOp (CommMonoidTree.mulOp CommMonoidTree.leaf CommMonoidTree.leaf) CommMonoidTree.leaf) :=
  CommMonoidTreeConv.commSwap CommMonoidTree.leaf (CommMonoidTree.mulOp CommMonoidTree.leaf CommMonoidTree.leaf)

/-- ★ **The decision in action (positive)** — two DIFFERENTLY-shaped three-slot trees are convertible,
decided purely by their equal leaf count (`3 = 3`) through the completeness leg — no explicit rewrite path
supplied. -/
theorem commMonoidDecidesEqualCount :
    CommMonoidTreeConv
      (CommMonoidTree.mulOp (CommMonoidTree.mulOp CommMonoidTree.leaf CommMonoidTree.leaf) CommMonoidTree.leaf)
      (CommMonoidTree.mulOp CommMonoidTree.leaf (CommMonoidTree.mulOp CommMonoidTree.leaf CommMonoidTree.leaf)) :=
  commMonoidTreeConv_complete rfl

/-- ★ **The decision in action (negative)** — `m(leaf, leaf)` (2 slots) is NOT convertible to `leaf` (1 slot):
the leaf counts differ, so by soundness no convertibility can exist.  `2 ≠ 1` by `Nat.noConfusion`. -/
theorem commMonoidRejectsUnequalCount :
    ¬ CommMonoidTreeConv (CommMonoidTree.mulOp CommMonoidTree.leaf CommMonoidTree.leaf) CommMonoidTree.leaf :=
  fun conv => Nat.noConfusion (commMonoidTreeConv_sound conv)
    (fun oneEqZero => Nat.noConfusion oneEqZero)

/-! ## The marker -/

/-- ★ **The walking commutative monoid is DECIDED (single generator).**  `= true` records that
`commMonoidTreeConv_iff_leafCount` reduces the word problem to `Nat` equality of leaf counts — soundness,
normalization to the right-comb, and completeness all shipped.  The COLOURED (multi-generator) commutative
monoid, decided by multiset equality, is the honest successor wall. -/
def fxWalkingCommMonoid_hasSingleGeneratorDecision : Bool := true

end FX1Poly.Polygraph
