import FX1Poly.Polygraph.TwoCategory.WalkingCommutativeMonoid.CommutativeMonoidSeed

/-! # WalkingCommutativeMonoid/TwoColourCommutativeMonoidSeed — the walking commutative monoid on TWO generating slots: the Parikh-vector decision

The successor rung explicitly named as the honest wall in the single-generator sibling
(`CommutativeMonoidSeed`).  The free **commutative** monoid on TWO generating input slots `a`, `b` is not
`(ℕ, +, 0)` but `(ℕ², +, 0)` — a tree's class in the free commutative monoid is determined by the PAIR
(number of `a`-slots, number of `b`-slots), i.e. its **Parikh vector**.  Because that pair is a COMPLETE
invariant, the word problem is decided by a CONJUNCTION of two `Nat` equalities.

## ★ Why this walker is FULLY DECIDED (two generators)

The single-generator sibling reduced the word problem to one leaf count; here there are two generator kinds
(`leafA`, `leafB`), so the invariant is a pair of counts held as TWO separate `Nat` folds (`countAOf`,
`countBOf`) rather than a `Prod`/structure — keeping every equality a plain `Nat` equality and dodging any
`Prod`-equality `propext` leak.  This file ships:

* **soundness** — convertible trees have equal `a`-count AND equal `b`-count (`twoColourCommMonoidConv_soundA`,
  `twoColourCommMonoidConv_soundB`);
* **normalization** — every tree reduces to the canonical `a`-block-then-`b`-block right-comb of its two counts
  (`twoColourCommMonoidReducesToNormal`), grafting two normal forms via the merge lemma `combMerge`;
* **completeness** — equal `a`-count and equal `b`-count ⟹ convertible (`twoColourCommMonoidConv_complete`);
* **the decision** — the convertibility ⟺ conjunction-of-`Nat`-equalities biconditional
  (`twoColourCommMonoidConv_iff_counts`) plus a shipped `Decidable`.

## ★ The honest wall

The `n`-generator (arbitrary alphabet) free commutative monoid is the free commutative monoid on the generator
SET — the finite MULTISETS over the generators, i.e. `ℕ` indexed by the (finite) generator set, decided by
multiset (sorted-list) equality rather than a fixed tuple of `Nat`s.  Two generators is the last case whose
invariant is a fixed finite tuple of counts; the alphabet-parameterised case needs a multiset normal form and
is the successor rung — NOT attempted here.  This file is the two-generator instance, complete.

Raw Lean 4 + Init; the convertibility is an inductive `Prop`; per-declaration `#assert_no_axioms` gated in the
audit twin.  Free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega` — the only
arithmetic used is `Nat.add_assoc` / `Nat.add_comm` / `Nat.add_zero` (via `commMonoidNatZeroAdd`, reused from
the single-generator sibling), all propext-clean. -/

namespace FX1Poly.Polygraph

/-! ## The two-colour commutative-monoid tree carrier -/

/-- ★ The **tree carrier** of the walking commutative monoid on TWO generating slots: an un-indexed planar
tree over the two generators `a`, `b` plus the `{m, e}` monoid signature.  `leafA` and `leafB` are the two
arity-1 input slots; `unitOp` is the nullary generator `e`; `mulOp` grafts two subtrees under the binary
generator `m`.  A closed tree's PAIR of leaf counts (its Parikh vector) is its complete convertibility
invariant. -/
inductive TwoColourCommMonoidTree where
  /-- The first arity-1 input slot — the `a` generator. -/
  | leafA
  /-- The second arity-1 input slot — the `b` generator. -/
  | leafB
  /-- The nullary generator `e : arity 0` (the monoid unit). -/
  | unitOp
  /-- The binary generator `m : arity 2` grafting the left and right subtrees (`m(left, right)`). -/
  | mulOp : TwoColourCommMonoidTree → TwoColourCommMonoidTree → TwoColourCommMonoidTree

/-! ## The soundness invariant: two leaf counts (the Parikh vector) -/

/-- The **`a`-count** of a tree — the number of `leafA` input slots.  `leafA ↦ 1`, everything else recurses or
is `0`.  A full-enumeration structural fold (no wildcard), propext-clean.  The first component of the Parikh
vector. -/
def countAOf : TwoColourCommMonoidTree → Nat
  | .leafA => 1
  | .leafB => 0
  | .unitOp => 0
  | .mulOp left right => countAOf left + countAOf right

/-- The **`b`-count** of a tree — the number of `leafB` input slots.  `leafB ↦ 1`, everything else recurses or
is `0`.  The second component of the Parikh vector. -/
def countBOf : TwoColourCommMonoidTree → Nat
  | .leafA => 0
  | .leafB => 1
  | .unitOp => 0
  | .mulOp left right => countBOf left + countBOf right

/-- Smoke: a single `a`-slot has `a`-count 1. -/
theorem countAOf_leafA : countAOf TwoColourCommMonoidTree.leafA = 1 := rfl

/-- Smoke: a single `b`-slot has `b`-count 1. -/
theorem countBOf_leafB : countBOf TwoColourCommMonoidTree.leafB = 1 := rfl

/-- Smoke: `m(m(leafA, leafB), leafB)` has `b`-count 2. -/
theorem countBOf_twoLeafB :
    countBOf (TwoColourCommMonoidTree.mulOp
      (TwoColourCommMonoidTree.mulOp TwoColourCommMonoidTree.leafA TwoColourCommMonoidTree.leafB)
      TwoColourCommMonoidTree.leafB) = 2 := rfl

/-! ## The two-colour commutative-monoid tree-pasting convertibility -/

/-- ★ The **tree-pasting convertibility** of the walking commutative monoid on two generators — the free-operad
convertibility of the `{m, e}` signature over the two generators closed under the four commutative-monoid laws
(associativity, left unit, right unit, and **commutativity**), the full tree-congruence `mulCongr`, and
`refl` / `symm` / `trans`.  Same shapes as the single-generator sibling over the two-generator carrier (no
idempotency).  Two trees denote the same element of the free commutative monoid on `{a, b}` exactly when they
are `TwoColourCommMonoidTreeConv`-related. -/
inductive TwoColourCommMonoidTreeConv : TwoColourCommMonoidTree → TwoColourCommMonoidTree → Prop where
  /-- **Associativity** `m(m(left, middle), right) ≈ m(left, m(middle, right))`. -/
  | assoc (left middle right : TwoColourCommMonoidTree) :
      TwoColourCommMonoidTreeConv
        (TwoColourCommMonoidTree.mulOp (TwoColourCommMonoidTree.mulOp left middle) right)
        (TwoColourCommMonoidTree.mulOp left (TwoColourCommMonoidTree.mulOp middle right))
  /-- **Left unit** `m(unitOp, subtree) ≈ subtree`. -/
  | unitLeft (subtree : TwoColourCommMonoidTree) :
      TwoColourCommMonoidTreeConv (TwoColourCommMonoidTree.mulOp TwoColourCommMonoidTree.unitOp subtree) subtree
  /-- **Right unit** `m(subtree, unitOp) ≈ subtree`. -/
  | unitRight (subtree : TwoColourCommMonoidTree) :
      TwoColourCommMonoidTreeConv (TwoColourCommMonoidTree.mulOp subtree TwoColourCommMonoidTree.unitOp) subtree
  /-- **Commutativity** `m(left, right) ≈ m(right, left)` — mixing the two colours freely. -/
  | commSwap (left right : TwoColourCommMonoidTree) :
      TwoColourCommMonoidTreeConv
        (TwoColourCommMonoidTree.mulOp left right) (TwoColourCommMonoidTree.mulOp right left)
  /-- **Congruence under a grafting node** — into BOTH children. -/
  | mulCongr {leftOld leftNew rightOld rightNew : TwoColourCommMonoidTree} :
      TwoColourCommMonoidTreeConv leftOld leftNew → TwoColourCommMonoidTreeConv rightOld rightNew →
      TwoColourCommMonoidTreeConv
        (TwoColourCommMonoidTree.mulOp leftOld rightOld) (TwoColourCommMonoidTree.mulOp leftNew rightNew)
  /-- Reflexivity. -/
  | refl (tree : TwoColourCommMonoidTree) : TwoColourCommMonoidTreeConv tree tree
  /-- Symmetry. -/
  | symm {tree1 tree2 : TwoColourCommMonoidTree} :
      TwoColourCommMonoidTreeConv tree1 tree2 → TwoColourCommMonoidTreeConv tree2 tree1
  /-- Transitivity. -/
  | trans {tree1 tree2 tree3 : TwoColourCommMonoidTree} :
      TwoColourCommMonoidTreeConv tree1 tree2 → TwoColourCommMonoidTreeConv tree2 tree3 →
      TwoColourCommMonoidTreeConv tree1 tree3

/-! ## Soundness: convertible ⟹ equal Parikh vector (per colour) -/

/-- ★ **Soundness, `a`-component** — convertible trees have equal `a`-count.  Each law preserves the count:
associativity by `Nat.add_assoc`, left unit by `0 + n = n` (`commMonoidNatZeroAdd`, reused from the sibling),
right unit by the definitional `n + 0 = n`, commutativity by `Nat.add_comm`, and the congruence by the
inductive hypotheses.  All arithmetic is propext-clean. -/
theorem twoColourCommMonoidConv_soundA {source target : TwoColourCommMonoidTree}
    (conv : TwoColourCommMonoidTreeConv source target) : countAOf source = countAOf target := by
  induction conv with
  | assoc left middle right => exact Nat.add_assoc (countAOf left) (countAOf middle) (countAOf right)
  | unitLeft subtree => exact commMonoidNatZeroAdd (countAOf subtree)
  | unitRight subtree => exact rfl
  | commSwap left right => exact Nat.add_comm (countAOf left) (countAOf right)
  | mulCongr _ _ ihLeft ihRight =>
      exact (congrArg (fun leftCount => leftCount + _) ihLeft).trans
        (congrArg (fun rightCount => _ + rightCount) ihRight)
  | refl tree => exact rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- ★ **Soundness, `b`-component** — convertible trees have equal `b`-count.  Identical in shape to the
`a`-component, over `countBOf`. -/
theorem twoColourCommMonoidConv_soundB {source target : TwoColourCommMonoidTree}
    (conv : TwoColourCommMonoidTreeConv source target) : countBOf source = countBOf target := by
  induction conv with
  | assoc left middle right => exact Nat.add_assoc (countBOf left) (countBOf middle) (countBOf right)
  | unitLeft subtree => exact commMonoidNatZeroAdd (countBOf subtree)
  | unitRight subtree => exact rfl
  | commSwap left right => exact Nat.add_comm (countBOf left) (countBOf right)
  | mulCongr _ _ ihLeft ihRight =>
      exact (congrArg (fun leftCount => leftCount + _) ihLeft).trans
        (congrArg (fun rightCount => _ + rightCount) ihRight)
  | refl tree => exact rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ## The canonical normal form: an `a`-block then a `b`-block -/

/-- The **`b`-block** of a given `b`-count: `combBBlock 0 = unitOp` and
`combBBlock (n+1) = m(leafB, combBBlock n)`, the canonical right-comb of `n` `b`-slots. -/
def combBBlock : Nat → TwoColourCommMonoidTree
  | 0 => TwoColourCommMonoidTree.unitOp
  | Nat.succ predecessor => TwoColourCommMonoidTree.mulOp TwoColourCommMonoidTree.leafB (combBBlock predecessor)

/-- The **canonical normal form** of a Parikh vector `(countA, countB)`: `countA` copies of `leafA` grafted to
the left of a `b`-block of `countB` copies of `leafB`, all right-combed —
`combOfCounts 0 countB = combBBlock countB` and
`combOfCounts (a+1) countB = m(leafA, combOfCounts a countB)`.  The unique representative of the free
commutative monoid element `(countA, countB) ∈ ℕ²`. -/
def combOfCounts : Nat → Nat → TwoColourCommMonoidTree
  | 0, countB => combBBlock countB
  | Nat.succ predecessorA, countB =>
      TwoColourCommMonoidTree.mulOp TwoColourCommMonoidTree.leafA (combOfCounts predecessorA countB)

/-! ## Bubbling a `b`-slot to the front and merging two normal forms -/

/-- **The `b`-bubble lemma** — prepending one `leafB` to the front of a normal form is convertible to the
normal form with its `b`-count incremented: `m(leafB, combOfCounts a b) ≈ combOfCounts a (b + 1)`.  Induction
on the `a`-count: the base is definitional (`combOfCounts 0 (b+1) = m(leafB, combBBlock b)`), the step swaps the
new `leafB` past the leading `leafA` (`commSwap` + `assoc` + `commSwap`) and applies the inductive
hypothesis. -/
theorem prependBBubble (countA countB : Nat) :
    TwoColourCommMonoidTreeConv
      (TwoColourCommMonoidTree.mulOp TwoColourCommMonoidTree.leafB (combOfCounts countA countB))
      (combOfCounts countA (countB + 1)) := by
  induction countA with
  | zero => exact TwoColourCommMonoidTreeConv.refl (combOfCounts 0 (countB + 1))
  | succ predecessorA ih =>
      exact TwoColourCommMonoidTreeConv.trans
        (TwoColourCommMonoidTreeConv.commSwap TwoColourCommMonoidTree.leafB
          (TwoColourCommMonoidTree.mulOp TwoColourCommMonoidTree.leafA (combOfCounts predecessorA countB)))
        (TwoColourCommMonoidTreeConv.trans
          (TwoColourCommMonoidTreeConv.assoc TwoColourCommMonoidTree.leafA (combOfCounts predecessorA countB)
            TwoColourCommMonoidTree.leafB)
          (TwoColourCommMonoidTreeConv.mulCongr (TwoColourCommMonoidTreeConv.refl TwoColourCommMonoidTree.leafA)
            (TwoColourCommMonoidTreeConv.trans
              (TwoColourCommMonoidTreeConv.commSwap (combOfCounts predecessorA countB)
                TwoColourCommMonoidTree.leafB)
              ih)))

/-- **The `b`-block merge** — grafting a `b`-block onto a normal form absorbs its `b`-slots one at a time:
`m(combBBlock countB1, combOfCounts countA2 countB2) ≈ combOfCounts countA2 (countB2 + countB1)`.  Induction on
`countB1`: the base is `unitLeft` (`countB2 + 0 = countB2` definitionally), the step re-associates the leading
`leafB` out (`assoc`), recurses (`mulCongr` + IH), and bubbles the freed `leafB` into the `b`-count
(`prependBBubble`); the index `countB2 + (countB1+1)` reduces definitionally to `(countB2 + countB1) + 1`. -/
theorem combMergeBBlock (countB1 countA2 countB2 : Nat) :
    TwoColourCommMonoidTreeConv
      (TwoColourCommMonoidTree.mulOp (combBBlock countB1) (combOfCounts countA2 countB2))
      (combOfCounts countA2 (countB2 + countB1)) := by
  induction countB1 with
  | zero => exact TwoColourCommMonoidTreeConv.unitLeft (combOfCounts countA2 countB2)
  | succ predecessorB innerIH =>
      exact TwoColourCommMonoidTreeConv.trans
        (TwoColourCommMonoidTreeConv.assoc TwoColourCommMonoidTree.leafB
          (combBBlock predecessorB) (combOfCounts countA2 countB2))
        (TwoColourCommMonoidTreeConv.trans
          (TwoColourCommMonoidTreeConv.mulCongr
            (TwoColourCommMonoidTreeConv.refl TwoColourCommMonoidTree.leafB) innerIH)
          (prependBBubble countA2 (countB2 + predecessorB)))

/-- ★ **The merge lemma** — grafting two normal forms is convertible to the normal form of the summed Parikh
vectors: `m(combOfCounts a1 b1, combOfCounts a2 b2) ≈ combOfCounts (a2 + a1) (b2 + b1)`.  Induction on `a1`: the
base is `combMergeBBlock` (`a2 + 0 = a2` definitionally), the step re-associates the leading `leafA` out and
recurses; the summed indices are ordered `(a2 + a1)` / `(b2 + b1)` so that `Nat.add`'s right recursion
discharges every step definitionally — no transport.  The commutativity of the sums is absorbed once, at the
normalization call site. -/
theorem combMerge (countA1 countB1 countA2 countB2 : Nat) :
    TwoColourCommMonoidTreeConv
      (TwoColourCommMonoidTree.mulOp (combOfCounts countA1 countB1) (combOfCounts countA2 countB2))
      (combOfCounts (countA2 + countA1) (countB2 + countB1)) := by
  induction countA1 with
  | zero => exact combMergeBBlock countB1 countA2 countB2
  | succ predecessorA outerIH =>
      exact TwoColourCommMonoidTreeConv.trans
        (TwoColourCommMonoidTreeConv.assoc TwoColourCommMonoidTree.leafA
          (combOfCounts predecessorA countB1) (combOfCounts countA2 countB2))
        (TwoColourCommMonoidTreeConv.mulCongr
          (TwoColourCommMonoidTreeConv.refl TwoColourCommMonoidTree.leafA) outerIH)

/-! ## Normalization: every tree reduces to its canonical normal form -/

/-- ★ **Normalization** — every tree is convertible to the canonical normal form of its own Parikh vector.
Induction on the tree: `leafA` and `leafB` reduce via right unit (`combOfCounts 1 0 = m(leafA, unitOp)`,
`combOfCounts 0 1 = m(leafB, unitOp)`), `unitOp` is already `combOfCounts 0 0`, and `mulOp` normalizes the two
children (`mulCongr`) then grafts them with `combMerge`, transporting the summed indices from the merge order
`(right + left)` back to the definitional `countXOf (mulOp left right) = left + right` order via `Nat.add_comm`
(the single commutativity absorption). -/
theorem twoColourCommMonoidReducesToNormal (tree : TwoColourCommMonoidTree) :
    TwoColourCommMonoidTreeConv tree (combOfCounts (countAOf tree) (countBOf tree)) := by
  induction tree with
  | leafA => exact TwoColourCommMonoidTreeConv.symm (TwoColourCommMonoidTreeConv.unitRight TwoColourCommMonoidTree.leafA)
  | leafB => exact TwoColourCommMonoidTreeConv.symm (TwoColourCommMonoidTreeConv.unitRight TwoColourCommMonoidTree.leafB)
  | unitOp => exact TwoColourCommMonoidTreeConv.refl TwoColourCommMonoidTree.unitOp
  | mulOp left right ihLeft ihRight =>
      have combined : TwoColourCommMonoidTreeConv (TwoColourCommMonoidTree.mulOp left right)
          (combOfCounts (countAOf right + countAOf left) (countBOf right + countBOf left)) :=
        TwoColourCommMonoidTreeConv.trans
          (TwoColourCommMonoidTreeConv.mulCongr ihLeft ihRight)
          (combMerge (countAOf left) (countBOf left) (countAOf right) (countBOf right))
      have treeEq : combOfCounts (countAOf right + countAOf left) (countBOf right + countBOf left)
          = combOfCounts (countAOf (TwoColourCommMonoidTree.mulOp left right))
              (countBOf (TwoColourCommMonoidTree.mulOp left right)) :=
        (congrArg (fun aIndex => combOfCounts aIndex (countBOf right + countBOf left))
            (Nat.add_comm (countAOf right) (countAOf left))).trans
          (congrArg (fun bIndex => combOfCounts (countAOf left + countAOf right) bIndex)
            (Nat.add_comm (countBOf right) (countBOf left)))
      exact treeEq ▸ combined

/-! ## Completeness and the decision -/

/-- ★ **Completeness** — equal `a`-count and equal `b`-count imply convertibility.  Both trees normalize to the
canonical normal form of their (equal) Parikh vector, so they are convertible through that common normal
form. -/
theorem twoColourCommMonoidConv_complete {source target : TwoColourCommMonoidTree}
    (eqA : countAOf source = countAOf target) (eqB : countBOf source = countBOf target) :
    TwoColourCommMonoidTreeConv source target := by
  have sourceReduces : TwoColourCommMonoidTreeConv source (combOfCounts (countAOf source) (countBOf source)) :=
    twoColourCommMonoidReducesToNormal source
  have targetReduces : TwoColourCommMonoidTreeConv target (combOfCounts (countAOf target) (countBOf target)) :=
    twoColourCommMonoidReducesToNormal target
  have combEq : combOfCounts (countAOf source) (countBOf source)
      = combOfCounts (countAOf target) (countBOf target) :=
    (congrArg (fun aIndex => combOfCounts aIndex (countBOf source)) eqA).trans
      (congrArg (fun bIndex => combOfCounts (countAOf target) bIndex) eqB)
  exact TwoColourCommMonoidTreeConv.trans sourceReduces
    (combEq.symm ▸ TwoColourCommMonoidTreeConv.symm targetReduces)

/-- ★ **The decision** — convertibility in the walking commutative monoid on two generators is exactly the
conjunction of `Nat` equalities of the two counts (the Parikh vectors coincide).  Since each count equality is
decidable (`Nat.decEq`), this biconditional decides the word problem. -/
theorem twoColourCommMonoidConv_iff_counts (source target : TwoColourCommMonoidTree) :
    TwoColourCommMonoidTreeConv source target ↔
      (countAOf source = countAOf target ∧ countBOf source = countBOf target) :=
  ⟨fun conv => ⟨twoColourCommMonoidConv_soundA conv, twoColourCommMonoidConv_soundB conv⟩,
   fun pair => twoColourCommMonoidConv_complete pair.1 pair.2⟩

/-- ★ **The decider** — a shipped `Decidable` for the two-colour convertibility, built from the two count
decisions: match the `a`-count decision, then (when it holds) the `b`-count decision, discharging `isTrue` by
completeness and each `isFalse` by the matching soundness component.  Full-enumeration nested matches (no
wildcard over the `Decidable` inductive), a genuine decider, propext-free. -/
def decideTwoColourCommMonoidTreeConv (source target : TwoColourCommMonoidTree) :
    Decidable (TwoColourCommMonoidTreeConv source target) :=
  match Nat.decEq (countAOf source) (countAOf target) with
  | isFalse countANe => isFalse (fun conv => countANe (twoColourCommMonoidConv_soundA conv))
  | isTrue countAEq =>
      match Nat.decEq (countBOf source) (countBOf target) with
      | isFalse countBNe => isFalse (fun conv => countBNe (twoColourCommMonoidConv_soundB conv))
      | isTrue countBEq => isTrue (twoColourCommMonoidConv_complete countAEq countBEq)

/-- The two-colour convertibility as a `Decidable` INSTANCE, so the `decide` tactic and instance resolution
fire on it — mirroring the single-generator sibling.  A definitional alias of the shipped
`decideTwoColourCommMonoidTreeConv`, hence propext-free. -/
instance instDecidableTwoColourCommMonoidTreeConv (source target : TwoColourCommMonoidTree) :
    Decidable (TwoColourCommMonoidTreeConv source target) :=
  decideTwoColourCommMonoidTreeConv source target

/-! ## Groundings -/

/-- ★ **Commutativity mixes the two colours** — `m(leafA, leafB) ≈ m(leafB, leafA)`: a cross-colour swap, the
move whose availability distinguishes the commutative monoid from the planar operad. -/
theorem twoColourCommMonoidCommHolds :
    TwoColourCommMonoidTreeConv
      (TwoColourCommMonoidTree.mulOp TwoColourCommMonoidTree.leafA TwoColourCommMonoidTree.leafB)
      (TwoColourCommMonoidTree.mulOp TwoColourCommMonoidTree.leafB TwoColourCommMonoidTree.leafA) :=
  TwoColourCommMonoidTreeConv.commSwap TwoColourCommMonoidTree.leafA TwoColourCommMonoidTree.leafB

/-- ★ **The decision in action (positive)** — two DIFFERENTLY-shaped trees with the same Parikh vector `(2, 1)`
are convertible, decided purely by their equal `a`-count (`2 = 2`) and `b`-count (`1 = 1`) through the
completeness leg — no explicit rewrite path supplied. -/
theorem twoColourCommMonoidDecidesEqualCounts :
    TwoColourCommMonoidTreeConv
      (TwoColourCommMonoidTree.mulOp
        (TwoColourCommMonoidTree.mulOp TwoColourCommMonoidTree.leafA TwoColourCommMonoidTree.leafA)
        TwoColourCommMonoidTree.leafB)
      (TwoColourCommMonoidTree.mulOp TwoColourCommMonoidTree.leafA
        (TwoColourCommMonoidTree.mulOp TwoColourCommMonoidTree.leafB TwoColourCommMonoidTree.leafA)) :=
  twoColourCommMonoidConv_complete rfl rfl

/-- ★ **The decision in action (negative)** — `m(leafA, m(leafB, leafB))` (Parikh `(1, 2)`) is NOT convertible
to `m(leafA, leafB)` (Parikh `(1, 1)`): the `b`-counts differ, so by the `b`-soundness component no
convertibility can exist.  `2 ≠ 1` by `Nat.noConfusion`. -/
theorem twoColourCommMonoidRejectsUnequalCountB :
    ¬ TwoColourCommMonoidTreeConv
        (TwoColourCommMonoidTree.mulOp TwoColourCommMonoidTree.leafA
          (TwoColourCommMonoidTree.mulOp TwoColourCommMonoidTree.leafB TwoColourCommMonoidTree.leafB))
        (TwoColourCommMonoidTree.mulOp TwoColourCommMonoidTree.leafA TwoColourCommMonoidTree.leafB) :=
  fun conv => Nat.noConfusion (twoColourCommMonoidConv_soundB conv)
    (fun oneEqZero => Nat.noConfusion oneEqZero)

/-! ## The marker -/

/-- ★ **The walking commutative monoid on TWO generators is DECIDED.**  `= true` records that
`twoColourCommMonoidConv_iff_counts` reduces the two-colour word problem to a PAIR of `Nat` equalities — the
coincidence of Parikh vectors in `ℕ²` — with soundness (per colour), normalization to the `a`-block/`b`-block
canonical form, and completeness all shipped.  The honest successor is the `n`-generator (arbitrary alphabet)
commutative monoid, whose invariant is a finite MULTISET over the generator set rather than a fixed tuple of
counts, decided by multiset (sorted-list) equality. -/
def fxWalkingCommMonoid_hasTwoColourDecision : Bool := true

end FX1Poly.Polygraph
