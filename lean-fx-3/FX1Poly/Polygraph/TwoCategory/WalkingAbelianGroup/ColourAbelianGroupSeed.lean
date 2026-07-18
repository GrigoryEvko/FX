import FX1Poly.Polygraph.TwoCategory.WalkingSemilattice.FiniteSetSemilatticeSeed

/-! # WalkingAbelianGroup/ColourAbelianGroupSeed — the walking free abelian group on an ARBITRARY alphabet
= ℤᵏ (free ℤ-module / finitely-supported ℕ→ℤ): the CROSS-ADDED multiset winding decision

The successor rung explicitly named as the honest wall in the single-generator sibling
(`AbelianGroupSeed`, invariant a single difference pair `⟨positiveSlots, inverseSlots⟩ : ℕ²` presenting ℤ).
Adjoining a formal inverse `i` to the free **commutative monoid** on the colour set `ℕ` (whose class is a
finite MULTISET of colours, `MultisetCommutativeMonoidSeed`) completes each per-colour count to its group of
differences — so the free **abelian group** on `ℕ` is `ℤᵏ`, the free ℤ-module: a tree's class is a per-colour
winding VECTOR.  This file decides that word problem WITHOUT a signed type and WITHOUT subtraction, holding
the winding vector as a difference of two sorted colour-multisets `⟨positiveColours, inverseColours⟩` under the
CROSS-ADDED multiset equivalence `insertMany posSource invTarget = insertMany posTarget invSource` — the
single-generator `p₁ + n₂ = p₂ + n₁` lifted from `ℕ` counts to sorted colour-lists, with the multiset merge
`insertMany` playing the role of `⊎` (and of `+`).

## ★ Why this walker is FULLY DECIDED (arbitrary alphabet) — and why the model is ℤᵏ

This file REUSES the multiset commutative-monoid substrate verbatim (imported transitively through
`FiniteSetSemilatticeSeed`): the purpose-built structural `natBle`, the sorted-insert `insertSorted`, the
merge `insertMany`, and all their algebra (`insertSortedComm` / `insertManyAssoc` / `insertManyComm`).  The
genuinely new work is a **multiset cancellation kit** — `deleteFirst` as a left-inverse of `insertSorted`
(`insertSortedRetract`), giving injectivity (`insertSortedInjective`) and prefix cancellation
(`insertManyLeftCancel`), the analogue of the single generator's additive `Nat` right cancellation.  This file
ships:

* **soundness** — convertible trees have `multisetWindingEquiv` winding vectors
  (`colourAbelianGroupTreeConv_sound`); every abelian-group law preserves the cross-added multiset;
* **normalization** — every tree reduces to an unreduced colour pair-form
  (`toPairFormColoursConv`), grafting via `pairFormMergeColours`;
* **completeness** — `multisetWindingEquiv` winding vectors ⟹ convertible, by pumping both pair-forms to a
  common one via a cancelling `m(leaf c, i leaf c) ≈ e` insertion (`colourAbelianGroupTreeConv_complete`);
* **the decision** — the convertibility ⟺ `multisetWindingEquiv` biconditional plus a genuine `Decidable`
  (`colourAbelianGroupTreeConv_iff_windingEquiv`, `decideColourAbelianGroupTreeConv`).

This CLOSES the ℤᵏ successor wall that `AbelianGroupSeed` named.

Raw Lean 4 + Init; the convertibility is an inductive `Prop`; per-declaration `#assert_no_axioms` gated in the
audit twin.  Free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`, `Nat.sub`, and
`Int` — the ordering is the imported structural `natBle` (no `Nat.le`/`Nat.ble` lemma), the inserts are
cons-only, and no `List.append` (`++`) appears anywhere. -/

namespace FX1Poly.Polygraph

/-! ## The abelian-group tree carrier over a colour alphabet -/

/-- ★ The **tree carrier** of the walking abelian group on an arbitrary alphabet: an un-indexed tree over
colour-indexed input slots plus the three group generators.  `leaf colour` is an arity-1 input slot tagged
with a colour in `ℕ`; `unitOp` is the nullary generator `e`; `invOp` applies the unary inverse `i`; `mulOp`
grafts two subtrees under the binary generator `m`.  A closed tree's per-colour winding vector — held as a
difference of two sorted colour-multisets — is its complete convertibility invariant. -/
inductive ColourAbelianTree where
  /-- An arity-1 input slot tagged with a colour in `ℕ` — a generator of the chosen alphabet. -/
  | leaf (colour : Nat)
  /-- The nullary generator `e : arity 0` (the group unit). -/
  | unitOp
  /-- The unary generator `i : arity 1` (the group inverse) applied to a subtree. -/
  | invOp : ColourAbelianTree → ColourAbelianTree
  /-- The binary generator `m : arity 2` grafting the left and right subtrees (`m(left, right)`). -/
  | mulOp : ColourAbelianTree → ColourAbelianTree → ColourAbelianTree

/-! ## The winding invariant: a difference of two sorted colour-multisets (ℤᵏ, no signed type, no subtraction) -/

/-- The **winding colour-lists** of a tree — the pair `(positive colours, inverse colours)`, each a sorted
colour-multiset (the normal form under `insertMany`).  `leaf colour ↦ ([colour], [])`, `unitOp ↦ ([], [])`,
`invOp` SWAPS the two components (passing through one inverse flips positive and inverse), and `mulOp` merges
componentwise via `insertMany`.  The (per-colour Grothendieck) difference is the winding vector in `ℤᵏ`.  A
full-enumeration structural fold (no wildcard), propext-clean. -/
def windingColoursOf : ColourAbelianTree → (List Nat × List Nat)
  | .leaf colour => ([colour], [])
  | .unitOp => ([], [])
  | .invOp inner => ((windingColoursOf inner).2, (windingColoursOf inner).1)
  | .mulOp left right =>
      (insertMany (windingColoursOf left).1 (windingColoursOf right).1,
       insertMany (windingColoursOf left).2 (windingColoursOf right).2)

/-- The **positive colour-multiset** of a tree — colours reached through an even number of inverses. -/
def posColoursOf (tree : ColourAbelianTree) : List Nat := (windingColoursOf tree).1

/-- The **inverse colour-multiset** of a tree — colours reached through an odd number of inverses. -/
def invColoursOf (tree : ColourAbelianTree) : List Nat := (windingColoursOf tree).2

/-- Smoke: a single input slot has positive colour-list its singleton. -/
theorem posColoursOf_leaf : posColoursOf (ColourAbelianTree.leaf 3) = [3] := rfl

/-- Smoke: an inverted slot moves its colour to the inverse list. -/
theorem invColoursOf_invLeaf : invColoursOf (ColourAbelianTree.invOp (ColourAbelianTree.leaf 3)) = [3] := rfl

/-- Smoke: a two-colour graft sorts its positive colours. -/
theorem posColoursOf_mulSorts :
    posColoursOf (ColourAbelianTree.mulOp (ColourAbelianTree.leaf 3) (ColourAbelianTree.leaf 1)) = [1, 3] :=
  rfl

/-! ## The multiset-cancellation kit (the genuinely new work: `deleteFirst` retracts `insertSorted`) -/

/-- Structural reflexivity of the core Boolean equality `Nat.beq`: `Nat.beq value value = true`. -/
theorem natBeqRefl : (value : Nat) → Nat.beq value value = true
  | 0 => rfl
  | Nat.succ predecessor => natBeqRefl predecessor

/-- Soundness of `Nat.beq`: `Nat.beq first second = true` forces `first = second`.  Structural recursion on
both arguments; the mixed corners fall to `Bool.noConfusion`. -/
theorem natBeqSound : (first second : Nat) → Nat.beq first second = true → first = second
  | 0, 0, _ => rfl
  | 0, Nat.succ _, hbeq => Bool.noConfusion hbeq
  | Nat.succ _, 0, hbeq => Bool.noConfusion hbeq
  | Nat.succ firstPredecessor, Nat.succ secondPredecessor, hbeq =>
      congrArg Nat.succ (natBeqSound firstPredecessor secondPredecessor hbeq)

/-- Remove the **first occurrence** of `target` from a list (by the core Boolean equality `Nat.beq`).  The
left-inverse of `insertSorted` used to make `insertSorted` injective. -/
def deleteFirst (target : Nat) : List Nat → List Nat
  | [] => []
  | head :: tail =>
      match Nat.beq head target with
      | true => tail
      | false => head :: deleteFirst target tail

/-- Equation: when the head equals `target` (`Nat.beq` true), the head is dropped. -/
theorem deleteFirstConsTrue (target head : Nat) (tail : List Nat) (h : Nat.beq head target = true) :
    deleteFirst target (head :: tail) = tail := by
  show (match Nat.beq head target with
        | true => tail
        | false => head :: deleteFirst target tail) = tail
  rw [h]

/-- Equation: when the head differs from `target` (`Nat.beq` false), the head stays and deletion recurses. -/
theorem deleteFirstConsFalse (target head : Nat) (tail : List Nat) (h : Nat.beq head target = false) :
    deleteFirst target (head :: tail) = head :: deleteFirst target tail := by
  show (match Nat.beq head target with
        | true => tail
        | false => head :: deleteFirst target tail) = head :: deleteFirst target tail
  rw [h]

/-- ★ **`deleteFirst` retracts `insertSorted`** (no sortedness needed): `deleteFirst v (insertSorted v xs) = xs`.
Induction on `xs`; at the false (`v > head`) cons branch, `natBleRefl` forces `head ≠ v` (so `Nat.beq head v`
is false and `deleteFirst` skips the head) and the induction hypothesis closes the tail. -/
theorem insertSortedRetract (value : Nat) (xs : List Nat) :
    deleteFirst value (insertSorted value xs) = xs := by
  induction xs with
  | nil =>
    rw [insertSortedNilEq value]
    exact deleteFirstConsTrue value value [] (natBeqRefl value)
  | cons head tail ih =>
    cases hVH : natBle value head with
    | true =>
      rw [insertSortedConsTrue value head tail hVH]
      exact deleteFirstConsTrue value value (head :: tail) (natBeqRefl value)
    | false =>
      rw [insertSortedConsFalse value head tail hVH]
      cases hbeq : Nat.beq head value with
      | false =>
        rw [deleteFirstConsFalse value head (insertSorted value tail) hbeq]
        exact congrArg (fun rest => head :: rest) ih
      | true =>
        have hEq : head = value := natBeqSound head value hbeq
        rw [hEq] at hVH
        exact Bool.noConfusion ((natBleRefl value).symm.trans hVH)

/-- **`insertSorted` is injective** in its list argument (via the `deleteFirst` retract). -/
theorem insertSortedInjective (value : Nat) (xs ys : List Nat)
    (insertsEq : insertSorted value xs = insertSorted value ys) : xs = ys :=
  (insertSortedRetract value xs).symm.trans
    ((congrArg (deleteFirst value) insertsEq).trans (insertSortedRetract value ys))

/-- ★ **Left cancellation of a common prefix-multiset**: `insertMany common xs = insertMany common ys → xs = ys`.
Structural recursion on `common`; each cons peels one `insertSorted head` via `insertSortedInjective`.  The
multiset analogue of the single generator's additive `Nat` cancellation. -/
theorem insertManyLeftCancel : (common xs ys : List Nat) →
    insertMany common xs = insertMany common ys → xs = ys
  | [], _, _, prefixEq => prefixEq
  | head :: tail, xs, ys, prefixEq =>
      insertManyLeftCancel tail xs ys
        (insertSortedInjective head (insertMany tail xs) (insertMany tail ys) prefixEq)

/-! ## The `insertMany` arithmetic kit (mirrors the single generator's `Nat` kit; `insertMany a b` reads as `a ⊎ b`) -/

/-- The **middle-four exchange** `(a ⊎ b) ⊎ (c ⊎ d) = (a ⊎ c) ⊎ (b ⊎ d)` — pure `insertManyAssoc` /
`insertManyComm` (kept in the nested `insertMany _ (insertMany _ _)` shape on both sides).  The one
reassociation engine the multiplication congruence shares.  Mirrors the single generator's `addMiddleFour`. -/
theorem insertManyMiddleFour (aa bb cc dd : List Nat) :
    insertMany (insertMany aa bb) (insertMany cc dd) = insertMany (insertMany aa cc) (insertMany bb dd) :=
  (insertManyAssoc aa bb (insertMany cc dd)).trans
    ((congrArg (insertMany aa) (insertManyComm bb cc dd)).trans
      (insertManyAssoc aa cc (insertMany bb dd)).symm)

/-- A cross-sum block is a fixed point of `insertMany · []` when its accumulator side is: `insertMany (insertMany
xs ys) [] = insertMany xs ys` given `insertMany ys [] = ys`.  The tool for reading `insertMany [] _` off both
ends of a `blockComm`. -/
theorem insertManyPairSortedFixed (xs ys : List Nat) (hys : insertMany ys [] = ys) :
    insertMany (insertMany xs ys) [] = insertMany xs ys :=
  (insertManyAssoc xs ys []).trans (congrArg (insertMany xs) hys)

/-- **Block commutation for sorted-fixed operands**: `insertMany aa bb = insertMany bb aa` when both `aa` and
`bb` are fixed points of `insertMany · []` (i.e. already sorted).  The role the single generator got for free
from `Nat.add_comm`.  Routes through the nested `insertMany _ (insertMany _ [])` form and back. -/
theorem insertManyBlockComm (aa bb : List Nat)
    (haa : insertMany aa [] = aa) (hbb : insertMany bb [] = bb) :
    insertMany aa bb = insertMany bb aa :=
  (congrArg (insertMany aa) hbb.symm).trans
    ((insertManyComm aa bb []).trans (congrArg (insertMany bb) haa))

/-- The **diagonal exchange for sorted-fixed operands** `(a ⊎ b) ⊎ (c ⊎ d) = (a ⊎ d) ⊎ (c ⊎ b)` — swaps the
two trailing blocks.  Built from `insertManyMiddleFour` twice around one `insertManyBlockComm` (which is why
the swapped blocks `bb`, `dd` must be sorted-fixed).  Mirrors the single generator's `addExchange`. -/
theorem insertManyExchangeFixed (aa bb cc dd : List Nat)
    (hbb : insertMany bb [] = bb) (hdd : insertMany dd [] = dd) :
    insertMany (insertMany aa bb) (insertMany cc dd) = insertMany (insertMany aa dd) (insertMany cc bb) :=
  (insertManyMiddleFour aa bb cc dd).trans
    ((congrArg (insertMany (insertMany aa cc)) (insertManyBlockComm bb dd hbb hdd)).trans
      (insertManyMiddleFour aa cc dd bb))

/-! ## Sorted-fixedness of the winding colour-lists -/

/-- ★ **The winding colour-lists are sorted-fixed**: `insertMany (posColoursOf tree) [] = posColoursOf tree`
and the inverse version.  Paired structural induction on the tree (the `invOp` case swaps the two components,
so the pair must be proved together); `mulOp` re-associates the trailing `[]` onto the right child via the
right induction hypothesis.  This imports the sortedness that `insertMany`'s order-dependence needs. -/
theorem windingColoursSortedFixed (tree : ColourAbelianTree) :
    insertMany (posColoursOf tree) [] = posColoursOf tree
      ∧ insertMany (invColoursOf tree) [] = invColoursOf tree := by
  induction tree with
  | leaf colour => exact ⟨rfl, rfl⟩
  | unitOp => exact ⟨rfl, rfl⟩
  | invOp inner ih => exact ⟨ih.2, ih.1⟩
  | mulOp left right _ ihRight =>
    exact
      ⟨(insertManyAssoc (posColoursOf left) (posColoursOf right) []).trans
          (congrArg (insertMany (posColoursOf left)) ihRight.1),
       (insertManyAssoc (invColoursOf left) (invColoursOf right) []).trans
          (congrArg (insertMany (invColoursOf left)) ihRight.2)⟩

/-! ## The winding equivalence (cross-added multiset equality) and its algebra -/

/-- The **winding equivalence** — two winding vectors present the same element of `ℤᵏ`.  Stated purely as a
CROSS-ADDED multiset equality (`insertMany posSource invTarget = insertMany posTarget invSource`), so it needs
no subtraction and no signed type; decidable via `DecidableEq (List Nat)`. -/
def multisetWindingEquiv (source target : ColourAbelianTree) : Prop :=
  insertMany (posColoursOf source) (invColoursOf target)
    = insertMany (posColoursOf target) (invColoursOf source)

/-- `multisetWindingEquiv` is reflexive. -/
theorem multisetWindingEquivRefl (tree : ColourAbelianTree) : multisetWindingEquiv tree tree := rfl

/-- `multisetWindingEquiv` is symmetric. -/
theorem multisetWindingEquivSymm {source target : ColourAbelianTree}
    (equiv : multisetWindingEquiv source target) : multisetWindingEquiv target source := equiv.symm

/-- `multisetWindingEquiv` respects the componentwise merge — the winding shadow of `mulCongr`, built from
`insertManyMiddleFour` (mirrors the single generator's `windingEquivMulCongr`). -/
theorem multisetWindingEquivMulCongr {leftOld leftNew rightOld rightNew : ColourAbelianTree}
    (leftEquiv : multisetWindingEquiv leftOld leftNew)
    (rightEquiv : multisetWindingEquiv rightOld rightNew) :
    multisetWindingEquiv (ColourAbelianTree.mulOp leftOld rightOld)
      (ColourAbelianTree.mulOp leftNew rightNew) :=
  (insertManyMiddleFour (posColoursOf leftOld) (posColoursOf rightOld)
      (invColoursOf leftNew) (invColoursOf rightNew)).trans
    ((congrArg (fun leftPart =>
          insertMany leftPart (insertMany (posColoursOf rightOld) (invColoursOf rightNew))) leftEquiv).trans
      ((congrArg (insertMany (insertMany (posColoursOf leftNew) (invColoursOf leftOld))) rightEquiv).trans
        (insertManyMiddleFour (posColoursOf leftNew) (invColoursOf leftOld)
          (posColoursOf rightNew) (invColoursOf rightOld))))

/-- `multisetWindingEquiv` respects the inverse swap — the winding shadow of `invCongr`, built from two
`insertManyBlockComm`s around the hypothesis (mirrors the single generator's `windingEquivInvCongr`). -/
theorem multisetWindingEquivInvCongr {innerOld innerNew : ColourAbelianTree}
    (innerEquiv : multisetWindingEquiv innerOld innerNew) :
    multisetWindingEquiv (ColourAbelianTree.invOp innerOld) (ColourAbelianTree.invOp innerNew) :=
  (insertManyBlockComm (invColoursOf innerOld) (posColoursOf innerNew)
      (windingColoursSortedFixed innerOld).2 (windingColoursSortedFixed innerNew).1).trans
    (innerEquiv.symm.trans
      (insertManyBlockComm (posColoursOf innerOld) (invColoursOf innerNew)
        (windingColoursSortedFixed innerOld).1 (windingColoursSortedFixed innerNew).2))

/-- ★ `multisetWindingEquiv` is **transitive** — the one nontrivial step.  Mirrors the single generator's
`windingEquivTrans`: two `insertManyExchangeFixed`s bracket the two hypotheses, a final `insertManyBlockComm`
(the multiset `add_comm`) exposes the common block `insertMany (posColoursOf b) (invColoursOf b)`, and
`insertManyLeftCancel` cancels it. -/
theorem multisetWindingEquivTrans {treeA treeB treeC : ColourAbelianTree}
    (equivAB : multisetWindingEquiv treeA treeB) (equivBC : multisetWindingEquiv treeB treeC) :
    multisetWindingEquiv treeA treeC :=
  insertManyLeftCancel (insertMany (posColoursOf treeB) (invColoursOf treeB))
    (insertMany (posColoursOf treeA) (invColoursOf treeC))
    (insertMany (posColoursOf treeC) (invColoursOf treeA))
    ((insertManyExchangeFixed (posColoursOf treeB) (invColoursOf treeB)
        (posColoursOf treeA) (invColoursOf treeC)
        (windingColoursSortedFixed treeB).2 (windingColoursSortedFixed treeC).2).trans
      ((congrArg (fun blk => insertMany blk (insertMany (posColoursOf treeA) (invColoursOf treeB)))
            equivBC).trans
        ((congrArg (insertMany (insertMany (posColoursOf treeC) (invColoursOf treeB))) equivAB).trans
          ((insertManyExchangeFixed (posColoursOf treeC) (invColoursOf treeB)
              (posColoursOf treeB) (invColoursOf treeA)
              (windingColoursSortedFixed treeB).2 (windingColoursSortedFixed treeA).2).trans
            (insertManyBlockComm (insertMany (posColoursOf treeC) (invColoursOf treeA))
              (insertMany (posColoursOf treeB) (invColoursOf treeB))
              (insertManyPairSortedFixed (posColoursOf treeC) (invColoursOf treeA)
                (windingColoursSortedFixed treeA).2)
              (insertManyPairSortedFixed (posColoursOf treeB) (invColoursOf treeB)
                (windingColoursSortedFixed treeB).2))))))

/-! ## The abelian-group tree convertibility -/

/-- ★ The **tree convertibility** of the walking abelian group on an arbitrary alphabet — the free
convertibility of the `{m, e, i}` signature over colour-tagged generators closed under the abelian-group laws
(associativity, left/right unit, commutativity, left/right inverse, and the inverse-homomorphism laws), the
full congruences `mulCongr` / `invCongr`, and `refl` / `symm` / `trans`.  Same shapes as the single-generator
sibling over the colour-tagged carrier.  Two trees denote the same element of the free abelian group on `ℕ`
exactly when they are `ColourAbelianGroupTreeConv`-related. -/
inductive ColourAbelianGroupTreeConv : ColourAbelianTree → ColourAbelianTree → Prop where
  /-- **Associativity** `m(m(left, middle), right) ≈ m(left, m(middle, right))`. -/
  | assoc (left middle right : ColourAbelianTree) :
      ColourAbelianGroupTreeConv
        (ColourAbelianTree.mulOp (ColourAbelianTree.mulOp left middle) right)
        (ColourAbelianTree.mulOp left (ColourAbelianTree.mulOp middle right))
  /-- **Left unit** `m(e, subtree) ≈ subtree`. -/
  | unitLeft (subtree : ColourAbelianTree) :
      ColourAbelianGroupTreeConv (ColourAbelianTree.mulOp ColourAbelianTree.unitOp subtree) subtree
  /-- **Right unit** `m(subtree, e) ≈ subtree`. -/
  | unitRight (subtree : ColourAbelianTree) :
      ColourAbelianGroupTreeConv (ColourAbelianTree.mulOp subtree ColourAbelianTree.unitOp) subtree
  /-- **Commutativity** `m(left, right) ≈ m(right, left)` — mixing colours freely. -/
  | commSwap (left right : ColourAbelianTree) :
      ColourAbelianGroupTreeConv (ColourAbelianTree.mulOp left right)
        (ColourAbelianTree.mulOp right left)
  /-- **Left inverse** `m(i subtree, subtree) ≈ e`. -/
  | invLeft (subtree : ColourAbelianTree) :
      ColourAbelianGroupTreeConv
        (ColourAbelianTree.mulOp (ColourAbelianTree.invOp subtree) subtree) ColourAbelianTree.unitOp
  /-- **Right inverse** `m(subtree, i subtree) ≈ e`. -/
  | invRight (subtree : ColourAbelianTree) :
      ColourAbelianGroupTreeConv
        (ColourAbelianTree.mulOp subtree (ColourAbelianTree.invOp subtree)) ColourAbelianTree.unitOp
  /-- **Inverse homomorphism** `i(m(treeA, treeB)) ≈ m(i treeA, i treeB)` (valid because the group is abelian,
  so the inverse distributes without reversing order). -/
  | invHom (treeA treeB : ColourAbelianTree) :
      ColourAbelianGroupTreeConv (ColourAbelianTree.invOp (ColourAbelianTree.mulOp treeA treeB))
        (ColourAbelianTree.mulOp (ColourAbelianTree.invOp treeA) (ColourAbelianTree.invOp treeB))
  /-- **Inverse of unit** `i e ≈ e`. -/
  | invUnit :
      ColourAbelianGroupTreeConv (ColourAbelianTree.invOp ColourAbelianTree.unitOp) ColourAbelianTree.unitOp
  /-- **Inverse involution** `i(i subtree) ≈ subtree`. -/
  | invInvol (subtree : ColourAbelianTree) :
      ColourAbelianGroupTreeConv (ColourAbelianTree.invOp (ColourAbelianTree.invOp subtree)) subtree
  /-- **Congruence under a grafting node** — into BOTH children. -/
  | mulCongr {leftOld leftNew rightOld rightNew : ColourAbelianTree} :
      ColourAbelianGroupTreeConv leftOld leftNew → ColourAbelianGroupTreeConv rightOld rightNew →
      ColourAbelianGroupTreeConv (ColourAbelianTree.mulOp leftOld rightOld)
        (ColourAbelianTree.mulOp leftNew rightNew)
  /-- **Congruence under an inverse node**. -/
  | invCongr {innerOld innerNew : ColourAbelianTree} :
      ColourAbelianGroupTreeConv innerOld innerNew →
      ColourAbelianGroupTreeConv (ColourAbelianTree.invOp innerOld) (ColourAbelianTree.invOp innerNew)
  /-- Reflexivity. -/
  | refl (tree : ColourAbelianTree) : ColourAbelianGroupTreeConv tree tree
  /-- Symmetry. -/
  | symm {tree1 tree2 : ColourAbelianTree} :
      ColourAbelianGroupTreeConv tree1 tree2 → ColourAbelianGroupTreeConv tree2 tree1
  /-- Transitivity. -/
  | trans {tree1 tree2 tree3 : ColourAbelianTree} :
      ColourAbelianGroupTreeConv tree1 tree2 → ColourAbelianGroupTreeConv tree2 tree3 →
      ColourAbelianGroupTreeConv tree1 tree3

/-! ## Soundness: convertible ⟹ winding-equivalent -/

/-- ★ **Soundness** — convertible trees have `multisetWindingEquiv` winding vectors.  Every law preserves the
cross-added multiset: the (co)unit / associativity laws by `insertMany [] _` / `insertManyAssoc`, commutativity
by `insertManyBlockComm`, the inverse laws because the swap makes `m(i x, x)` cross-add symmetrically, the
inverse-homomorphism laws by pure `rfl`, and the congruences by the two winding-congruence shadows.  All
list-arithmetic is propext-clean; no `Nat.sub`, no signed cancellation. -/
theorem colourAbelianGroupTreeConv_sound {source target : ColourAbelianTree}
    (conv : ColourAbelianGroupTreeConv source target) :
    multisetWindingEquiv source target := by
  induction conv with
  | assoc left middle right =>
    exact (congrArg (fun positivePart => insertMany positivePart
              (invColoursOf (ColourAbelianTree.mulOp left (ColourAbelianTree.mulOp middle right))))
            (insertManyAssoc (posColoursOf left) (posColoursOf middle) (posColoursOf right))).trans
      (congrArg (insertMany (posColoursOf (ColourAbelianTree.mulOp left
              (ColourAbelianTree.mulOp middle right))))
        (insertManyAssoc (invColoursOf left) (invColoursOf middle) (invColoursOf right)).symm)
  | unitLeft subtree => rfl
  | unitRight subtree =>
    exact (congrArg (fun positivePart => insertMany positivePart (invColoursOf subtree))
            (windingColoursSortedFixed subtree).1).trans
      (congrArg (insertMany (posColoursOf subtree)) (windingColoursSortedFixed subtree).2.symm)
  | commSwap left right =>
    exact (congrArg (fun positivePart =>
              insertMany positivePart (invColoursOf (ColourAbelianTree.mulOp right left)))
            (insertManyBlockComm (posColoursOf left) (posColoursOf right)
              (windingColoursSortedFixed left).1 (windingColoursSortedFixed right).1)).trans
      (congrArg (insertMany (posColoursOf (ColourAbelianTree.mulOp right left)))
        (insertManyBlockComm (invColoursOf right) (invColoursOf left)
          (windingColoursSortedFixed right).2 (windingColoursSortedFixed left).2))
  | invLeft subtree =>
    exact (insertManyPairSortedFixed (invColoursOf subtree) (posColoursOf subtree)
            (windingColoursSortedFixed subtree).1).trans
      (insertManyBlockComm (invColoursOf subtree) (posColoursOf subtree)
        (windingColoursSortedFixed subtree).2 (windingColoursSortedFixed subtree).1)
  | invRight subtree =>
    exact (insertManyPairSortedFixed (posColoursOf subtree) (invColoursOf subtree)
            (windingColoursSortedFixed subtree).2).trans
      (insertManyBlockComm (posColoursOf subtree) (invColoursOf subtree)
        (windingColoursSortedFixed subtree).1 (windingColoursSortedFixed subtree).2)
  | invHom treeA treeB => rfl
  | invUnit => rfl
  | invInvol subtree => rfl
  | @mulCongr leftOld leftNew rightOld rightNew _ _ ihLeft ihRight =>
    exact multisetWindingEquivMulCongr ihLeft ihRight
  | @invCongr innerOld innerNew _ ihInner =>
    exact multisetWindingEquivInvCongr ihInner
  | refl tree => exact multisetWindingEquivRefl tree
  | symm _ ih => exact multisetWindingEquivSymm ih
  | trans _ _ ihAB ihBC => exact multisetWindingEquivTrans ihAB ihBC

/-! ## Normalization: every tree reduces to an unreduced colour pair-form -/

/-- The **positive colour-comb** of a colour list: `[] ↦ e` and `colour :: rest ↦ m(leaf colour, ·)`. -/
def combPosColours : List Nat → ColourAbelianTree
  | [] => ColourAbelianTree.unitOp
  | colour :: rest => ColourAbelianTree.mulOp (ColourAbelianTree.leaf colour) (combPosColours rest)

/-- The **inverse colour-comb** of a colour list: `[] ↦ e` and `colour :: rest ↦ m(i(leaf colour), ·)`. -/
def combInvColours : List Nat → ColourAbelianTree
  | [] => ColourAbelianTree.unitOp
  | colour :: rest =>
      ColourAbelianTree.mulOp (ColourAbelianTree.invOp (ColourAbelianTree.leaf colour)) (combInvColours rest)

/-- The **colour pair-form** normal shape `m(combPosColours pos, combInvColours inv)` — an (unreduced)
difference of the positive colour-multiset `pos` and the inverse colour-multiset `inv`. -/
def pairFormColours (pos inv : List Nat) : ColourAbelianTree :=
  ColourAbelianTree.mulOp (combPosColours pos) (combInvColours inv)

/-- A syntactic tree equality lifts to convertibility (via `Eq.rec`, propext-clean). -/
theorem convOfTreeEqColours {left right : ColourAbelianTree} (treeEq : left = right) :
    ColourAbelianGroupTreeConv left right := by
  cases treeEq
  exact ColourAbelianGroupTreeConv.refl left

/-- The **tree middle-four exchange** `m(m(A, B), m(C, D)) ≈ m(m(A, C), m(B, D))` — the associativity +
commutativity shuffle regrouping four subtrees.  Mirrors the single generator's `convMiddleFour`. -/
theorem convMiddleFourColours (treeA treeB treeC treeD : ColourAbelianTree) :
    ColourAbelianGroupTreeConv
      (ColourAbelianTree.mulOp (ColourAbelianTree.mulOp treeA treeB)
        (ColourAbelianTree.mulOp treeC treeD))
      (ColourAbelianTree.mulOp (ColourAbelianTree.mulOp treeA treeC)
        (ColourAbelianTree.mulOp treeB treeD)) :=
  (ColourAbelianGroupTreeConv.assoc treeA treeB (ColourAbelianTree.mulOp treeC treeD)).trans
    ((ColourAbelianGroupTreeConv.mulCongr (ColourAbelianGroupTreeConv.refl treeA)
        (ColourAbelianGroupTreeConv.symm (ColourAbelianGroupTreeConv.assoc treeB treeC treeD))).trans
      ((ColourAbelianGroupTreeConv.mulCongr (ColourAbelianGroupTreeConv.refl treeA)
          (ColourAbelianGroupTreeConv.mulCongr (ColourAbelianGroupTreeConv.commSwap treeB treeC)
            (ColourAbelianGroupTreeConv.refl treeD))).trans
        ((ColourAbelianGroupTreeConv.mulCongr (ColourAbelianGroupTreeConv.refl treeA)
            (ColourAbelianGroupTreeConv.assoc treeC treeB treeD)).trans
          (ColourAbelianGroupTreeConv.symm
            (ColourAbelianGroupTreeConv.assoc treeA treeC (ColourAbelianTree.mulOp treeB treeD))))))

/-- **Inserting a colour into a positive comb is convertible to grafting it on the front**:
`combPosColours (insertSorted colour xs) ≈ m(leaf colour, combPosColours xs)`.  Induction on `xs`; the `false`
cons bubbles the new colour past the head via `commSwap` sandwiched between two associativities. -/
theorem combPosInsertSorted (colour : Nat) (xs : List Nat) :
    ColourAbelianGroupTreeConv (combPosColours (insertSorted colour xs))
      (ColourAbelianTree.mulOp (ColourAbelianTree.leaf colour) (combPosColours xs)) := by
  induction xs with
  | nil => exact ColourAbelianGroupTreeConv.refl _
  | cons head rest ih =>
    cases h : natBle colour head with
    | true =>
      rw [insertSortedConsTrue colour head rest h]
      exact ColourAbelianGroupTreeConv.refl _
    | false =>
      rw [insertSortedConsFalse colour head rest h]
      exact
        (ColourAbelianGroupTreeConv.mulCongr (ColourAbelianGroupTreeConv.refl (ColourAbelianTree.leaf head))
            ih).trans
          ((ColourAbelianGroupTreeConv.symm
              (ColourAbelianGroupTreeConv.assoc (ColourAbelianTree.leaf head) (ColourAbelianTree.leaf colour)
                (combPosColours rest))).trans
            ((ColourAbelianGroupTreeConv.mulCongr
                (ColourAbelianGroupTreeConv.commSwap (ColourAbelianTree.leaf head)
                  (ColourAbelianTree.leaf colour))
                (ColourAbelianGroupTreeConv.refl (combPosColours rest))).trans
              (ColourAbelianGroupTreeConv.assoc (ColourAbelianTree.leaf colour) (ColourAbelianTree.leaf head)
                (combPosColours rest))))

/-- **Inserting a colour into an inverse comb is convertible to grafting it on the front**:
`combInvColours (insertSorted colour xs) ≈ m(i(leaf colour), combInvColours xs)`.  Same shape as
`combPosInsertSorted` with `i(leaf ·)` in place of `leaf ·`. -/
theorem combInvInsertSorted (colour : Nat) (xs : List Nat) :
    ColourAbelianGroupTreeConv (combInvColours (insertSorted colour xs))
      (ColourAbelianTree.mulOp (ColourAbelianTree.invOp (ColourAbelianTree.leaf colour))
        (combInvColours xs)) := by
  induction xs with
  | nil => exact ColourAbelianGroupTreeConv.refl _
  | cons head rest ih =>
    cases h : natBle colour head with
    | true =>
      rw [insertSortedConsTrue colour head rest h]
      exact ColourAbelianGroupTreeConv.refl _
    | false =>
      rw [insertSortedConsFalse colour head rest h]
      exact
        (ColourAbelianGroupTreeConv.mulCongr
            (ColourAbelianGroupTreeConv.refl (ColourAbelianTree.invOp (ColourAbelianTree.leaf head))) ih).trans
          ((ColourAbelianGroupTreeConv.symm
              (ColourAbelianGroupTreeConv.assoc (ColourAbelianTree.invOp (ColourAbelianTree.leaf head))
                (ColourAbelianTree.invOp (ColourAbelianTree.leaf colour)) (combInvColours rest))).trans
            ((ColourAbelianGroupTreeConv.mulCongr
                (ColourAbelianGroupTreeConv.commSwap (ColourAbelianTree.invOp (ColourAbelianTree.leaf head))
                  (ColourAbelianTree.invOp (ColourAbelianTree.leaf colour)))
                (ColourAbelianGroupTreeConv.refl (combInvColours rest))).trans
              (ColourAbelianGroupTreeConv.assoc (ColourAbelianTree.invOp (ColourAbelianTree.leaf colour))
                (ColourAbelianTree.invOp (ColourAbelianTree.leaf head)) (combInvColours rest))))

/-- **Grafting two positive combs concatenates them**: `m(combPosColours xs, combPosColours ys) ≈
combPosColours (insertMany xs ys)`.  Induction on `xs`; the cons case re-associates the leading colour out,
recurses, and re-absorbs it via `combPosInsertSorted`. -/
theorem combPosConcatColours (xs ys : List Nat) :
    ColourAbelianGroupTreeConv (ColourAbelianTree.mulOp (combPosColours xs) (combPosColours ys))
      (combPosColours (insertMany xs ys)) := by
  induction xs with
  | nil => exact ColourAbelianGroupTreeConv.unitLeft (combPosColours ys)
  | cons head tail ih =>
    exact
      (ColourAbelianGroupTreeConv.assoc (ColourAbelianTree.leaf head) (combPosColours tail)
          (combPosColours ys)).trans
        ((ColourAbelianGroupTreeConv.mulCongr (ColourAbelianGroupTreeConv.refl (ColourAbelianTree.leaf head))
            ih).trans
          (ColourAbelianGroupTreeConv.symm (combPosInsertSorted head (insertMany tail ys))))

/-- **Grafting two inverse combs concatenates them**: `m(combInvColours xs, combInvColours ys) ≈
combInvColours (insertMany xs ys)`.  Same shape as `combPosConcatColours`. -/
theorem combInvConcatColours (xs ys : List Nat) :
    ColourAbelianGroupTreeConv (ColourAbelianTree.mulOp (combInvColours xs) (combInvColours ys))
      (combInvColours (insertMany xs ys)) := by
  induction xs with
  | nil => exact ColourAbelianGroupTreeConv.unitLeft (combInvColours ys)
  | cons head tail ih =>
    exact
      (ColourAbelianGroupTreeConv.assoc (ColourAbelianTree.invOp (ColourAbelianTree.leaf head))
          (combInvColours tail) (combInvColours ys)).trans
        ((ColourAbelianGroupTreeConv.mulCongr
            (ColourAbelianGroupTreeConv.refl (ColourAbelianTree.invOp (ColourAbelianTree.leaf head))) ih).trans
          (ColourAbelianGroupTreeConv.symm (combInvInsertSorted head (insertMany tail ys))))

/-- **Colour pair-form merge** — a product of two colour pair-forms is a single colour pair-form with merged
lists: `m(pairFormColours p₁ n₁, pairFormColours p₂ n₂) ≈ pairFormColours (insertMany p₁ p₂) (insertMany n₁ n₂)`.
The `convMiddleFourColours` shuffle gathers the two positive combs and the two inverse combs, then
`combPosConcatColours` / `combInvConcatColours` merge each side. -/
theorem pairFormMergeColours (posOne invOne posTwo invTwo : List Nat) :
    ColourAbelianGroupTreeConv
      (ColourAbelianTree.mulOp (pairFormColours posOne invOne) (pairFormColours posTwo invTwo))
      (pairFormColours (insertMany posOne posTwo) (insertMany invOne invTwo)) :=
  (convMiddleFourColours (combPosColours posOne) (combInvColours invOne)
      (combPosColours posTwo) (combInvColours invTwo)).trans
    (ColourAbelianGroupTreeConv.mulCongr (combPosConcatColours posOne posTwo)
      (combInvConcatColours invOne invTwo))

/-- Pushing an inverse through a positive comb yields the inverse comb: `i(combPosColours xs) ≈
combInvColours xs`.  Induction on `xs` via `invHom` / `invUnit`. -/
theorem invCombPosColours (xs : List Nat) :
    ColourAbelianGroupTreeConv (ColourAbelianTree.invOp (combPosColours xs)) (combInvColours xs) := by
  induction xs with
  | nil => exact ColourAbelianGroupTreeConv.invUnit
  | cons head tail ih =>
    exact (ColourAbelianGroupTreeConv.invHom (ColourAbelianTree.leaf head) (combPosColours tail)).trans
      (ColourAbelianGroupTreeConv.mulCongr
        (ColourAbelianGroupTreeConv.refl (ColourAbelianTree.invOp (ColourAbelianTree.leaf head))) ih)

/-- Pushing an inverse through an inverse comb yields the positive comb: `i(combInvColours xs) ≈
combPosColours xs`.  Induction on `xs` via `invHom` / `invInvol` / `invUnit`. -/
theorem invCombInvColours (xs : List Nat) :
    ColourAbelianGroupTreeConv (ColourAbelianTree.invOp (combInvColours xs)) (combPosColours xs) := by
  induction xs with
  | nil => exact ColourAbelianGroupTreeConv.invUnit
  | cons head tail ih =>
    exact (ColourAbelianGroupTreeConv.invHom (ColourAbelianTree.invOp (ColourAbelianTree.leaf head))
            (combInvColours tail)).trans
      (ColourAbelianGroupTreeConv.mulCongr (ColourAbelianGroupTreeConv.invInvol (ColourAbelianTree.leaf head))
        ih)

/-- **Inverting a colour pair-form swaps its lists**: `i(pairFormColours pos inv) ≈ pairFormColours inv pos`.
Distribute the inverse (`invHom`), turn each comb into the other kind, and swap sides (`commSwap`). -/
theorem invPairFormColoursSwap (pos inv : List Nat) :
    ColourAbelianGroupTreeConv (ColourAbelianTree.invOp (pairFormColours pos inv))
      (pairFormColours inv pos) :=
  (ColourAbelianGroupTreeConv.invHom (combPosColours pos) (combInvColours inv)).trans
    ((ColourAbelianGroupTreeConv.mulCongr (invCombPosColours pos) (invCombInvColours inv)).trans
      (ColourAbelianGroupTreeConv.commSwap (combInvColours pos) (combPosColours inv)))

/-- ★ **Normalization** — every tree is convertible to the colour pair-form of its own winding vector.
Induction on the tree: `leaf` / `unitOp` reduce to `pairFormColours [c] []` / `pairFormColours [] []`; `invOp`
inverts the child's pair-form and swaps its lists (`invPairFormColoursSwap`); `mulOp` normalizes both children
and merges (`pairFormMergeColours`). -/
theorem toPairFormColoursConv (tree : ColourAbelianTree) :
    ColourAbelianGroupTreeConv tree (pairFormColours (posColoursOf tree) (invColoursOf tree)) := by
  induction tree with
  | leaf colour =>
    exact ((ColourAbelianGroupTreeConv.unitRight (ColourAbelianTree.leaf colour)).symm).trans
      (ColourAbelianGroupTreeConv.unitRight
        (ColourAbelianTree.mulOp (ColourAbelianTree.leaf colour) ColourAbelianTree.unitOp)).symm
  | unitOp => exact (ColourAbelianGroupTreeConv.unitLeft ColourAbelianTree.unitOp).symm
  | invOp inner ih =>
    exact (ColourAbelianGroupTreeConv.invCongr ih).trans
      (invPairFormColoursSwap (posColoursOf inner) (invColoursOf inner))
  | mulOp left right ihLeft ihRight =>
    exact (ColourAbelianGroupTreeConv.mulCongr ihLeft ihRight).trans
      (pairFormMergeColours (posColoursOf left) (invColoursOf left)
        (posColoursOf right) (invColoursOf right))

/-! ## The pump and completeness -/

/-- **The pump** — a colour pair-form gains a cancelling positive/inverse slot pair:
`pairFormColours pos inv ≈ pairFormColours (insertSorted c pos) (insertSorted c inv)`.  Read backwards: the
extra `leaf c` and `i(leaf c)` shuffle together (`convMiddleFourColours`), cancel (`invRight`), and the
leftover unit is absorbed (`unitLeft`). -/
theorem pairFormColoursPump (pos inv : List Nat) (colour : Nat) :
    ColourAbelianGroupTreeConv (pairFormColours pos inv)
      (pairFormColours (insertSorted colour pos) (insertSorted colour inv)) :=
  ((ColourAbelianGroupTreeConv.mulCongr (combPosInsertSorted colour pos)
        (combInvInsertSorted colour inv)).trans
      ((convMiddleFourColours (ColourAbelianTree.leaf colour) (combPosColours pos)
          (ColourAbelianTree.invOp (ColourAbelianTree.leaf colour)) (combInvColours inv)).trans
        ((ColourAbelianGroupTreeConv.mulCongr
            (ColourAbelianGroupTreeConv.invRight (ColourAbelianTree.leaf colour))
            (ColourAbelianGroupTreeConv.refl
              (ColourAbelianTree.mulOp (combPosColours pos) (combInvColours inv)))).trans
          (ColourAbelianGroupTreeConv.unitLeft
            (ColourAbelianTree.mulOp (combPosColours pos) (combInvColours inv)))))).symm

/-- **Iterated pump** — `pairFormColours pos inv ≈ pairFormColours (insertMany extra pos) (insertMany extra
inv)`, pumping by a whole colour list.  Induction on `extra` using `pairFormColoursPump`. -/
theorem pairFormColoursPumpMany (pos inv extra : List Nat) :
    ColourAbelianGroupTreeConv (pairFormColours pos inv)
      (pairFormColours (insertMany extra pos) (insertMany extra inv)) := by
  induction extra with
  | nil => exact ColourAbelianGroupTreeConv.refl (pairFormColours pos inv)
  | cons head tail ih =>
    exact ih.trans (pairFormColoursPump (insertMany tail pos) (insertMany tail inv) head)

/-- **Colour pair-forms with equal cross-add are convertible** — pump each up by the other's inverse list to a
common colour pair-form, then join.  The hypothesis `insertMany posOne invTwo = insertMany posTwo invOne` is
exactly `multisetWindingEquiv` of the two vectors; the four sorted-fixedness hypotheses let the block
commutations move each cross-sum around.  Mirrors the single generator's `pairFormEquivConv`. -/
theorem pairFormColoursEquivConv (posOne invOne posTwo invTwo : List Nat)
    (fixPosOne : insertMany posOne [] = posOne) (fixInvOne : insertMany invOne [] = invOne)
    (fixPosTwo : insertMany posTwo [] = posTwo) (fixInvTwo : insertMany invTwo [] = invTwo)
    (windingHyp : insertMany posOne invTwo = insertMany posTwo invOne) :
    ColourAbelianGroupTreeConv (pairFormColours posOne invOne) (pairFormColours posTwo invTwo) :=
  let pumpedOne := pairFormColoursPumpMany posOne invOne invTwo
  let pumpedTwo := pairFormColoursPumpMany posTwo invTwo invOne
  let posEq : insertMany invTwo posOne = insertMany invOne posTwo :=
    ((insertManyBlockComm posOne invTwo fixPosOne fixInvTwo).symm.trans windingHyp).trans
      (insertManyBlockComm posTwo invOne fixPosTwo fixInvOne)
  let invEq : insertMany invTwo invOne = insertMany invOne invTwo :=
    insertManyBlockComm invTwo invOne fixInvTwo fixInvOne
  let treeEq : pairFormColours (insertMany invTwo posOne) (insertMany invTwo invOne)
      = pairFormColours (insertMany invOne posTwo) (insertMany invOne invTwo) :=
    (congrArg (fun p => pairFormColours p (insertMany invTwo invOne)) posEq).trans
      (congrArg (fun n => pairFormColours (insertMany invOne posTwo) n) invEq)
  pumpedOne.trans ((convOfTreeEqColours treeEq).trans (ColourAbelianGroupTreeConv.symm pumpedTwo))

/-- ★ **Completeness** — winding-equivalent trees are convertible.  Both trees normalize to the colour
pair-form of their winding vector, and equal-cross-add pair-forms are convertible
(`pairFormColoursEquivConv`, fed the sorted-fixedness of each tree's colour-lists), so they meet. -/
theorem colourAbelianGroupTreeConv_complete {source target : ColourAbelianTree}
    (windingHyp : multisetWindingEquiv source target) :
    ColourAbelianGroupTreeConv source target :=
  (toPairFormColoursConv source).trans
    ((pairFormColoursEquivConv (posColoursOf source) (invColoursOf source)
        (posColoursOf target) (invColoursOf target)
        (windingColoursSortedFixed source).1 (windingColoursSortedFixed source).2
        (windingColoursSortedFixed target).1 (windingColoursSortedFixed target).2
        windingHyp).trans
      (ColourAbelianGroupTreeConv.symm (toPairFormColoursConv target)))

/-! ## The decision -/

/-- ★ **The decision** — convertibility in the walking abelian group on an arbitrary alphabet is exactly the
cross-added multiset winding equivalence.  Since `multisetWindingEquiv` is a `List Nat` equality (decidable via
structural `DecidableEq`), this biconditional decides the word problem. -/
theorem colourAbelianGroupTreeConv_iff_windingEquiv (source target : ColourAbelianTree) :
    ColourAbelianGroupTreeConv source target ↔ multisetWindingEquiv source target :=
  ⟨colourAbelianGroupTreeConv_sound, colourAbelianGroupTreeConv_complete⟩

/-- ★ **The decider** — a shipped `Decidable` for the arbitrary-alphabet convertibility, built from the
winding-vector decision: match the derived `DecidableEq (List Nat)` on the two cross-added multisets,
discharging `isTrue` by completeness and `isFalse` by soundness.  A genuine decider (not `decidable_of_iff`),
propext-free. -/
def decideColourAbelianGroupTreeConv (source target : ColourAbelianTree) :
    Decidable (ColourAbelianGroupTreeConv source target) :=
  match (inferInstance : Decidable
      (insertMany (posColoursOf source) (invColoursOf target)
        = insertMany (posColoursOf target) (invColoursOf source))) with
  | isTrue equiv => isTrue (colourAbelianGroupTreeConv_complete equiv)
  | isFalse notEquiv => isFalse (fun conv => notEquiv (colourAbelianGroupTreeConv_sound conv))

/-- The arbitrary-alphabet convertibility as a `Decidable` INSTANCE, so the `decide` tactic and instance
resolution fire on it.  A definitional alias of the shipped decider, hence propext-free. -/
instance instDecidableColourAbelianGroupTreeConv (source target : ColourAbelianTree) :
    Decidable (ColourAbelianGroupTreeConv source target) :=
  decideColourAbelianGroupTreeConv source target

/-! ## Groundings -/

/-- ★ **The decision in action (positive, per-colour cancellation)** — a cancelling insertion
`m(m(leaf 0, i leaf 0), leaf 1)` is convertible to `leaf 1`: both wind to the vector `+1` on colour `1`, so
they meet through completeness with no explicit rewrite path — the inverse-cancellation the multiset
commutative-monoid walker cannot see. -/
theorem colourAbelianGroupCancellationHolds :
    ColourAbelianGroupTreeConv
      (ColourAbelianTree.mulOp
        (ColourAbelianTree.mulOp (ColourAbelianTree.leaf 0)
          (ColourAbelianTree.invOp (ColourAbelianTree.leaf 0)))
        (ColourAbelianTree.leaf 1))
      (ColourAbelianTree.leaf 1) :=
  colourAbelianGroupTreeConv_complete rfl

/-- ★ **The decision in action (positive, cross-colour reorder)** — two differently-ordered two-colour trees
with the same winding vector are convertible, decided by their equal cross-added multiset through completeness
— no explicit rewrite path supplied. -/
theorem colourAbelianGroupReordersColours :
    ColourAbelianGroupTreeConv
      (ColourAbelianTree.mulOp (ColourAbelianTree.leaf 0) (ColourAbelianTree.leaf 1))
      (ColourAbelianTree.mulOp (ColourAbelianTree.leaf 1) (ColourAbelianTree.leaf 0)) :=
  colourAbelianGroupTreeConv_complete rfl

/-- ★ **The inverse does real work** — `i(m(leaf 0, leaf 1)) ≈ m(i leaf 0, i leaf 1)`: the inverse distributes
over a product (valid precisely because the group is abelian).  Both wind to `-1` on colours `0` and `1`. -/
theorem colourAbelianGroupInverseDistributes :
    ColourAbelianGroupTreeConv
      (ColourAbelianTree.invOp (ColourAbelianTree.mulOp (ColourAbelianTree.leaf 0) (ColourAbelianTree.leaf 1)))
      (ColourAbelianTree.mulOp (ColourAbelianTree.invOp (ColourAbelianTree.leaf 0))
        (ColourAbelianTree.invOp (ColourAbelianTree.leaf 1))) :=
  ColourAbelianGroupTreeConv.invHom (ColourAbelianTree.leaf 0) (ColourAbelianTree.leaf 1)

/-- ★ **The decision in action (negative)** — a slot of colour `0` is NOT convertible to a slot of colour `1`:
their winding vectors differ (`[0] ≠ [1]` on the positive component), so by soundness no convertibility can
exist.  `Nat.noConfusion`. -/
theorem colourAbelianGroupRejectsDistinctColours :
    ¬ ColourAbelianGroupTreeConv (ColourAbelianTree.leaf 0) (ColourAbelianTree.leaf 1) := by
  intro conv
  have equiv : ([0] : List Nat) = ([1] : List Nat) := colourAbelianGroupTreeConv_sound conv
  injection equiv with headEq _
  exact Nat.noConfusion headEq

/-! ## The marker -/

/-- ★ **The walking abelian group on an ARBITRARY alphabet is DECIDED** — the ℤᵏ winding-vector decision.
`= true` records that `colourAbelianGroupTreeConv_iff_windingEquiv` reduces the alphabet-parameterised word
problem to the CROSS-ADDED multiset equivalence `insertMany posSource invTarget = insertMany posTarget
invSource` — adjoining a formal inverse completes each per-colour count of the free commutative monoid to the
integers, presenting the free abelian group on `ℕ` as `ℤᵏ` (the free ℤ-module) with no signed type and no
subtraction, the single generator's `p₁ + n₂ = p₂ + n₁` lifted to sorted colour-lists.  Soundness (every law
preserves the cross-added multiset, via the `deleteFirst` cancellation kit and the sorted-fixed block algebra),
normalization to the colour pair-form, and completeness are all shipped, plus a genuine `Decidable`.  This
CLOSES the ℤᵏ successor wall named by `AbelianGroupSeed`.  All zero-axiom: the ordering is the imported
structural `natBle` (no `Nat.le`/`Nat.ble` lemma), no `Int`, no `Nat.sub`, and no `List.append` (`++`). -/
def fxWalkingAbelianGroup_hasColourVectorDecision : Bool := true

end FX1Poly.Polygraph
