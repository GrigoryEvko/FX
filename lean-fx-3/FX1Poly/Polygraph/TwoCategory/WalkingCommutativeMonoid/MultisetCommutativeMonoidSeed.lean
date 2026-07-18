/-! # WalkingCommutativeMonoid/MultisetCommutativeMonoidSeed — the walking commutative monoid on an ARBITRARY alphabet: the finite-multiset decision

The successor rung explicitly named as the honest wall in both the single-generator sibling
(`CommutativeMonoidSeed`, invariant a single leaf count) and the two-colour sibling
(`TwoColourCommutativeMonoidSeed`, invariant a fixed pair of counts / a Parikh vector).  The free
**commutative** monoid on the colour set `ℕ` is not `ℕ` nor a fixed tuple `ℕ^k` but the finite
MULTISETS of colours — a tree's class in the free commutative monoid is determined by the multiset of its
colour-slots.  Because that multiset is a COMPLETE invariant, and a multiset over `ℕ` has a canonical
representative as a SORTED list (insertion-sort normal form), the word problem is decided by plain equality
of sorted-colour lists.

## ★ Why this walker is FULLY DECIDED (arbitrary alphabet)

The fixed-arity siblings reduced the word problem to a fixed tuple of `Nat` counts.  Here the alphabet is all
of `ℕ`, so the invariant is a whole finite multiset, held as its sorted-list normal form `sortedColoursOf`
(insertion sort over the purpose-built structural `natBle`).  The crux is that `insertSorted` COMMUTES
(`insertSortedComm`) — insertion order is irrelevant — which is exactly permutation-invariance of the sorted
multiset.  This file ships:

* **soundness** — convertible trees have equal sorted-colour list (`multisetCommMonoidConv_sound`), the sorted
  multiset being a complete invariant that every commutative-monoid law preserves;
* **normalization** — every tree reduces to the right-comb of its sorted-colour list
  (`multisetTreeReducesToComb`), grafting via `combMergeColourLists`;
* **completeness** — equal sorted-colour list ⟹ convertible (`multisetCommMonoidConv_complete`);
* **the decision** — the convertibility ⟺ `List Nat`-equality biconditional
  (`multisetCommMonoidConv_iff_sortedColours`) plus a shipped `Decidable`.

This CLOSES the successor wall that the single-generator and two-colour commutative-monoid seeds named.

Raw Lean 4 + Init; the convertibility is an inductive `Prop`; per-declaration `#assert_no_axioms` gated in the
audit twin.  Free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega` — the ordering is
the purpose-built structural `natBle` (no `Nat.le`/`Nat.ble` lemma), and no `List.append` (`++`) appears
anywhere (it leaks `propext`); the multiset normal form is built with `insertSorted` / `insertMany`. -/

namespace FX1Poly.Polygraph

/-! ## Zero-axiom sorted-list kit -/

/-- Structural Boolean `≤` on `Nat` — a purpose-built comparison avoiding every propext-leaky `Nat.ble`/`Nat.le`
library lemma.  `natBle 0 _ = true`, `natBle (succ _) 0 = false`, `natBle (succ a) (succ b) = natBle a b`. -/
def natBle : Nat → Nat → Bool
  | 0, _ => true
  | Nat.succ _, 0 => false
  | Nat.succ first, Nat.succ second => natBle first second

/-- **Totality of `natBle`** — if `natBle first second` fails then `natBle second first` holds (the order is
total).  Structural recursion on `first` with a case on `second`. -/
theorem natBleTotal : (first second : Nat) → natBle first second = false → natBle second first = true
  | 0, _, hfalse => Bool.noConfusion hfalse
  | Nat.succ _, 0, _ => rfl
  | Nat.succ firstPredecessor, Nat.succ secondPredecessor, hfalse =>
      natBleTotal firstPredecessor secondPredecessor hfalse

/-- **Transitivity of `natBle`** — `natBle first second` and `natBle second third` give `natBle first third`.
Structural recursion on all three arguments; the impossible corners fall to `Bool.noConfusion`. -/
theorem natBleTrans : (first second third : Nat) →
    natBle first second = true → natBle second third = true → natBle first third = true
  | 0, _, _, _, _ => rfl
  | Nat.succ _, 0, _, hab, _ => Bool.noConfusion hab
  | Nat.succ _, Nat.succ _, 0, _, hbc => Bool.noConfusion hbc
  | Nat.succ firstPredecessor, Nat.succ secondPredecessor, Nat.succ thirdPredecessor, hab, hbc =>
      natBleTrans firstPredecessor secondPredecessor thirdPredecessor hab hbc

/-- **Antisymmetry of `natBle`** — `natBle first second` and `natBle second first` force `first = second`.
Structural recursion on both arguments; the mixed corners fall to `Bool.noConfusion`. -/
theorem natBleAntisymm : (first second : Nat) →
    natBle first second = true → natBle second first = true → first = second
  | 0, 0, _, _ => rfl
  | 0, Nat.succ _, _, hba => Bool.noConfusion hba
  | Nat.succ _, 0, hab, _ => Bool.noConfusion hab
  | Nat.succ firstPredecessor, Nat.succ secondPredecessor, hab, hba =>
      congrArg Nat.succ (natBleAntisymm firstPredecessor secondPredecessor hab hba)

/-- **Insertion of one colour into a sorted list**, keeping it sorted: place `value` before the first element
it does not exceed. -/
def insertSorted (value : Nat) : List Nat → List Nat
  | [] => [value]
  | head :: tail =>
      match natBle value head with
      | true => value :: head :: tail
      | false => head :: insertSorted value tail

/-- Equation: inserting into the empty list yields the singleton. -/
theorem insertSortedNilEq (value : Nat) : insertSorted value [] = [value] := rfl

/-- Equation: when `value` does not exceed `head`, it is placed at the front. -/
theorem insertSortedConsTrue (value head : Nat) (tail : List Nat)
    (hle : natBle value head = true) :
    insertSorted value (head :: tail) = value :: head :: tail := by
  show (match natBle value head with
        | true => value :: head :: tail
        | false => head :: insertSorted value tail) = value :: head :: tail
  rw [hle]

/-- Equation: when `value` exceeds `head`, `head` stays and the insertion recurses into the tail. -/
theorem insertSortedConsFalse (value head : Nat) (tail : List Nat)
    (hgt : natBle value head = false) :
    insertSorted value (head :: tail) = head :: insertSorted value tail := by
  show (match natBle value head with
        | true => value :: head :: tail
        | false => head :: insertSorted value tail) = head :: insertSorted value tail
  rw [hgt]

/-- **Insert every element of the first list into the accumulator**, one at a time. -/
def insertMany : List Nat → List Nat → List Nat
  | [], acc => acc
  | head :: tail, acc => insertSorted head (insertMany tail acc)

/-- ★ **`insertSorted` commutes** — the order of two insertions is irrelevant.  This is the heart of the
multiset decision: it is exactly permutation-invariance of the sorted normal form.  Structural induction on the
list; each cons splits on `natBle value head` for both inserted values, using `natBleTotal` to rule out the
double-`false` corner, `natBleTrans` to rule out the order-crossing corners, and `natBleAntisymm` to collapse
the equal-value corner. -/
theorem insertSortedComm (valueA valueB : Nat) (xs : List Nat) :
    insertSorted valueA (insertSorted valueB xs) = insertSorted valueB (insertSorted valueA xs) := by
  induction xs with
  | nil =>
    rw [insertSortedNilEq valueB, insertSortedNilEq valueA]
    cases hAB : natBle valueA valueB with
    | true =>
      rw [insertSortedConsTrue valueA valueB [] hAB]
      cases hBA : natBle valueB valueA with
      | true =>
        rw [insertSortedConsTrue valueB valueA [] hBA]
        have hEq : valueA = valueB := natBleAntisymm valueA valueB hAB hBA
        rw [hEq]
      | false =>
        rw [insertSortedConsFalse valueB valueA [] hBA, insertSortedNilEq valueB]
    | false =>
      rw [insertSortedConsFalse valueA valueB [] hAB, insertSortedNilEq valueA]
      have hBA : natBle valueB valueA = true := natBleTotal valueA valueB hAB
      rw [insertSortedConsTrue valueB valueA [] hBA]
  | cons head tail ih =>
    cases hAH : natBle valueA head with
    | true =>
      cases hBH : natBle valueB head with
      | true =>
        rw [insertSortedConsTrue valueB head tail hBH, insertSortedConsTrue valueA head tail hAH]
        cases hAB : natBle valueA valueB with
        | true =>
          rw [insertSortedConsTrue valueA valueB (head :: tail) hAB]
          cases hBA : natBle valueB valueA with
          | true =>
            rw [insertSortedConsTrue valueB valueA (head :: tail) hBA]
            have hEq : valueA = valueB := natBleAntisymm valueA valueB hAB hBA
            rw [hEq]
          | false =>
            rw [insertSortedConsFalse valueB valueA (head :: tail) hBA,
                insertSortedConsTrue valueB head tail hBH]
        | false =>
          rw [insertSortedConsFalse valueA valueB (head :: tail) hAB,
              insertSortedConsTrue valueA head tail hAH]
          have hBA : natBle valueB valueA = true := natBleTotal valueA valueB hAB
          rw [insertSortedConsTrue valueB valueA (head :: tail) hBA]
      | false =>
        rw [insertSortedConsFalse valueB head tail hBH, insertSortedConsTrue valueA head tail hAH,
            insertSortedConsTrue valueA head (insertSorted valueB tail) hAH]
        cases hBA : natBle valueB valueA with
        | true =>
          exact Bool.noConfusion ((natBleTrans valueB valueA head hBA hAH).symm.trans hBH)
        | false =>
          rw [insertSortedConsFalse valueB valueA (head :: tail) hBA,
              insertSortedConsFalse valueB head tail hBH]
    | false =>
      cases hBH : natBle valueB head with
      | true =>
        rw [insertSortedConsTrue valueB head tail hBH, insertSortedConsFalse valueA head tail hAH,
            insertSortedConsTrue valueB head (insertSorted valueA tail) hBH]
        cases hAB : natBle valueA valueB with
        | true =>
          exact Bool.noConfusion ((natBleTrans valueA valueB head hAB hBH).symm.trans hAH)
        | false =>
          rw [insertSortedConsFalse valueA valueB (head :: tail) hAB,
              insertSortedConsFalse valueA head tail hAH]
      | false =>
        rw [insertSortedConsFalse valueB head tail hBH, insertSortedConsFalse valueA head tail hAH,
            insertSortedConsFalse valueA head (insertSorted valueB tail) hAH,
            insertSortedConsFalse valueB head (insertSorted valueA tail) hBH]
        exact congrArg (fun rest => head :: rest) ih

/-- Pushing an `insertSorted` through an `insertMany` moves it onto the accumulator (the inserted colours all
commute past `value`, by `insertSortedComm`). -/
theorem insertSortedInsertMany (value : Nat) (xs acc : List Nat) :
    insertSorted value (insertMany xs acc) = insertMany xs (insertSorted value acc) := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
    show insertSorted value (insertSorted head (insertMany tail acc))
      = insertSorted head (insertMany tail (insertSorted value acc))
    rw [insertSortedComm value head (insertMany tail acc), ih]

/-- Pulling an `insertSorted` out of the head list of an `insertMany` (the mirror of
`insertSortedInsertMany`). -/
theorem insertManyInsertSorted (value : Nat) (xs acc : List Nat) :
    insertMany (insertSorted value xs) acc = insertSorted value (insertMany xs acc) := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
    cases h : natBle value head with
    | true =>
      rw [insertSortedConsTrue value head tail h]
      rfl
    | false =>
      rw [insertSortedConsFalse value head tail h]
      show insertSorted head (insertMany (insertSorted value tail) acc)
        = insertSorted value (insertMany (head :: tail) acc)
      rw [ih]
      show insertSorted head (insertSorted value (insertMany tail acc))
        = insertSorted value (insertSorted head (insertMany tail acc))
      rw [insertSortedComm head value (insertMany tail acc)]

/-- **`insertMany` is associative** in the fold order — `insertMany (insertMany xs ys) acc` collapses to
`insertMany xs (insertMany ys acc)`. -/
theorem insertManyAssoc (xs ys acc : List Nat) :
    insertMany (insertMany xs ys) acc = insertMany xs (insertMany ys acc) := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
    show insertMany (insertSorted head (insertMany tail ys)) acc
      = insertSorted head (insertMany tail (insertMany ys acc))
    rw [insertManyInsertSorted head (insertMany tail ys) acc, ih]

/-- **`insertMany` commutes** over its two list arguments (into a common accumulator) — the multiset-level
permutation-invariance, lifted from `insertSortedComm` through `insertSortedInsertMany`. -/
theorem insertManyComm (xs ys acc : List Nat) :
    insertMany xs (insertMany ys acc) = insertMany ys (insertMany xs acc) := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
    show insertSorted head (insertMany tail (insertMany ys acc))
      = insertMany ys (insertSorted head (insertMany tail acc))
    rw [ih, insertSortedInsertMany head ys (insertMany tail acc)]

/-! ## The carrier and the tree-insert invariant -/

/-- ★ The **tree carrier** of the walking commutative monoid on an arbitrary alphabet: an un-indexed planar
tree over colour-indexed generator slots plus the `{m, e}` monoid signature.  `leaf colour` is an arity-1 input
slot tagged with a colour in `ℕ`; `unitOp` is the nullary generator `e`; `mulOp` grafts two subtrees under the
binary generator `m`.  A closed tree's MULTISET of colour-slots (as a sorted list) is its complete
convertibility invariant. -/
inductive ColourTree where
  /-- An arity-1 input slot tagged with a colour in `ℕ` — a generator of the chosen alphabet. -/
  | leaf (colour : Nat)
  /-- The nullary generator `e : arity 0` (the monoid unit). -/
  | unitOp
  /-- The binary generator `m : arity 2` grafting the left and right subtrees (`m(left, right)`). -/
  | mulOp : ColourTree → ColourTree → ColourTree

/-- **Insert a tree's colour-slots into an accumulator**, sorted: a `leaf` inserts its colour, `unitOp`
contributes nothing, and `mulOp` inserts the right subtree then the left. -/
def insertTree : ColourTree → List Nat → List Nat
  | .leaf colour, acc => insertSorted colour acc
  | .unitOp, acc => acc
  | .mulOp left right, acc => insertTree left (insertTree right acc)

/-- The **sorted-colour list** of a tree — its multiset of colour-slots in insertion-sort normal form.  The
complete convertibility invariant of the free commutative monoid on `ℕ`. -/
def sortedColoursOf (tree : ColourTree) : List Nat := insertTree tree []

/-- Smoke: a single colour-slot yields its singleton. -/
theorem sortedColoursOf_leaf : sortedColoursOf (ColourTree.leaf 2) = [2] := rfl

/-- Smoke: a two-colour graft sorts its colours. -/
theorem sortedColoursOf_mulSorts :
    sortedColoursOf (ColourTree.mulOp (ColourTree.leaf 3) (ColourTree.leaf 1)) = [1, 3] := rfl

/-- Smoke: three colours in a skewed tree come out sorted. -/
theorem sortedColoursOf_threeSorts :
    sortedColoursOf (ColourTree.mulOp
      (ColourTree.mulOp (ColourTree.leaf 2) (ColourTree.leaf 0)) (ColourTree.leaf 1)) = [0, 1, 2] := rfl

/-- **`insertTree` spreads as an `insertMany` of the tree's sorted colours** onto the accumulator.  Structural
induction on the tree (generalizing the accumulator); the `mulOp` case decomposes the merged colours via the
subtree hypotheses and re-associates with `insertManyAssoc`. -/
theorem insertTreeSpread (tree : ColourTree) (acc : List Nat) :
    insertTree tree acc = insertMany (sortedColoursOf tree) acc := by
  induction tree generalizing acc with
  | leaf colour => rfl
  | unitOp => rfl
  | mulOp left right ihLeft ihRight =>
    show insertTree left (insertTree right acc)
      = insertMany (sortedColoursOf (ColourTree.mulOp left right)) acc
    rw [ihLeft (insertTree right acc), ihRight acc]
    have hMul : sortedColoursOf (ColourTree.mulOp left right)
        = insertMany (sortedColoursOf left) (sortedColoursOf right) := by
      show insertTree left (insertTree right [])
        = insertMany (sortedColoursOf left) (sortedColoursOf right)
      rw [ihLeft (insertTree right [])]
      rfl
    rw [hMul, insertManyAssoc (sortedColoursOf left) (sortedColoursOf right) acc]

/-- **The colours of a graft merge the colours of the children** — `sortedColoursOf (mulOp left right)` is the
`insertMany` of the two children's sorted-colour lists.  A one-line corollary of `insertTreeSpread`. -/
theorem sortedColoursOfMul (left right : ColourTree) :
    sortedColoursOf (ColourTree.mulOp left right)
      = insertMany (sortedColoursOf left) (sortedColoursOf right) := by
  show insertTree left (insertTree right []) = insertMany (sortedColoursOf left) (sortedColoursOf right)
  rw [insertTreeSpread left (insertTree right [])]
  rfl

/-- Folding a tree's sorted colours into the empty accumulator recovers the sorted colours (the accumulator
starts empty in `sortedColoursOf`).  A definitional corollary of `insertTreeSpread` at `acc = []`. -/
theorem insertManySortedColoursNil (tree : ColourTree) :
    insertMany (sortedColoursOf tree) [] = sortedColoursOf tree :=
  (insertTreeSpread tree []).symm

/-! ## The commutative-monoid tree-pasting convertibility -/

/-- ★ The **tree-pasting convertibility** of the walking commutative monoid on an arbitrary alphabet — the
free-operad convertibility of the `{m, e}` signature over the colour-tagged generators closed under the four
commutative-monoid laws (associativity, left unit, right unit, and **commutativity**), the full tree-congruence
`mulCongr`, and `refl` / `symm` / `trans`.  Same shapes as the fixed-arity siblings over the colour-tagged
carrier.  Two trees denote the same element of the free commutative monoid on `ℕ` exactly when they are
`MultisetCommMonoidTreeConv`-related. -/
inductive MultisetCommMonoidTreeConv : ColourTree → ColourTree → Prop where
  /-- **Associativity** `m(m(left, middle), right) ≈ m(left, m(middle, right))`. -/
  | assoc (left middle right : ColourTree) :
      MultisetCommMonoidTreeConv
        (ColourTree.mulOp (ColourTree.mulOp left middle) right)
        (ColourTree.mulOp left (ColourTree.mulOp middle right))
  /-- **Left unit** `m(unitOp, subtree) ≈ subtree`. -/
  | unitLeft (subtree : ColourTree) :
      MultisetCommMonoidTreeConv (ColourTree.mulOp ColourTree.unitOp subtree) subtree
  /-- **Right unit** `m(subtree, unitOp) ≈ subtree`. -/
  | unitRight (subtree : ColourTree) :
      MultisetCommMonoidTreeConv (ColourTree.mulOp subtree ColourTree.unitOp) subtree
  /-- **Commutativity** `m(left, right) ≈ m(right, left)` — mixing colours freely. -/
  | commSwap (left right : ColourTree) :
      MultisetCommMonoidTreeConv (ColourTree.mulOp left right) (ColourTree.mulOp right left)
  /-- **Congruence under a grafting node** — into BOTH children. -/
  | mulCongr {leftOld leftNew rightOld rightNew : ColourTree} :
      MultisetCommMonoidTreeConv leftOld leftNew → MultisetCommMonoidTreeConv rightOld rightNew →
      MultisetCommMonoidTreeConv (ColourTree.mulOp leftOld rightOld) (ColourTree.mulOp leftNew rightNew)
  /-- Reflexivity. -/
  | refl (tree : ColourTree) : MultisetCommMonoidTreeConv tree tree
  /-- Symmetry. -/
  | symm {tree1 tree2 : ColourTree} :
      MultisetCommMonoidTreeConv tree1 tree2 → MultisetCommMonoidTreeConv tree2 tree1
  /-- Transitivity. -/
  | trans {tree1 tree2 tree3 : ColourTree} :
      MultisetCommMonoidTreeConv tree1 tree2 → MultisetCommMonoidTreeConv tree2 tree3 →
      MultisetCommMonoidTreeConv tree1 tree3

/-! ## Soundness: convertible ⟹ equal sorted-colour list -/

/-- ★ **Soundness** — convertible trees have equal sorted-colour list.  Each law preserves the sorted multiset:
associativity, left unit, and right unit are definitional (`insertTree` is a right-nested fold); commutativity
is `insertManyComm` (via `sortedColoursOfMul` and `insertManySortedColoursNil`); the congruence follows from
the inductive hypotheses through `sortedColoursOfMul`.  The sorted-colour list is a COMPLETE invariant. -/
theorem multisetCommMonoidConv_sound {source target : ColourTree}
    (conv : MultisetCommMonoidTreeConv source target) : sortedColoursOf source = sortedColoursOf target := by
  induction conv with
  | assoc left middle right => rfl
  | unitLeft subtree => rfl
  | unitRight subtree => rfl
  | commSwap left right =>
    rw [sortedColoursOfMul left right, sortedColoursOfMul right left]
    exact
      ((congrArg (insertMany (sortedColoursOf left)) (insertManySortedColoursNil right)).symm.trans
        (insertManyComm (sortedColoursOf left) (sortedColoursOf right) [])).trans
        (congrArg (insertMany (sortedColoursOf right)) (insertManySortedColoursNil left))
  | mulCongr _ _ ihLeft ihRight =>
    rw [sortedColoursOfMul, sortedColoursOfMul, ihLeft, ihRight]
  | refl tree => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ## Normalization: every tree reduces to the right-comb of its sorted colours -/

/-- The **right-comb of a colour list** — `combOfList [] = unitOp` and
`combOfList (colour :: rest) = m(leaf colour, combOfList rest)`, the canonical tree over a given colour
sequence.  Applied to a SORTED colour list it is the multiset normal form. -/
def combOfList : List Nat → ColourTree
  | [] => ColourTree.unitOp
  | colour :: rest => ColourTree.mulOp (ColourTree.leaf colour) (combOfList rest)

/-- **Inserting a colour into a sorted list is convertible to grafting it on the front** of the list's comb:
`combOfList (insertSorted colour xs) ≈ m(leaf colour, combOfList xs)`.  Induction on `xs`; the `false` cons
case bubbles the new colour past the head via `commSwap` sandwiched between the two associativities. -/
theorem combInsertSorted (colour : Nat) (xs : List Nat) :
    MultisetCommMonoidTreeConv (combOfList (insertSorted colour xs))
      (ColourTree.mulOp (ColourTree.leaf colour) (combOfList xs)) := by
  induction xs with
  | nil => exact MultisetCommMonoidTreeConv.refl _
  | cons head rest ih =>
    cases h : natBle colour head with
    | true =>
      rw [insertSortedConsTrue colour head rest h]
      exact MultisetCommMonoidTreeConv.refl _
    | false =>
      rw [insertSortedConsFalse colour head rest h]
      exact
        (MultisetCommMonoidTreeConv.mulCongr (MultisetCommMonoidTreeConv.refl (ColourTree.leaf head)) ih).trans
          ((MultisetCommMonoidTreeConv.symm
              (MultisetCommMonoidTreeConv.assoc (ColourTree.leaf head) (ColourTree.leaf colour)
                (combOfList rest))).trans
            ((MultisetCommMonoidTreeConv.mulCongr
                (MultisetCommMonoidTreeConv.commSwap (ColourTree.leaf head) (ColourTree.leaf colour))
                (MultisetCommMonoidTreeConv.refl (combOfList rest))).trans
              (MultisetCommMonoidTreeConv.assoc (ColourTree.leaf colour) (ColourTree.leaf head)
                (combOfList rest))))

/-- **Grafting two combs is convertible to the comb of the merged colour lists**:
`m(combOfList xs, combOfList ys) ≈ combOfList (insertMany xs ys)`.  Induction on `xs`; the cons case
re-associates the leading colour out, recurses, and re-absorbs it via `combInsertSorted`. -/
theorem combMergeColourLists (xs ys : List Nat) :
    MultisetCommMonoidTreeConv (ColourTree.mulOp (combOfList xs) (combOfList ys))
      (combOfList (insertMany xs ys)) := by
  induction xs with
  | nil => exact MultisetCommMonoidTreeConv.unitLeft (combOfList ys)
  | cons head tail ih =>
    exact
      (MultisetCommMonoidTreeConv.assoc (ColourTree.leaf head) (combOfList tail) (combOfList ys)).trans
        ((MultisetCommMonoidTreeConv.mulCongr (MultisetCommMonoidTreeConv.refl (ColourTree.leaf head)) ih).trans
          (MultisetCommMonoidTreeConv.symm (combInsertSorted head (insertMany tail ys))))

/-- ★ **Normalization** — every tree is convertible to the right-comb of its own sorted-colour list.  Induction
on the tree: `leaf` reduces via right unit, `unitOp` is already `combOfList []`, and `mulOp` normalizes the two
children (`mulCongr`) then grafts them with `combMergeColourLists`, transporting the merged colours back through
`sortedColoursOfMul`. -/
theorem multisetTreeReducesToComb (tree : ColourTree) :
    MultisetCommMonoidTreeConv tree (combOfList (sortedColoursOf tree)) := by
  induction tree with
  | leaf colour => exact MultisetCommMonoidTreeConv.symm (MultisetCommMonoidTreeConv.unitRight (ColourTree.leaf colour))
  | unitOp => exact MultisetCommMonoidTreeConv.refl ColourTree.unitOp
  | mulOp left right ihLeft ihRight =>
    have chain : MultisetCommMonoidTreeConv (ColourTree.mulOp left right)
        (combOfList (insertMany (sortedColoursOf left) (sortedColoursOf right))) :=
      (MultisetCommMonoidTreeConv.mulCongr ihLeft ihRight).trans
        (combMergeColourLists (sortedColoursOf left) (sortedColoursOf right))
    have treeEq : combOfList (insertMany (sortedColoursOf left) (sortedColoursOf right))
        = combOfList (sortedColoursOf (ColourTree.mulOp left right)) :=
      congrArg combOfList (sortedColoursOfMul left right).symm
    exact treeEq ▸ chain

/-! ## Completeness and the decision -/

/-- ★ **Completeness** — equal sorted-colour list implies convertibility.  Both trees normalize to the
right-comb of their (equal) sorted colours, so they are convertible through that common normal form. -/
theorem multisetCommMonoidConv_complete {source target : ColourTree}
    (coloursEq : sortedColoursOf source = sortedColoursOf target) :
    MultisetCommMonoidTreeConv source target := by
  have sourceReduces : MultisetCommMonoidTreeConv source (combOfList (sortedColoursOf source)) :=
    multisetTreeReducesToComb source
  have targetReduces : MultisetCommMonoidTreeConv target (combOfList (sortedColoursOf target)) :=
    multisetTreeReducesToComb target
  have combEq : combOfList (sortedColoursOf source) = combOfList (sortedColoursOf target) :=
    congrArg combOfList coloursEq
  exact MultisetCommMonoidTreeConv.trans sourceReduces
    (combEq.symm ▸ MultisetCommMonoidTreeConv.symm targetReduces)

/-- ★ **The decision** — convertibility in the walking commutative monoid on an arbitrary alphabet is exactly
equality of sorted-colour lists (the multisets of colour-slots coincide).  Since `List Nat` equality is
decidable (structural `DecidableEq`), this biconditional decides the word problem. -/
theorem multisetCommMonoidConv_iff_sortedColours (source target : ColourTree) :
    MultisetCommMonoidTreeConv source target ↔ sortedColoursOf source = sortedColoursOf target :=
  ⟨multisetCommMonoidConv_sound, multisetCommMonoidConv_complete⟩

/-- ★ **The decider** — a shipped `Decidable` for the arbitrary-alphabet convertibility, built from the
sorted-colour-list decision: match the derived `DecidableEq (List Nat)`, discharging `isTrue` by completeness
and `isFalse` by soundness.  A genuine decider (not `decidable_of_iff`), propext-free. -/
def decideMultisetCommMonoidTreeConv (source target : ColourTree) :
    Decidable (MultisetCommMonoidTreeConv source target) :=
  match (inferInstance : Decidable (sortedColoursOf source = sortedColoursOf target)) with
  | isTrue coloursEq => isTrue (multisetCommMonoidConv_complete coloursEq)
  | isFalse coloursNe => isFalse (fun conv => coloursNe (multisetCommMonoidConv_sound conv))

/-- The arbitrary-alphabet convertibility as a `Decidable` INSTANCE, so the `decide` tactic and instance
resolution fire on it — mirroring the fixed-arity siblings.  A definitional alias of the shipped
`decideMultisetCommMonoidTreeConv`, hence propext-free. -/
instance instDecidableMultisetCommMonoidTreeConv (source target : ColourTree) :
    Decidable (MultisetCommMonoidTreeConv source target) :=
  decideMultisetCommMonoidTreeConv source target

/-! ## Groundings -/

/-- ★ **The decision in action (positive, two colours)** — two differently-ordered two-colour trees with the
same multiset `{0, 1}` are convertible, decided purely by their equal sorted-colour list (`[0, 1] = [0, 1]`)
through the completeness leg — no explicit rewrite path supplied. -/
theorem multisetCommMonoidReordersTwoColours :
    MultisetCommMonoidTreeConv
      (ColourTree.mulOp (ColourTree.leaf 0) (ColourTree.leaf 1))
      (ColourTree.mulOp (ColourTree.leaf 1) (ColourTree.leaf 0)) :=
  multisetCommMonoidConv_complete rfl

/-- ★ **The decision in action (positive, three colours)** — two differently-shaped three-colour trees with the
same multiset `{0, 1, 2}` are convertible, decided by their equal sorted-colour list (`[0, 1, 2] = [0, 1, 2]`).
A genuinely multiset-level reordering across three distinct colours. -/
theorem multisetCommMonoidReordersThreeColours :
    MultisetCommMonoidTreeConv
      (ColourTree.mulOp (ColourTree.mulOp (ColourTree.leaf 2) (ColourTree.leaf 0)) (ColourTree.leaf 1))
      (ColourTree.mulOp (ColourTree.leaf 1) (ColourTree.mulOp (ColourTree.leaf 0) (ColourTree.leaf 2))) :=
  multisetCommMonoidConv_complete rfl

/-- ★ **The decision in action (negative, multiplicity matters)** — `m(leaf 0, leaf 0)` (multiset `{0, 0}`) is
NOT convertible to `leaf 0` (multiset `{0}`): the sorted-colour lists `[0, 0]` and `[0]` differ, so by
soundness no convertibility can exist.  `[0, 0] ≠ [0]` by structural `cases` on the equality (a two-element
list cannot equal a one-element list). -/
theorem multisetCommMonoidRejectsUnequalMultiset :
    ¬ MultisetCommMonoidTreeConv
        (ColourTree.mulOp (ColourTree.leaf 0) (ColourTree.leaf 0)) (ColourTree.leaf 0) := by
  intro conv
  have coloursEq : ([0, 0] : List Nat) = [0] := multisetCommMonoidConv_sound conv
  cases coloursEq

/-! ## The marker -/

/-- ★ **The walking commutative monoid on an ARBITRARY alphabet is DECIDED.**  `= true` records that
`multisetCommMonoidConv_iff_sortedColours` reduces the alphabet-parameterised word problem to equality of
sorted-colour lists — the coincidence of the finite MULTISETS of colour-slots — with soundness (the sorted
multiset is a complete invariant, permutation-invariance flowing from `insertSortedComm`), normalization to the
sorted comb, and completeness all shipped, plus a genuine `Decidable`.  This CLOSES the successor wall named by
the single-generator (`CommutativeMonoidSeed`, one leaf count) and two-colour (`TwoColourCommutativeMonoidSeed`,
a Parikh vector) siblings.  All zero-axiom: the ordering is the structural `natBle` (no `Nat.le`/`Nat.ble`
lemma), and no `List.append` (`++`) appears anywhere. -/
def fxWalkingCommMonoid_hasMultisetDecision : Bool := true

end FX1Poly.Polygraph
