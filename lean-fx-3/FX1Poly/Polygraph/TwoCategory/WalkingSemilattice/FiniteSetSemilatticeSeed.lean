import FX1Poly.Polygraph.TwoCategory.WalkingCommutativeMonoid.MultisetCommutativeMonoidSeed

/-! # WalkingSemilattice/FiniteSetSemilatticeSeed — the walking bounded semilattice on an ARBITRARY alphabet: the finite-SET decision

The successor rung explicitly named as the honest wall in the single-generator (`SemilatticeSeed`, a
two-valued `SlotPresence`) and two-colour (`TwoColourSemilatticeSeed`, a pair of presences = the powerset of a
two-element generator set) semilattice siblings.  The free **bounded semilattice** = idempotent commutative
monoid on the colour set `ℕ` is not a fixed presence tuple but the finite **POWERSET** of the generator set
(join = union): a tree's class in the free bounded semilattice is the SET of colours it contains, with NO
multiplicity — each colour is present or absent.  Because that set is a COMPLETE invariant, and a subset of
`ℕ` has a canonical representative as a SORTED, DISTINCT (dedup'd) list, the word problem is decided by plain
equality of sorted-distinct colour lists.

## ★ Why this walker is the idempotent successor of the multiset commutative monoid

This file REUSES the multiset commutative-monoid substrate verbatim: the purpose-built structural `natBle`
(with totality / transitivity / antisymmetry), the `ColourTree` carrier (`leaf` / `unitOp` / `mulOp`), and the
right-comb `combOfList` — all imported, none redeclared.  The one new ingredient is the **dedup-on-equal**
insert `insertSortedSet`: where the multiset `insertSorted` always grafts a new colour, `insertSortedSet`
COLLAPSES the insertion to a no-op when the colour is already present (the value=head collision).  Idempotency
is threaded exactly at that collision — in `insertSortedSet`, in `insertManySetInsertSorted`, in the
`idem`-law soundness clause, and in `combInsertSortedSet`.  This file ships:

* **soundness** — convertible trees have equal sorted-distinct colour list (`finiteSetSemilatticeConv_sound`),
  the sorted set being a complete invariant that every bounded-semilattice law (the four commutative-monoid
  laws PLUS idempotency) preserves;
* **normalization** — every tree reduces to the right-comb of its sorted-distinct colour list
  (`finiteSetTreeReducesToComb`), grafting via `combMergeSet`;
* **completeness** — equal sorted-distinct colour list ⟹ convertible (`finiteSetSemilatticeConv_complete`);
* **the decision** — the convertibility ⟺ `List Nat`-equality biconditional
  (`finiteSetSemilatticeConv_iff_setColours`) plus a shipped `Decidable`.

This CLOSES the `n`-colour bounded-semilattice successor wall named by `SemilatticeSeed` /
`TwoColourSemilatticeSeed`.

Raw Lean 4 + Init; the convertibility is an inductive `Prop`; per-declaration `#assert_no_axioms` gated in the
audit twin.  Free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega` — the ordering is
the imported structural `natBle` (no `Nat.le`/`Nat.ble` lemma), the inserts are cons-only, and no `List.append`
(`++`) appears anywhere. -/

namespace FX1Poly.Polygraph

/-! ## The natBle reflexivity add-on and two contradiction helpers -/

/-- Reflexivity of the structural `natBle`: `natBle value value = true`.  Structural recursion on `value`. -/
theorem natBleRefl : (value : Nat) → natBle value value = true
  | 0 => rfl
  | Nat.succ predecessor => natBleRefl predecessor

/-- If `natBle left mid` holds but `natBle left right` fails, then `natBle mid right` fails — the
contrapositive of transitivity through `left` on the middle argument.  Used to derive the value-vs-value
strict order from the value-vs-head comparisons in `insertSortedSetComm`. -/
theorem natBleFalseMid (left mid right : Nat)
    (hLeftMid : natBle left mid = true) (hLeftRight : natBle left right = false) :
    natBle mid right = false := by
  cases hMidRight : natBle mid right with
  | false => rfl
  | true =>
    exact Bool.noConfusion
      ((natBleTrans left mid right hLeftMid hMidRight).symm.trans hLeftRight)

/-- If `natBle mid right` holds but `natBle left right` fails, then `natBle left mid` fails — the
contrapositive of transitivity through `right` on the left argument.  The mirror of `natBleFalseMid`. -/
theorem natBleFalseEnd (left mid right : Nat)
    (hMidRight : natBle mid right = true) (hLeftRight : natBle left right = false) :
    natBle left mid = false := by
  cases hLeftMid : natBle left mid with
  | false => rfl
  | true =>
    exact Bool.noConfusion
      ((natBleTrans left mid right hLeftMid hMidRight).symm.trans hLeftRight)

/-! ## The dedup-on-equal sorted-set insert -/

/-- Insert one colour into a sorted DISTINCT list, keeping it sorted and distinct: if `value ≤ head` and
`head ≤ value` (equal, already present) it is a NO-OP; if `value < head` it goes to the front; otherwise it
recurses past `head`.  The dedup is the idempotency of the free bounded semilattice made structural. -/
def insertSortedSet (value : Nat) : List Nat → List Nat
  | [] => [value]
  | head :: tail =>
      match natBle value head with
      | true =>
          match natBle head value with
          | true => head :: tail
          | false => value :: head :: tail
      | false => head :: insertSortedSet value tail

/-- Equation: inserting into the empty list yields the singleton. -/
theorem insertSortedSetNilEq (value : Nat) : insertSortedSet value [] = [value] := rfl

/-- Equation (EQUAL): when `value ≤ head` and `head ≤ value`, the colour is already present — a no-op. -/
theorem insertSortedSetEq (value head : Nat) (tail : List Nat)
    (hle : natBle value head = true) (hge : natBle head value = true) :
    insertSortedSet value (head :: tail) = head :: tail := by
  show (match natBle value head with
        | true => match natBle head value with
                  | true => head :: tail
                  | false => value :: head :: tail
        | false => head :: insertSortedSet value tail) = head :: tail
  rw [hle, hge]

/-- Equation (LESS-THAN): when `value ≤ head` but not `head ≤ value`, the colour is placed at the front. -/
theorem insertSortedSetLt (value head : Nat) (tail : List Nat)
    (hle : natBle value head = true) (hgt : natBle head value = false) :
    insertSortedSet value (head :: tail) = value :: head :: tail := by
  show (match natBle value head with
        | true => match natBle head value with
                  | true => head :: tail
                  | false => value :: head :: tail
        | false => head :: insertSortedSet value tail) = value :: head :: tail
  rw [hle, hgt]

/-- Equation (GREATER-THAN): when `value` exceeds `head`, `head` stays and the insertion recurses. -/
theorem insertSortedSetGt (value head : Nat) (tail : List Nat)
    (hgt : natBle value head = false) :
    insertSortedSet value (head :: tail) = head :: insertSortedSet value tail := by
  show (match natBle value head with
        | true => match natBle head value with
                  | true => head :: tail
                  | false => value :: head :: tail
        | false => head :: insertSortedSet value tail) = head :: insertSortedSet value tail
  rw [hgt]

/-! ## The two crux lemmas -/

/-- Inserting the same colour twice is inserting it once (idempotency of the set-insert).  Structural
induction on the list; at each cons split `natBle value head` then `natBle head value`. -/
theorem insertSortedSetIdem (value : Nat) (xs : List Nat) :
    insertSortedSet value (insertSortedSet value xs) = insertSortedSet value xs := by
  induction xs with
  | nil =>
    rw [insertSortedSetNilEq value,
        insertSortedSetEq value value [] (natBleRefl value) (natBleRefl value)]
  | cons head tail ih =>
    cases hVH : natBle value head with
    | true =>
      cases hHV : natBle head value with
      | true =>
        rw [insertSortedSetEq value head tail hVH hHV, insertSortedSetEq value head tail hVH hHV]
      | false =>
        rw [insertSortedSetLt value head tail hVH hHV,
            insertSortedSetEq value value (head :: tail) (natBleRefl value) (natBleRefl value)]
    | false =>
      rw [insertSortedSetGt value head tail hVH,
          insertSortedSetGt value head (insertSortedSet value tail) hVH, ih]

/-- ★ **The set-insert COMMUTES** — the order of two insertions is irrelevant.  The heart of the finite-set
decision (permutation-invariance of the sorted-distinct normal form).  Structural induction on the list; each
cons resolves the three-way position (LESS / EQUAL / GREATER) of `valueA` and of `valueB` against `head`,
deriving the `valueA`-vs-`valueB` comparisons from those via `natBleTrans` / `natBleTotal` / `natBleAntisymm`
and the two contradiction helpers.  The extra content over the multiset sibling is the EQUAL-to-head no-op
branch handled by `insertSortedSetEq`. -/
theorem insertSortedSetComm (valueA valueB : Nat) (xs : List Nat) :
    insertSortedSet valueA (insertSortedSet valueB xs)
      = insertSortedSet valueB (insertSortedSet valueA xs) := by
  induction xs with
  | nil =>
    rw [insertSortedSetNilEq valueB, insertSortedSetNilEq valueA]
    cases hAB : natBle valueA valueB with
    | true =>
      cases hBA : natBle valueB valueA with
      | true =>
        rw [insertSortedSetEq valueA valueB [] hAB hBA, insertSortedSetEq valueB valueA [] hBA hAB]
        have hEq : valueA = valueB := natBleAntisymm valueA valueB hAB hBA
        rw [hEq]
      | false =>
        rw [insertSortedSetLt valueA valueB [] hAB hBA, insertSortedSetGt valueB valueA [] hBA,
            insertSortedSetNilEq valueB]
    | false =>
      have hBA : natBle valueB valueA = true := natBleTotal valueA valueB hAB
      rw [insertSortedSetGt valueA valueB [] hAB, insertSortedSetNilEq valueA,
          insertSortedSetLt valueB valueA [] hBA hAB]
  | cons head tail ih =>
    cases hAH : natBle valueA head with
    | true =>
      cases hHA : natBle head valueA with
      | true =>
        -- valueA EQUAL head
        cases hBH : natBle valueB head with
        | true =>
          cases hHB : natBle head valueB with
          | true =>
            -- (EQ, EQ)
            rw [insertSortedSetEq valueB head tail hBH hHB, insertSortedSetEq valueA head tail hAH hHA,
                insertSortedSetEq valueB head tail hBH hHB]
          | false =>
            -- (EQ, LT)
            have hABf : natBle valueA valueB = false := natBleFalseMid head valueA valueB hHA hHB
            rw [insertSortedSetLt valueB head tail hBH hHB,
                insertSortedSetGt valueA valueB (head :: tail) hABf,
                insertSortedSetEq valueA head tail hAH hHA,
                insertSortedSetLt valueB head tail hBH hHB]
        | false =>
          -- (EQ, GT)
          rw [insertSortedSetGt valueB head tail hBH,
              insertSortedSetEq valueA head (insertSortedSet valueB tail) hAH hHA,
              insertSortedSetEq valueA head tail hAH hHA,
              insertSortedSetGt valueB head tail hBH]
      | false =>
        -- valueA LESS head
        cases hBH : natBle valueB head with
        | true =>
          cases hHB : natBle head valueB with
          | true =>
            -- (LT, EQ)
            have hBAf : natBle valueB valueA = false := natBleFalseMid head valueB valueA hHB hHA
            rw [insertSortedSetEq valueB head tail hBH hHB, insertSortedSetLt valueA head tail hAH hHA,
                insertSortedSetGt valueB valueA (head :: tail) hBAf,
                insertSortedSetEq valueB head tail hBH hHB]
          | false =>
            -- (LT, LT)
            rw [insertSortedSetLt valueB head tail hBH hHB, insertSortedSetLt valueA head tail hAH hHA]
            cases hAB : natBle valueA valueB with
            | true =>
              cases hBA : natBle valueB valueA with
              | true =>
                rw [insertSortedSetEq valueA valueB (head :: tail) hAB hBA,
                    insertSortedSetEq valueB valueA (head :: tail) hBA hAB]
                have hEq : valueA = valueB := natBleAntisymm valueA valueB hAB hBA
                rw [hEq]
              | false =>
                rw [insertSortedSetLt valueA valueB (head :: tail) hAB hBA,
                    insertSortedSetGt valueB valueA (head :: tail) hBA,
                    insertSortedSetLt valueB head tail hBH hHB]
            | false =>
              have hBA : natBle valueB valueA = true := natBleTotal valueA valueB hAB
              rw [insertSortedSetGt valueA valueB (head :: tail) hAB,
                  insertSortedSetLt valueA head tail hAH hHA,
                  insertSortedSetLt valueB valueA (head :: tail) hBA hAB]
        | false =>
          -- (LT, GT)
          have hBAf : natBle valueB valueA = false := natBleFalseEnd valueB valueA head hAH hBH
          rw [insertSortedSetGt valueB head tail hBH,
              insertSortedSetLt valueA head (insertSortedSet valueB tail) hAH hHA,
              insertSortedSetLt valueA head tail hAH hHA,
              insertSortedSetGt valueB valueA (head :: tail) hBAf,
              insertSortedSetGt valueB head tail hBH]
    | false =>
      -- valueA GREATER head
      cases hBH : natBle valueB head with
      | true =>
        cases hHB : natBle head valueB with
        | true =>
          -- (GT, EQ)
          rw [insertSortedSetEq valueB head tail hBH hHB, insertSortedSetGt valueA head tail hAH,
              insertSortedSetEq valueB head (insertSortedSet valueA tail) hBH hHB]
        | false =>
          -- (GT, LT)
          have hHA : natBle head valueA = true := natBleTotal valueA head hAH
          have hABf : natBle valueA valueB = false := natBleFalseMid head valueA valueB hHA hHB
          rw [insertSortedSetLt valueB head tail hBH hHB,
              insertSortedSetGt valueA valueB (head :: tail) hABf,
              insertSortedSetGt valueA head tail hAH,
              insertSortedSetLt valueB head (insertSortedSet valueA tail) hBH hHB]
      | false =>
        -- (GT, GT)
        rw [insertSortedSetGt valueB head tail hBH,
            insertSortedSetGt valueA head (insertSortedSet valueB tail) hAH,
            insertSortedSetGt valueA head tail hAH,
            insertSortedSetGt valueB head (insertSortedSet valueA tail) hBH]
        exact congrArg (fun rest => head :: rest) ih

/-! ## The many-insert layer -/

/-- Insert every element of the first list into the accumulator, one at a time (set semantics). -/
def insertManySet : List Nat → List Nat → List Nat
  | [], acc => acc
  | head :: tail, acc => insertSortedSet head (insertManySet tail acc)

/-- Push a set-insert through an `insertManySet` onto the accumulator (from `insertSortedSetComm`). -/
theorem insertSortedSetInsertMany (value : Nat) (xs acc : List Nat) :
    insertSortedSet value (insertManySet xs acc) = insertManySet xs (insertSortedSet value acc) := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
    show insertSortedSet value (insertSortedSet head (insertManySet tail acc))
      = insertSortedSet head (insertManySet tail (insertSortedSet value acc))
    rw [insertSortedSetComm value head (insertManySet tail acc), ih]

/-- Pull a set-insert out of the head list of an `insertManySet` (the mirror), collapsing the duplicate head
insert by `insertSortedSetIdem` when the head equals `value`. -/
theorem insertManySetInsertSorted (value : Nat) (xs acc : List Nat) :
    insertManySet (insertSortedSet value xs) acc = insertSortedSet value (insertManySet xs acc) := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
    cases hVH : natBle value head with
    | true =>
      cases hHV : natBle head value with
      | true =>
        rw [insertSortedSetEq value head tail hVH hHV]
        show insertSortedSet head (insertManySet tail acc)
          = insertSortedSet value (insertSortedSet head (insertManySet tail acc))
        have hEq : value = head := natBleAntisymm value head hVH hHV
        rw [hEq, insertSortedSetIdem head (insertManySet tail acc)]
      | false =>
        rw [insertSortedSetLt value head tail hVH hHV]
        rfl
    | false =>
      rw [insertSortedSetGt value head tail hVH]
      show insertSortedSet head (insertManySet (insertSortedSet value tail) acc)
        = insertSortedSet value (insertManySet (head :: tail) acc)
      rw [ih]
      show insertSortedSet head (insertSortedSet value (insertManySet tail acc))
        = insertSortedSet value (insertSortedSet head (insertManySet tail acc))
      rw [insertSortedSetComm head value (insertManySet tail acc)]

/-- `insertManySet` is associative in the fold order. -/
theorem insertManySetAssoc (xs ys acc : List Nat) :
    insertManySet (insertManySet xs ys) acc = insertManySet xs (insertManySet ys acc) := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
    show insertManySet (insertSortedSet head (insertManySet tail ys)) acc
      = insertSortedSet head (insertManySet tail (insertManySet ys acc))
    rw [insertManySetInsertSorted head (insertManySet tail ys) acc, ih]

/-- `insertManySet` commutes over its two list arguments (into a common accumulator). -/
theorem insertManySetComm (xs ys acc : List Nat) :
    insertManySet xs (insertManySet ys acc) = insertManySet ys (insertManySet xs acc) := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
    show insertSortedSet head (insertManySet tail (insertManySet ys acc))
      = insertManySet ys (insertSortedSet head (insertManySet tail acc))
    rw [ih, insertSortedSetInsertMany head ys (insertManySet tail acc)]

/-- Inserting a list's colours on top of themselves is idempotent (from `insertSortedSetIdem` +
`insertSortedSetInsertMany`). -/
theorem insertManySetIdem (xs acc : List Nat) :
    insertManySet xs (insertManySet xs acc) = insertManySet xs acc := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
    show insertSortedSet head (insertManySet tail (insertSortedSet head (insertManySet tail acc)))
      = insertSortedSet head (insertManySet tail acc)
    rw [(insertSortedSetInsertMany head tail (insertManySet tail acc)).symm,
        insertSortedSetIdem head (insertManySet tail (insertManySet tail acc))]
    exact congrArg (insertSortedSet head) ih

/-! ## The tree fold to the sorted-distinct normal form -/

/-- Insert a tree's colour-slots into an accumulator, sorted and DISTINCT: a `leaf` inserts its colour,
`unitOp` contributes nothing, and `mulOp` inserts the right subtree then the left. -/
def insertTreeSet : ColourTree → List Nat → List Nat
  | .leaf colour, acc => insertSortedSet colour acc
  | .unitOp, acc => acc
  | .mulOp left right, acc => insertTreeSet left (insertTreeSet right acc)

/-- The sorted-DISTINCT colour list of a tree — its SET of colours in sorted normal form.  The complete
convertibility invariant of the free bounded semilattice on `ℕ`. -/
def setColoursOf (tree : ColourTree) : List Nat := insertTreeSet tree []

/-- Smoke: a single colour-slot yields its singleton. -/
theorem setColoursOf_leaf : setColoursOf (ColourTree.leaf 2) = [2] := rfl

/-- Smoke: two copies of the same colour DEDUP to a single occurrence — the idempotent collapse. -/
theorem setColoursOf_dedup :
    setColoursOf (ColourTree.mulOp (ColourTree.leaf 1) (ColourTree.leaf 1)) = [1] := rfl

/-- Smoke: two distinct colours in a skewed graft come out sorted and distinct. -/
theorem setColoursOf_sorts :
    setColoursOf (ColourTree.mulOp (ColourTree.leaf 3) (ColourTree.leaf 1)) = [1, 3] := rfl

/-- `insertTreeSet` spreads as an `insertManySet` of the tree's sorted-distinct colours onto the accumulator.
Structural induction on the tree (generalizing the accumulator); the `mulOp` case re-associates with
`insertManySetAssoc`. -/
theorem insertTreeSetSpread (tree : ColourTree) (acc : List Nat) :
    insertTreeSet tree acc = insertManySet (setColoursOf tree) acc := by
  induction tree generalizing acc with
  | leaf colour => rfl
  | unitOp => rfl
  | mulOp left right ihLeft ihRight =>
    show insertTreeSet left (insertTreeSet right acc)
      = insertManySet (setColoursOf (ColourTree.mulOp left right)) acc
    rw [ihLeft (insertTreeSet right acc), ihRight acc]
    have hMul : setColoursOf (ColourTree.mulOp left right)
        = insertManySet (setColoursOf left) (setColoursOf right) := by
      show insertTreeSet left (insertTreeSet right [])
        = insertManySet (setColoursOf left) (setColoursOf right)
      rw [ihLeft (insertTreeSet right [])]
      rfl
    rw [hMul, insertManySetAssoc (setColoursOf left) (setColoursOf right) acc]

/-- The colours of a graft merge the colours of the children — a one-line corollary of
`insertTreeSetSpread`. -/
theorem setColoursOfMul (left right : ColourTree) :
    setColoursOf (ColourTree.mulOp left right)
      = insertManySet (setColoursOf left) (setColoursOf right) := by
  show insertTreeSet left (insertTreeSet right []) = insertManySet (setColoursOf left) (setColoursOf right)
  rw [insertTreeSetSpread left (insertTreeSet right [])]
  rfl

/-- Folding a tree's sorted-distinct colours into the empty accumulator recovers those colours. -/
theorem insertManySetSetColoursNil (tree : ColourTree) :
    insertManySet (setColoursOf tree) [] = setColoursOf tree :=
  (insertTreeSetSpread tree []).symm

/-! ## The bounded-semilattice tree-pasting convertibility (five laws) -/

/-- ★ The **tree-pasting convertibility** of the walking bounded semilattice on an arbitrary alphabet — the
free-operad convertibility of the `{m, e}` signature over colour-tagged generators closed under the FIVE
bounded-semilattice laws (associativity, left unit, right unit, commutativity, and **idempotency**
`m(x, x) ≈ x`), the full tree-congruence `mulCongr`, and `refl` / `symm` / `trans`.  Two trees denote the same
element of the free bounded semilattice on `ℕ` exactly when they are `FiniteSetSemilatticeTreeConv`-related. -/
inductive FiniteSetSemilatticeTreeConv : ColourTree → ColourTree → Prop where
  /-- **Associativity** `m(m(left, middle), right) ≈ m(left, m(middle, right))`. -/
  | assoc (left middle right : ColourTree) :
      FiniteSetSemilatticeTreeConv
        (ColourTree.mulOp (ColourTree.mulOp left middle) right)
        (ColourTree.mulOp left (ColourTree.mulOp middle right))
  /-- **Left unit** `m(unitOp, subtree) ≈ subtree`. -/
  | unitLeft (subtree : ColourTree) :
      FiniteSetSemilatticeTreeConv (ColourTree.mulOp ColourTree.unitOp subtree) subtree
  /-- **Right unit** `m(subtree, unitOp) ≈ subtree`. -/
  | unitRight (subtree : ColourTree) :
      FiniteSetSemilatticeTreeConv (ColourTree.mulOp subtree ColourTree.unitOp) subtree
  /-- **Commutativity** `m(left, right) ≈ m(right, left)` — mixing colours freely. -/
  | commSwap (left right : ColourTree) :
      FiniteSetSemilatticeTreeConv (ColourTree.mulOp left right) (ColourTree.mulOp right left)
  /-- **Idempotency** `m(subtree, subtree) ≈ subtree` — the relation the commutative monoid lacks. -/
  | idem (subtree : ColourTree) :
      FiniteSetSemilatticeTreeConv (ColourTree.mulOp subtree subtree) subtree
  /-- **Congruence under a grafting node** — into BOTH children. -/
  | mulCongr {leftOld leftNew rightOld rightNew : ColourTree} :
      FiniteSetSemilatticeTreeConv leftOld leftNew → FiniteSetSemilatticeTreeConv rightOld rightNew →
      FiniteSetSemilatticeTreeConv (ColourTree.mulOp leftOld rightOld) (ColourTree.mulOp leftNew rightNew)
  /-- Reflexivity. -/
  | refl (tree : ColourTree) : FiniteSetSemilatticeTreeConv tree tree
  /-- Symmetry. -/
  | symm {tree1 tree2 : ColourTree} :
      FiniteSetSemilatticeTreeConv tree1 tree2 → FiniteSetSemilatticeTreeConv tree2 tree1
  /-- Transitivity. -/
  | trans {tree1 tree2 tree3 : ColourTree} :
      FiniteSetSemilatticeTreeConv tree1 tree2 → FiniteSetSemilatticeTreeConv tree2 tree3 →
      FiniteSetSemilatticeTreeConv tree1 tree3

/-! ## Soundness: convertible ⟹ equal sorted-distinct colour list -/

/-- ★ **Soundness** — convertible trees have equal sorted-distinct colour list.  Each law preserves the sorted
set: associativity, left unit, and right unit are definitional (`insertTreeSet` is a right-nested fold);
commutativity is `insertManySetComm`; idempotency is `insertManySetIdem`; the congruence follows from the
inductive hypotheses through `setColoursOfMul`.  The sorted-distinct list is a COMPLETE invariant. -/
theorem finiteSetSemilatticeConv_sound {source target : ColourTree}
    (conv : FiniteSetSemilatticeTreeConv source target) : setColoursOf source = setColoursOf target := by
  induction conv with
  | assoc left middle right => rfl
  | unitLeft subtree => rfl
  | unitRight subtree => rfl
  | commSwap left right =>
    rw [setColoursOfMul left right, setColoursOfMul right left]
    exact
      ((congrArg (insertManySet (setColoursOf left)) (insertManySetSetColoursNil right)).symm.trans
        (insertManySetComm (setColoursOf left) (setColoursOf right) [])).trans
        (congrArg (insertManySet (setColoursOf right)) (insertManySetSetColoursNil left))
  | idem subtree =>
    rw [setColoursOfMul subtree subtree]
    have hIdem := insertManySetIdem (setColoursOf subtree) []
    rw [insertManySetSetColoursNil subtree] at hIdem
    exact hIdem
  | mulCongr _ _ ihLeft ihRight =>
    rw [setColoursOfMul, setColoursOfMul, ihLeft, ihRight]
  | refl tree => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ## Normalization: every tree reduces to the right-comb of its sorted-distinct colours -/

/-- Inserting a colour into a sorted-distinct list is convertible to grafting it on the comb's front,
COLLAPSING by idempotency when the colour is already present.  Induction on the list; at each cons split
`natBle colour head` then `natBle head colour`. -/
theorem combInsertSortedSet (colour : Nat) (xs : List Nat) :
    FiniteSetSemilatticeTreeConv (combOfList (insertSortedSet colour xs))
      (ColourTree.mulOp (ColourTree.leaf colour) (combOfList xs)) := by
  induction xs with
  | nil => exact FiniteSetSemilatticeTreeConv.refl _
  | cons head rest ih =>
    cases hCH : natBle colour head with
    | true =>
      cases hHC : natBle head colour with
      | true =>
        rw [insertSortedSetEq colour head rest hCH hHC]
        have hEq : colour = head := natBleAntisymm colour head hCH hHC
        rw [hEq]
        exact FiniteSetSemilatticeTreeConv.symm
          (FiniteSetSemilatticeTreeConv.trans
            (FiniteSetSemilatticeTreeConv.symm
              (FiniteSetSemilatticeTreeConv.assoc (ColourTree.leaf head) (ColourTree.leaf head)
                (combOfList rest)))
            (FiniteSetSemilatticeTreeConv.mulCongr
              (FiniteSetSemilatticeTreeConv.idem (ColourTree.leaf head))
              (FiniteSetSemilatticeTreeConv.refl (combOfList rest))))
      | false =>
        rw [insertSortedSetLt colour head rest hCH hHC]
        exact FiniteSetSemilatticeTreeConv.refl _
    | false =>
      rw [insertSortedSetGt colour head rest hCH]
      exact
        (FiniteSetSemilatticeTreeConv.mulCongr
            (FiniteSetSemilatticeTreeConv.refl (ColourTree.leaf head)) ih).trans
          ((FiniteSetSemilatticeTreeConv.symm
              (FiniteSetSemilatticeTreeConv.assoc (ColourTree.leaf head) (ColourTree.leaf colour)
                (combOfList rest))).trans
            ((FiniteSetSemilatticeTreeConv.mulCongr
                (FiniteSetSemilatticeTreeConv.commSwap (ColourTree.leaf head) (ColourTree.leaf colour))
                (FiniteSetSemilatticeTreeConv.refl (combOfList rest))).trans
              (FiniteSetSemilatticeTreeConv.assoc (ColourTree.leaf colour) (ColourTree.leaf head)
                (combOfList rest))))

/-- Grafting two combs is convertible to the comb of the merged (dedup'd) colour lists.  Induction on `xs`;
the cons case re-associates the leading colour out, recurses, and re-absorbs via `combInsertSortedSet`. -/
theorem combMergeSet (xs ys : List Nat) :
    FiniteSetSemilatticeTreeConv (ColourTree.mulOp (combOfList xs) (combOfList ys))
      (combOfList (insertManySet xs ys)) := by
  induction xs with
  | nil => exact FiniteSetSemilatticeTreeConv.unitLeft (combOfList ys)
  | cons head tail ih =>
    exact
      (FiniteSetSemilatticeTreeConv.assoc (ColourTree.leaf head) (combOfList tail) (combOfList ys)).trans
        ((FiniteSetSemilatticeTreeConv.mulCongr (FiniteSetSemilatticeTreeConv.refl (ColourTree.leaf head))
            ih).trans
          (FiniteSetSemilatticeTreeConv.symm (combInsertSortedSet head (insertManySet tail ys))))

/-- ★ **Normalization** — every tree is convertible to the right-comb of its own sorted-distinct colour list.
Induction on the tree: `leaf` reduces via right unit, `unitOp` is already `combOfList []`, and `mulOp`
normalizes the two children (`mulCongr`) then grafts them with `combMergeSet`, transporting the merged colours
back through `setColoursOfMul`. -/
theorem finiteSetTreeReducesToComb (tree : ColourTree) :
    FiniteSetSemilatticeTreeConv tree (combOfList (setColoursOf tree)) := by
  induction tree with
  | leaf colour =>
    exact FiniteSetSemilatticeTreeConv.symm (FiniteSetSemilatticeTreeConv.unitRight (ColourTree.leaf colour))
  | unitOp => exact FiniteSetSemilatticeTreeConv.refl ColourTree.unitOp
  | mulOp left right ihLeft ihRight =>
    have chain : FiniteSetSemilatticeTreeConv (ColourTree.mulOp left right)
        (combOfList (insertManySet (setColoursOf left) (setColoursOf right))) :=
      (FiniteSetSemilatticeTreeConv.mulCongr ihLeft ihRight).trans
        (combMergeSet (setColoursOf left) (setColoursOf right))
    have treeEq : combOfList (insertManySet (setColoursOf left) (setColoursOf right))
        = combOfList (setColoursOf (ColourTree.mulOp left right)) :=
      congrArg combOfList (setColoursOfMul left right).symm
    exact treeEq ▸ chain

/-! ## Completeness and the decision -/

/-- ★ **Completeness** — equal sorted-distinct colour list implies convertibility, through the common comb
normal form. -/
theorem finiteSetSemilatticeConv_complete {source target : ColourTree}
    (coloursEq : setColoursOf source = setColoursOf target) :
    FiniteSetSemilatticeTreeConv source target := by
  have sourceReduces : FiniteSetSemilatticeTreeConv source (combOfList (setColoursOf source)) :=
    finiteSetTreeReducesToComb source
  have targetReduces : FiniteSetSemilatticeTreeConv target (combOfList (setColoursOf target)) :=
    finiteSetTreeReducesToComb target
  have combEq : combOfList (setColoursOf source) = combOfList (setColoursOf target) :=
    congrArg combOfList coloursEq
  exact FiniteSetSemilatticeTreeConv.trans sourceReduces
    (combEq.symm ▸ FiniteSetSemilatticeTreeConv.symm targetReduces)

/-- ★ **The decision** — convertibility in the walking bounded semilattice on an arbitrary alphabet is exactly
equality of sorted-distinct colour lists (the finite SETS of colours coincide).  Since `List Nat` equality is
decidable (structural `DecidableEq`), this biconditional decides the word problem. -/
theorem finiteSetSemilatticeConv_iff_setColours (source target : ColourTree) :
    FiniteSetSemilatticeTreeConv source target ↔ setColoursOf source = setColoursOf target :=
  ⟨finiteSetSemilatticeConv_sound, finiteSetSemilatticeConv_complete⟩

/-- ★ **The decider** — a shipped `Decidable` for the arbitrary-alphabet convertibility, built from the
sorted-distinct-list decision: match the derived `DecidableEq (List Nat)`, discharging `isTrue` by completeness
and `isFalse` by soundness.  A genuine decider (not `decidable_of_iff`), propext-free. -/
def decideFiniteSetSemilatticeTreeConv (source target : ColourTree) :
    Decidable (FiniteSetSemilatticeTreeConv source target) :=
  match (inferInstance : Decidable (setColoursOf source = setColoursOf target)) with
  | isTrue coloursEq => isTrue (finiteSetSemilatticeConv_complete coloursEq)
  | isFalse coloursNe => isFalse (fun conv => coloursNe (finiteSetSemilatticeConv_sound conv))

/-- The arbitrary-alphabet convertibility as a `Decidable` INSTANCE, so the `decide` tactic and instance
resolution fire on it.  A definitional alias of the shipped decider, hence propext-free. -/
instance instDecidableFiniteSetSemilatticeTreeConv (source target : ColourTree) :
    Decidable (FiniteSetSemilatticeTreeConv source target) :=
  decideFiniteSetSemilatticeTreeConv source target

/-! ## Groundings -/

/-- ★ **The decision in action (positive, reorder)** — two differently-ordered two-colour trees with the same
colour SET `{0, 1}` are convertible, decided purely by their equal sorted-distinct colour list
(`[0, 1] = [0, 1]`) through completeness — no explicit rewrite path supplied. -/
theorem finiteSetSemilatticeReordersColours :
    FiniteSetSemilatticeTreeConv
      (ColourTree.mulOp (ColourTree.leaf 0) (ColourTree.leaf 1))
      (ColourTree.mulOp (ColourTree.leaf 1) (ColourTree.leaf 0)) :=
  finiteSetSemilatticeConv_complete rfl

/-- ★ **The decision in action (positive, idempotent collapse)** — `m(leaf 0, leaf 0)` (colour SET `{0}`) IS
convertible to `leaf 0`: the sorted-distinct lists coincide (`[0] = [0]`, the duplicate dedup'd), the SET-level
content the multiset commutative-monoid walker CANNOT see. -/
theorem finiteSetSemilatticeCollapsesRepeatedColour :
    FiniteSetSemilatticeTreeConv
      (ColourTree.mulOp (ColourTree.leaf 0) (ColourTree.leaf 0)) (ColourTree.leaf 0) :=
  finiteSetSemilatticeConv_complete rfl

/-- ★ **The decision in action (positive, dedup across a graft)** — `m(m(leaf 0, leaf 1), leaf 1)` collapses to
`m(leaf 0, leaf 1)`: the repeated colour `1` is dedup'd, both sides sharing the colour SET `{0, 1}`
(`[0, 1] = [0, 1]`). -/
theorem finiteSetSemilatticeDedupsRepeatedColour :
    FiniteSetSemilatticeTreeConv
      (ColourTree.mulOp (ColourTree.mulOp (ColourTree.leaf 0) (ColourTree.leaf 1)) (ColourTree.leaf 1))
      (ColourTree.mulOp (ColourTree.leaf 0) (ColourTree.leaf 1)) :=
  finiteSetSemilatticeConv_complete rfl

/-- ★ **The decision in action (negative)** — a lone `leaf 0` (colour SET `{0}`) is NOT convertible to
`m(leaf 0, leaf 1)` (colour SET `{0, 1}`): the sorted-distinct lists `[0]` and `[0, 1]` differ, so by
soundness no convertibility can exist.  `[0] ≠ [0, 1]` by structural `cases` on the equality. -/
theorem finiteSetSemilatticeRejectsMissingColour :
    ¬ FiniteSetSemilatticeTreeConv (ColourTree.leaf 0)
        (ColourTree.mulOp (ColourTree.leaf 0) (ColourTree.leaf 1)) := by
  intro conv
  have coloursEq : ([0] : List Nat) = [0, 1] := finiteSetSemilatticeConv_sound conv
  cases coloursEq

/-! ## The marker -/

/-- ★ **The walking bounded semilattice on an ARBITRARY alphabet is DECIDED** — finite-SET (sorted-distinct
colour list) equality.  `= true` records that `finiteSetSemilatticeConv_iff_setColours` reduces the
alphabet-parameterised word problem to equality of sorted-distinct colour lists — the coincidence of the finite
SETS of colours (the POWERSET of the generator set, join = union) — with soundness (idempotency flowing from
`insertManySetIdem` / `insertSortedSetIdem`), normalization to the dedup'd comb, and completeness all shipped,
plus a genuine `Decidable`.  This CLOSES the `n`-colour semilattice successor wall named by `SemilatticeSeed`
and `TwoColourSemilatticeSeed`.  All zero-axiom: the ordering is the imported structural `natBle` (no
`Nat.le`/`Nat.ble` lemma), the inserts are cons-only, and no `List.append` (`++`) appears anywhere. -/
def fxWalkingSemilattice_hasFiniteSetDecision : Bool := true

end FX1Poly.Polygraph
