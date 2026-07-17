/-! # WalkingAbelianGroup/AbelianGroupSeed — the walking (free) abelian group of rank one = walking ℤ: signature, tree convertibility, and the FULL single-generator decision

The presentation of the free **abelian group** on one generating input slot, as a signature plus a
tree convertibility: the binary multiplication `m : arity 2`, the nullary unit `e : arity 0`, the unary
inverse `i : arity 1`, and the input slot, with the abelian-group laws — associativity, left/right unit,
commutativity, left/right inverse (`m(i x, x) ≈ e`, `m(x, i x) ≈ e`), and the derived inverse-homomorphism
laws (`i(m a b) ≈ m(i a)(i b)`, `i e ≈ e`, `i(i x) ≈ x`).

## ★ Why this walker is FULLY DECIDED — and why the model is ℤ

The sibling `WalkingCommutativeMonoid` on one generator has word problem `(ℕ, +, 0)` — leaf COUNT; the
sibling `WalkingSemilattice` collapses that count to two values by idempotency.  Adjoining a formal inverse
`i` instead **completes** the commutative monoid `ℕ` to its group of differences — the integers `ℤ`.  So a
tree's class is determined by its **winding number**: (number of positive slots) minus (number of inverse
slots).  This file represents that integer WITHOUT a signed type and WITHOUT subtraction, as a difference
pair `⟨positiveSlots, inverseSlots⟩ : ℕ²` under the relation `p₁ + n₂ = p₂ + n₁` (the standard Grothendieck
construction of ℤ from ℕ, written purely additively) — deliberately dodging the `Int.add_comm` / `Nat.sub`
propext hazards.  This file ships:

* **soundness** — convertible trees have `windingEquiv` winding pairs (`abelianGroupTreeConv_sound`);
* **normalization** — every tree reduces to an unreduced pair-form `pairForm p n` (`toPairFormConv`);
* **completeness** — `windingEquiv` winding pairs ⟹ convertible, by pumping both pair-forms to a common
  one via a cancelling `m(leaf, i leaf) ≈ e` insertion (`abelianGroupTreeConv_complete`);
* **the decision** — the convertibility ⟺ `windingEquiv` biconditional plus a genuine `Decidable`
  (`abelianGroupTreeConv_iff_windingEquiv`, `decideAbelianGroupTreeConv`).

## ★ The honest wall

The MULTI-generator (coloured) free abelian group is `ℤᵏ` = the free ℤ-module on the generator set: a tree's
class is a VECTOR of winding numbers, decided by componentwise `ℤ`-equality rather than a single difference
pair.  That decision needs a per-colour winding vector and is the successor rung; it is NOT attempted here.
This file is the single-generator instance (= walking ℤ), complete.

Raw Lean 4 + Init; the convertibility is an inductive `Prop`; per-declaration `#assert_no_axioms` gated in the
audit twin.  Free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`, `Nat.sub` — the
only arithmetic used is `Nat.add_comm` / `Nat.add_assoc` / `Nat.add_zero` (all propext-clean) plus one
additive `Nat` right-cancellation proved structurally here. -/

namespace FX1Poly.Polygraph

/-! ## The abelian-group tree carrier -/

/-- ★ The **tree carrier** of the walking abelian group: an un-indexed tree over the three group generators.
`leaf` is an arity-1 input slot (the operad identity); `unitOp` is the nullary generator `e`; `invOp` applies
the unary inverse `i`; `mulOp` grafts two subtrees under the binary generator `m`.  For the single-generator
abelian group, a closed tree's winding number (positive slots minus inverse slots) is its complete
convertibility invariant. -/
inductive AbelianGroupTree where
  /-- An arity-1 input slot — the operad identity `id ∈ operad(1)`. -/
  | leaf
  /-- The nullary generator `e : arity 0` (the group unit). -/
  | unitOp
  /-- The unary generator `i : arity 1` (the group inverse) applied to a subtree. -/
  | invOp : AbelianGroupTree → AbelianGroupTree
  /-- The binary generator `m : arity 2` grafting the left and right subtrees (`m(left, right)`). -/
  | mulOp : AbelianGroupTree → AbelianGroupTree → AbelianGroupTree

/-! ## The winding invariant: a difference pair (ℕ² presenting ℤ, no signed type, no subtraction) -/

/-- The **winding count** of a tree — a difference pair presenting an integer as `positiveSlots` minus
`inverseSlots` WITHOUT a signed type or subtraction.  `positiveSlots` counts input slots reachable through an
even number of inverses; `inverseSlots` counts those reachable through an odd number.  Their (Grothendieck)
difference is the winding number in `ℤ`. -/
structure WindingCount where
  /-- Slots under an even number of inverses (the positive part of the difference). -/
  positiveSlots : Nat
  /-- Slots under an odd number of inverses (the negative part of the difference). -/
  inverseSlots : Nat

/-- The **winding count** of a tree.  `leaf ↦ ⟨1, 0⟩`, `unitOp ↦ ⟨0, 0⟩`, `invOp` SWAPS the two components
(passing through one inverse flips positive and negative), and `mulOp` adds componentwise.  A full-enumeration
structural fold (no wildcard), propext-clean. -/
def windingOf : AbelianGroupTree → WindingCount
  | .leaf => ⟨1, 0⟩
  | .unitOp => ⟨0, 0⟩
  | .invOp inner => ⟨(windingOf inner).inverseSlots, (windingOf inner).positiveSlots⟩
  | .mulOp left right =>
      ⟨(windingOf left).positiveSlots + (windingOf right).positiveSlots,
       (windingOf left).inverseSlots + (windingOf right).inverseSlots⟩

/-- The **winding equivalence** — two difference pairs present the same integer.  Stated purely additively
(`p₁ + n₂ = p₂ + n₁`), so it needs no subtraction and no signed type; decidable via `Nat.decEq`. -/
def windingEquiv (first second : WindingCount) : Prop :=
  first.positiveSlots + second.inverseSlots = second.positiveSlots + first.inverseSlots

/-- Smoke: a single input slot winds `⟨1, 0⟩`. -/
theorem windingOf_leaf : windingOf AbelianGroupTree.leaf = ⟨1, 0⟩ := rfl

/-- Smoke: the unit winds `⟨0, 0⟩`. -/
theorem windingOf_unit : windingOf AbelianGroupTree.unitOp = ⟨0, 0⟩ := rfl

/-- Smoke: an inverted slot winds `⟨0, 1⟩` — the inverse swaps the difference pair. -/
theorem windingOf_invLeaf : windingOf (AbelianGroupTree.invOp AbelianGroupTree.leaf) = ⟨0, 1⟩ := rfl

/-! ## The abelian-group tree convertibility -/

/-- ★ The **tree convertibility** of the walking abelian group — the free convertibility of the `{m, e, i}`
signature closed under the abelian-group laws (associativity, left/right unit, commutativity, left/right
inverse, and the inverse-homomorphism laws), the full congruences `mulCongr` / `invCongr`, and `refl` /
`symm` / `trans`.  Two trees denote the same element of the free abelian group exactly when they are
`AbelianGroupTreeConv`-related. -/
inductive AbelianGroupTreeConv : AbelianGroupTree → AbelianGroupTree → Prop where
  /-- **Associativity** `m(m(left, middle), right) ≈ m(left, m(middle, right))`. -/
  | assoc (left middle right : AbelianGroupTree) :
      AbelianGroupTreeConv
        (AbelianGroupTree.mulOp (AbelianGroupTree.mulOp left middle) right)
        (AbelianGroupTree.mulOp left (AbelianGroupTree.mulOp middle right))
  /-- **Left unit** `m(e, subtree) ≈ subtree`. -/
  | unitLeft (subtree : AbelianGroupTree) :
      AbelianGroupTreeConv (AbelianGroupTree.mulOp AbelianGroupTree.unitOp subtree) subtree
  /-- **Right unit** `m(subtree, e) ≈ subtree`. -/
  | unitRight (subtree : AbelianGroupTree) :
      AbelianGroupTreeConv (AbelianGroupTree.mulOp subtree AbelianGroupTree.unitOp) subtree
  /-- **Commutativity** `m(left, right) ≈ m(right, left)`. -/
  | commSwap (left right : AbelianGroupTree) :
      AbelianGroupTreeConv (AbelianGroupTree.mulOp left right) (AbelianGroupTree.mulOp right left)
  /-- **Left inverse** `m(i subtree, subtree) ≈ e`. -/
  | invLeft (subtree : AbelianGroupTree) :
      AbelianGroupTreeConv (AbelianGroupTree.mulOp (AbelianGroupTree.invOp subtree) subtree)
        AbelianGroupTree.unitOp
  /-- **Right inverse** `m(subtree, i subtree) ≈ e`. -/
  | invRight (subtree : AbelianGroupTree) :
      AbelianGroupTreeConv (AbelianGroupTree.mulOp subtree (AbelianGroupTree.invOp subtree))
        AbelianGroupTree.unitOp
  /-- **Inverse homomorphism** `i(m(treeA, treeB)) ≈ m(i treeA, i treeB)` (valid because the group is
  abelian, so the inverse distributes without reversing order). -/
  | invHom (treeA treeB : AbelianGroupTree) :
      AbelianGroupTreeConv (AbelianGroupTree.invOp (AbelianGroupTree.mulOp treeA treeB))
        (AbelianGroupTree.mulOp (AbelianGroupTree.invOp treeA) (AbelianGroupTree.invOp treeB))
  /-- **Inverse of unit** `i e ≈ e`. -/
  | invUnit : AbelianGroupTreeConv (AbelianGroupTree.invOp AbelianGroupTree.unitOp) AbelianGroupTree.unitOp
  /-- **Inverse involution** `i(i subtree) ≈ subtree`. -/
  | invInvol (subtree : AbelianGroupTree) :
      AbelianGroupTreeConv (AbelianGroupTree.invOp (AbelianGroupTree.invOp subtree)) subtree
  /-- **Congruence under a grafting node** — into BOTH children. -/
  | mulCongr {leftOld leftNew rightOld rightNew : AbelianGroupTree} :
      AbelianGroupTreeConv leftOld leftNew → AbelianGroupTreeConv rightOld rightNew →
      AbelianGroupTreeConv (AbelianGroupTree.mulOp leftOld rightOld)
        (AbelianGroupTree.mulOp leftNew rightNew)
  /-- **Congruence under an inverse node**. -/
  | invCongr {innerOld innerNew : AbelianGroupTree} :
      AbelianGroupTreeConv innerOld innerNew →
      AbelianGroupTreeConv (AbelianGroupTree.invOp innerOld) (AbelianGroupTree.invOp innerNew)
  /-- Reflexivity. -/
  | refl (tree : AbelianGroupTree) : AbelianGroupTreeConv tree tree
  /-- Symmetry. -/
  | symm {tree1 tree2 : AbelianGroupTree} :
      AbelianGroupTreeConv tree1 tree2 → AbelianGroupTreeConv tree2 tree1
  /-- Transitivity. -/
  | trans {tree1 tree2 tree3 : AbelianGroupTree} :
      AbelianGroupTreeConv tree1 tree2 → AbelianGroupTreeConv tree2 tree3 → AbelianGroupTreeConv tree1 tree3

/-! ## The propext-clean `Nat` arithmetic kit -/

/-- `0 + value = value`, propext-clean (via `add_comm` + the definitional `add_zero`, avoiding any leaky
lemma). -/
theorem natZeroAdd (value : Nat) : 0 + value = value :=
  (Nat.add_comm 0 value).trans (Nat.add_zero value)

/-- The **middle-four exchange** `(first + second) + (third + fourth) = (first + third) + (second + fourth)`
— pure `add_assoc` / `add_comm`, propext-clean.  The one reassociation engine both congruence lemmas below
share. -/
theorem addMiddleFour (first second third fourth : Nat) :
    (first + second) + (third + fourth) = (first + third) + (second + fourth) :=
  (Nat.add_assoc first second (third + fourth)).trans
    ((congrArg (fun tailSum => first + tailSum) (Nat.add_assoc second third fourth).symm).trans
      ((congrArg (fun swapped => first + (swapped + fourth)) (Nat.add_comm second third)).trans
        ((congrArg (fun tailSum => first + tailSum) (Nat.add_assoc third second fourth)).trans
          (Nat.add_assoc first third (second + fourth)).symm)))

/-- The **diagonal exchange** `(first + second) + (third + fourth) = (first + fourth) + (third + second)`
— swaps the two trailing summands; built from `addMiddleFour` and `add_comm`, propext-clean. -/
theorem addExchange (first second third fourth : Nat) :
    (first + second) + (third + fourth) = (first + fourth) + (third + second) :=
  (congrArg (fun tailSum => (first + second) + tailSum) (Nat.add_comm third fourth)).trans
    ((addMiddleFour first second fourth third).trans
      (congrArg (fun tailSum => (first + fourth) + tailSum) (Nat.add_comm second third)))

/-- Additive **right cancellation** on `Nat`, proved structurally on the cancelled amount (base by
`add_zero`, step by `Nat.succ.inj`).  Avoids `Nat.sub` entirely — the transitivity of `windingEquiv` needs
exactly this. -/
theorem abelianGroupNatAddRightCancel (amount : Nat) :
    ∀ (leftSummand rightSummand : Nat),
      leftSummand + amount = rightSummand + amount → leftSummand = rightSummand := by
  induction amount with
  | zero =>
      intro leftSummand rightSummand summandsEq
      exact (Nat.add_zero leftSummand).symm.trans (summandsEq.trans (Nat.add_zero rightSummand))
  | succ predecessor ih =>
      intro leftSummand rightSummand summandsEq
      exact ih leftSummand rightSummand (Nat.succ.inj summandsEq)

/-! ## The winding algebra: `windingEquiv` is an equivalence, and the two congruences -/

/-- Componentwise **product** of winding counts (matches `windingOf (mulOp _ _)` definitionally). -/
def windingMul (left right : WindingCount) : WindingCount :=
  ⟨left.positiveSlots + right.positiveSlots, left.inverseSlots + right.inverseSlots⟩

/-- The **swap** of a winding count (matches `windingOf (invOp _)` definitionally — the inverse flips the
difference pair). -/
def windingInv (inner : WindingCount) : WindingCount :=
  ⟨inner.inverseSlots, inner.positiveSlots⟩

/-- `windingEquiv` is reflexive. -/
theorem windingEquivRefl (value : WindingCount) : windingEquiv value value := rfl

/-- `windingEquiv` is symmetric. -/
theorem windingEquivSymm {first second : WindingCount}
    (equiv : windingEquiv first second) : windingEquiv second first := equiv.symm

/-- `windingEquiv` is transitive — the one nontrivial step, closed additively by right cancellation of
`second.positiveSlots + second.inverseSlots` (NO subtraction). -/
theorem windingEquivTrans {first second third : WindingCount}
    (firstToSecond : windingEquiv first second) (secondToThird : windingEquiv second third) :
    windingEquiv first third :=
  abelianGroupNatAddRightCancel (second.positiveSlots + second.inverseSlots)
    (first.positiveSlots + third.inverseSlots) (third.positiveSlots + first.inverseSlots)
    ((addExchange first.positiveSlots third.inverseSlots second.positiveSlots second.inverseSlots).trans
      ((congrArg (fun leftPart => leftPart + (second.positiveSlots + third.inverseSlots)) firstToSecond).trans
        ((congrArg (fun rightPart => (second.positiveSlots + first.inverseSlots) + rightPart) secondToThird).trans
          ((addExchange second.positiveSlots first.inverseSlots third.positiveSlots second.inverseSlots).trans
            (Nat.add_comm (second.positiveSlots + second.inverseSlots)
              (third.positiveSlots + first.inverseSlots))))))

/-- `windingEquiv` respects the componentwise product — the winding shadow of `mulCongr`. -/
theorem windingEquivMulCongr {leftOld leftNew rightOld rightNew : WindingCount}
    (leftEquiv : windingEquiv leftOld leftNew) (rightEquiv : windingEquiv rightOld rightNew) :
    windingEquiv (windingMul leftOld rightOld) (windingMul leftNew rightNew) :=
  (addMiddleFour leftOld.positiveSlots rightOld.positiveSlots leftNew.inverseSlots rightNew.inverseSlots).trans
    (((congrArg (fun leftPart => leftPart + (rightOld.positiveSlots + rightNew.inverseSlots)) leftEquiv).trans
        (congrArg (fun rightPart => (leftNew.positiveSlots + leftOld.inverseSlots) + rightPart) rightEquiv)).trans
      (addMiddleFour leftNew.positiveSlots leftOld.inverseSlots rightNew.positiveSlots rightOld.inverseSlots))

/-- `windingEquiv` respects the swap — the winding shadow of `invCongr`. -/
theorem windingEquivInvCongr {innerOld innerNew : WindingCount}
    (innerEquiv : windingEquiv innerOld innerNew) :
    windingEquiv (windingInv innerOld) (windingInv innerNew) :=
  (Nat.add_comm innerOld.inverseSlots innerNew.positiveSlots).trans
    (innerEquiv.symm.trans (Nat.add_comm innerOld.positiveSlots innerNew.inverseSlots))

/-! ## Soundness: convertible ⟹ winding-equivalent -/

/-- ★ **Soundness** — convertible trees have `windingEquiv` winding counts.  Every law preserves the
difference pair: the (co)unit / associativity / commutativity laws by `Nat.add_comm` / `add_assoc` /
`add_zero`, the inverse laws because the swap makes `m(i x, x)` wind `⟨p + n, n + p⟩ ~ ⟨0, 0⟩`, the
inverse-homomorphism laws by pure `rfl`, and the congruences by the two winding-congruence lemmas.  All
arithmetic is propext-clean; no `Nat.sub`, no signed cancellation. -/
theorem abelianGroupTreeConv_sound {source target : AbelianGroupTree}
    (conv : AbelianGroupTreeConv source target) : windingEquiv (windingOf source) (windingOf target) := by
  induction conv with
  | assoc left middle right =>
      exact (congrArg (fun positivePart =>
              positivePart + ((windingOf left).inverseSlots
                + ((windingOf middle).inverseSlots + (windingOf right).inverseSlots)))
              (Nat.add_assoc (windingOf left).positiveSlots (windingOf middle).positiveSlots
                (windingOf right).positiveSlots)).trans
        (congrArg (fun inversePart =>
              ((windingOf left).positiveSlots
                + ((windingOf middle).positiveSlots + (windingOf right).positiveSlots)) + inversePart)
              (Nat.add_assoc (windingOf left).inverseSlots (windingOf middle).inverseSlots
                (windingOf right).inverseSlots).symm)
  | unitLeft subtree =>
      exact (congrArg (fun positivePart => positivePart + (windingOf subtree).inverseSlots)
              (natZeroAdd (windingOf subtree).positiveSlots)).trans
        (congrArg (fun inversePart => (windingOf subtree).positiveSlots + inversePart)
              (natZeroAdd (windingOf subtree).inverseSlots).symm)
  | unitRight subtree => exact rfl
  | commSwap left right =>
      exact (congrArg (fun positivePart =>
              positivePart + ((windingOf right).inverseSlots + (windingOf left).inverseSlots))
              (Nat.add_comm (windingOf left).positiveSlots (windingOf right).positiveSlots)).trans
        (congrArg (fun inversePart =>
              ((windingOf right).positiveSlots + (windingOf left).positiveSlots) + inversePart)
              (Nat.add_comm (windingOf right).inverseSlots (windingOf left).inverseSlots))
  | invLeft subtree =>
      exact ((Nat.add_zero ((windingOf subtree).inverseSlots + (windingOf subtree).positiveSlots)).trans
              (Nat.add_comm (windingOf subtree).inverseSlots (windingOf subtree).positiveSlots)).trans
        (natZeroAdd ((windingOf subtree).positiveSlots + (windingOf subtree).inverseSlots)).symm
  | invRight subtree =>
      exact ((Nat.add_zero ((windingOf subtree).positiveSlots + (windingOf subtree).inverseSlots)).trans
              (Nat.add_comm (windingOf subtree).positiveSlots (windingOf subtree).inverseSlots)).trans
        (natZeroAdd ((windingOf subtree).inverseSlots + (windingOf subtree).positiveSlots)).symm
  | invHom treeA treeB => exact rfl
  | invUnit => exact rfl
  | invInvol subtree => exact rfl
  | @mulCongr leftOld leftNew rightOld rightNew _ _ ihLeft ihRight =>
      exact windingEquivMulCongr ihLeft ihRight
  | @invCongr innerOld innerNew _ ihInner =>
      exact windingEquivInvCongr ihInner
  | refl tree => exact windingEquivRefl (windingOf tree)
  | symm _ ih => exact windingEquivSymm ih
  | trans _ _ ih1 ih2 => exact windingEquivTrans ih1 ih2

/-! ## Normalization: every tree reduces to an unreduced pair-form -/

/-- The **positive right-comb** of a given length: `combPos 0 = e` and `combPos (k+1) = m(leaf, combPos k)`,
the canonical `k`-slot positive tree. -/
def combPos : Nat → AbelianGroupTree
  | 0 => AbelianGroupTree.unitOp
  | Nat.succ predecessor => AbelianGroupTree.mulOp AbelianGroupTree.leaf (combPos predecessor)

/-- The **inverse right-comb** of a given length: `combNeg 0 = e` and `combNeg (k+1) = m(i leaf, combNeg k)`,
the canonical `k`-slot inverse tree. -/
def combNeg : Nat → AbelianGroupTree
  | 0 => AbelianGroupTree.unitOp
  | Nat.succ predecessor =>
      AbelianGroupTree.mulOp (AbelianGroupTree.invOp AbelianGroupTree.leaf) (combNeg predecessor)

/-- The **pair-form** normal shape `m(combPos p, combNeg n)` — an (unreduced) difference of `p` positive
slots and `n` inverse slots.  Its winding count is `⟨p, n⟩` and completeness pumps two pair-forms to a
common one. -/
def pairForm (positiveLength inverseLength : Nat) : AbelianGroupTree :=
  AbelianGroupTree.mulOp (combPos positiveLength) (combNeg inverseLength)

/-- A syntactic tree equality lifts to convertibility (via `Eq.rec`, propext-clean). -/
theorem convOfTreeEq {left right : AbelianGroupTree} (treeEq : left = right) :
    AbelianGroupTreeConv left right := by
  cases treeEq
  exact AbelianGroupTreeConv.refl left

/-- The **tree middle-four exchange** `m(m(A, B), m(C, D)) ≈ m(m(A, C), m(B, D))` — the associativity +
commutativity shuffle that regroups four subtrees, used by both the pair-form merge and the pump. -/
theorem convMiddleFour (treeA treeB treeC treeD : AbelianGroupTree) :
    AbelianGroupTreeConv
      (AbelianGroupTree.mulOp (AbelianGroupTree.mulOp treeA treeB) (AbelianGroupTree.mulOp treeC treeD))
      (AbelianGroupTree.mulOp (AbelianGroupTree.mulOp treeA treeC) (AbelianGroupTree.mulOp treeB treeD)) :=
  (AbelianGroupTreeConv.assoc treeA treeB (AbelianGroupTree.mulOp treeC treeD)).trans
    ((AbelianGroupTreeConv.mulCongr (AbelianGroupTreeConv.refl treeA)
        (AbelianGroupTreeConv.symm (AbelianGroupTreeConv.assoc treeB treeC treeD))).trans
      ((AbelianGroupTreeConv.mulCongr (AbelianGroupTreeConv.refl treeA)
          (AbelianGroupTreeConv.mulCongr (AbelianGroupTreeConv.commSwap treeB treeC)
            (AbelianGroupTreeConv.refl treeD))).trans
        ((AbelianGroupTreeConv.mulCongr (AbelianGroupTreeConv.refl treeA)
            (AbelianGroupTreeConv.assoc treeC treeB treeD)).trans
          (AbelianGroupTreeConv.symm
            (AbelianGroupTreeConv.assoc treeA treeC (AbelianGroupTree.mulOp treeB treeD))))))

/-- Grafting two positive combs concatenates them: `m(combPos a, combPos b) ≈ combPos (a + b)`.  Induction on
`b`; base by right unit, step slides `leaf` out with `commSwap` + `assoc`. -/
theorem combPosConcat (leftLength rightLength : Nat) :
    AbelianGroupTreeConv (AbelianGroupTree.mulOp (combPos leftLength) (combPos rightLength))
      (combPos (leftLength + rightLength)) := by
  induction rightLength with
  | zero => exact AbelianGroupTreeConv.unitRight (combPos leftLength)
  | succ predecessor ih =>
      exact (AbelianGroupTreeConv.symm
              (AbelianGroupTreeConv.assoc (combPos leftLength) AbelianGroupTree.leaf
                (combPos predecessor))).trans
        ((AbelianGroupTreeConv.mulCongr
            (AbelianGroupTreeConv.commSwap (combPos leftLength) AbelianGroupTree.leaf)
            (AbelianGroupTreeConv.refl (combPos predecessor))).trans
          ((AbelianGroupTreeConv.assoc AbelianGroupTree.leaf (combPos leftLength)
              (combPos predecessor)).trans
            (AbelianGroupTreeConv.mulCongr (AbelianGroupTreeConv.refl AbelianGroupTree.leaf) ih)))

/-- Grafting two inverse combs concatenates them: `m(combNeg a, combNeg b) ≈ combNeg (a + b)`.  Same shape as
`combPosConcat` with `i leaf` in place of `leaf`. -/
theorem combNegConcat (leftLength rightLength : Nat) :
    AbelianGroupTreeConv (AbelianGroupTree.mulOp (combNeg leftLength) (combNeg rightLength))
      (combNeg (leftLength + rightLength)) := by
  induction rightLength with
  | zero => exact AbelianGroupTreeConv.unitRight (combNeg leftLength)
  | succ predecessor ih =>
      exact (AbelianGroupTreeConv.symm
              (AbelianGroupTreeConv.assoc (combNeg leftLength)
                (AbelianGroupTree.invOp AbelianGroupTree.leaf) (combNeg predecessor))).trans
        ((AbelianGroupTreeConv.mulCongr
            (AbelianGroupTreeConv.commSwap (combNeg leftLength)
              (AbelianGroupTree.invOp AbelianGroupTree.leaf))
            (AbelianGroupTreeConv.refl (combNeg predecessor))).trans
          ((AbelianGroupTreeConv.assoc (AbelianGroupTree.invOp AbelianGroupTree.leaf) (combNeg leftLength)
              (combNeg predecessor)).trans
            (AbelianGroupTreeConv.mulCongr
              (AbelianGroupTreeConv.refl (AbelianGroupTree.invOp AbelianGroupTree.leaf)) ih)))

/-- **Pair-form merge** — a product of two pair-forms is a single pair-form with summed lengths:
`m(pairForm p₁ n₁, pairForm p₂ n₂) ≈ pairForm (p₁ + p₂) (n₁ + n₂)`.  The `convMiddleFour` shuffle gathers the
two positive combs and the two inverse combs, then `combPosConcat` / `combNegConcat` merge each side. -/
theorem pairFormMerge (positiveOne inverseOne positiveTwo inverseTwo : Nat) :
    AbelianGroupTreeConv
      (AbelianGroupTree.mulOp (pairForm positiveOne inverseOne) (pairForm positiveTwo inverseTwo))
      (pairForm (positiveOne + positiveTwo) (inverseOne + inverseTwo)) :=
  (convMiddleFour (combPos positiveOne) (combNeg inverseOne) (combPos positiveTwo) (combNeg inverseTwo)).trans
    (AbelianGroupTreeConv.mulCongr (combPosConcat positiveOne positiveTwo)
      (combNegConcat inverseOne inverseTwo))

/-- Pushing an inverse through a positive comb yields the inverse comb: `i(combPos k) ≈ combNeg k`.  Induction
on `k` via `invHom` / `invUnit`. -/
theorem invCombPos (combLength : Nat) :
    AbelianGroupTreeConv (AbelianGroupTree.invOp (combPos combLength)) (combNeg combLength) := by
  induction combLength with
  | zero => exact AbelianGroupTreeConv.invUnit
  | succ predecessor ih =>
      exact (AbelianGroupTreeConv.invHom AbelianGroupTree.leaf (combPos predecessor)).trans
        (AbelianGroupTreeConv.mulCongr
          (AbelianGroupTreeConv.refl (AbelianGroupTree.invOp AbelianGroupTree.leaf)) ih)

/-- Pushing an inverse through an inverse comb yields the positive comb: `i(combNeg k) ≈ combPos k`.  Induction
on `k` via `invHom` / `invInvol` / `invUnit`. -/
theorem invCombNeg (combLength : Nat) :
    AbelianGroupTreeConv (AbelianGroupTree.invOp (combNeg combLength)) (combPos combLength) := by
  induction combLength with
  | zero => exact AbelianGroupTreeConv.invUnit
  | succ predecessor ih =>
      exact (AbelianGroupTreeConv.invHom (AbelianGroupTree.invOp AbelianGroupTree.leaf)
              (combNeg predecessor)).trans
        (AbelianGroupTreeConv.mulCongr (AbelianGroupTreeConv.invInvol AbelianGroupTree.leaf) ih)

/-- **Inverting a pair-form swaps its lengths**: `i(pairForm p n) ≈ pairForm n p`.  Distribute the inverse
(`invHom`), turn each comb into the other kind (`invCombPos` / `invCombNeg`), and swap sides (`commSwap`). -/
theorem invPairFormSwap (positiveLength inverseLength : Nat) :
    AbelianGroupTreeConv (AbelianGroupTree.invOp (pairForm positiveLength inverseLength))
      (pairForm inverseLength positiveLength) :=
  (AbelianGroupTreeConv.invHom (combPos positiveLength) (combNeg inverseLength)).trans
    ((AbelianGroupTreeConv.mulCongr (invCombPos positiveLength) (invCombNeg inverseLength)).trans
      (AbelianGroupTreeConv.commSwap (combNeg positiveLength) (combPos inverseLength)))

/-- ★ **Normalization** — every tree is convertible to the pair-form of its own winding count.  Induction on
the tree: `leaf` and `unitOp` reduce to `pairForm 1 0` / `pairForm 0 0`; `invOp` inverts the child's pair-form
and swaps its lengths (`invPairFormSwap`); `mulOp` normalizes both children and merges (`pairFormMerge`). -/
theorem toPairFormConv (tree : AbelianGroupTree) :
    AbelianGroupTreeConv tree (pairForm (windingOf tree).positiveSlots (windingOf tree).inverseSlots) := by
  induction tree with
  | leaf =>
      exact ((AbelianGroupTreeConv.unitRight AbelianGroupTree.leaf).symm).trans
        (AbelianGroupTreeConv.unitRight
          (AbelianGroupTree.mulOp AbelianGroupTree.leaf AbelianGroupTree.unitOp)).symm
  | unitOp => exact (AbelianGroupTreeConv.unitLeft AbelianGroupTree.unitOp).symm
  | invOp inner ih =>
      exact (AbelianGroupTreeConv.invCongr ih).trans
        (invPairFormSwap (windingOf inner).positiveSlots (windingOf inner).inverseSlots)
  | mulOp left right ihLeft ihRight =>
      exact (AbelianGroupTreeConv.mulCongr ihLeft ihRight).trans
        (pairFormMerge (windingOf left).positiveSlots (windingOf left).inverseSlots
          (windingOf right).positiveSlots (windingOf right).inverseSlots)

/-! ## The pump and completeness -/

/-- **The pump** — a pair-form gains a cancelling positive/inverse slot pair: `pairForm p n ≈
pairForm (p+1) (n+1)`.  Read backwards: `pairForm (p+1) (n+1)` shuffles (`convMiddleFour`) its extra
`leaf` and `i leaf` together, they cancel (`invRight`), and the leftover unit is absorbed (`unitLeft`). -/
theorem pairFormPump (positiveLength inverseLength : Nat) :
    AbelianGroupTreeConv (pairForm positiveLength inverseLength)
      (pairForm (positiveLength + 1) (inverseLength + 1)) :=
  ((convMiddleFour AbelianGroupTree.leaf (combPos positiveLength)
        (AbelianGroupTree.invOp AbelianGroupTree.leaf) (combNeg inverseLength)).trans
      ((AbelianGroupTreeConv.mulCongr (AbelianGroupTreeConv.invRight AbelianGroupTree.leaf)
          (AbelianGroupTreeConv.refl
            (AbelianGroupTree.mulOp (combPos positiveLength) (combNeg inverseLength)))).trans
        (AbelianGroupTreeConv.unitLeft
          (AbelianGroupTree.mulOp (combPos positiveLength) (combNeg inverseLength))))).symm

/-- **Iterated pump** — `pairForm p n ≈ pairForm (p + steps) (n + steps)`.  Induction on `steps`. -/
theorem pairFormPumpN (positiveLength inverseLength steps : Nat) :
    AbelianGroupTreeConv (pairForm positiveLength inverseLength)
      (pairForm (positiveLength + steps) (inverseLength + steps)) := by
  induction steps with
  | zero => exact AbelianGroupTreeConv.refl (pairForm positiveLength inverseLength)
  | succ predecessor ih =>
      exact ih.trans (pairFormPump (positiveLength + predecessor) (inverseLength + predecessor))

/-- **Pair-forms with equivalent windings are convertible** — pump each up by the other's inverse length to a
common pair-form, then join.  The hypothesis `p₁ + n₂ = p₂ + n₁` is exactly `windingEquiv ⟨p₁,n₁⟩ ⟨p₂,n₂⟩`. -/
theorem pairFormEquivConv (positiveOne inverseOne positiveTwo inverseTwo : Nat)
    (windingHyp : positiveOne + inverseTwo = positiveTwo + inverseOne) :
    AbelianGroupTreeConv (pairForm positiveOne inverseOne) (pairForm positiveTwo inverseTwo) :=
  let pumpedOne := pairFormPumpN positiveOne inverseOne inverseTwo
  let pumpedTwo := pairFormPumpN positiveTwo inverseTwo inverseOne
  let commonEq :
      pairForm (positiveOne + inverseTwo) (inverseOne + inverseTwo)
        = pairForm (positiveTwo + inverseOne) (inverseTwo + inverseOne) :=
    (congrArg (fun positivePart => pairForm positivePart (inverseOne + inverseTwo)) windingHyp).trans
      (congrArg (fun inversePart => pairForm (positiveTwo + inverseOne) inversePart)
        (Nat.add_comm inverseOne inverseTwo))
  pumpedOne.trans ((convOfTreeEq commonEq).trans (AbelianGroupTreeConv.symm pumpedTwo))

/-- ★ **Completeness** — winding-equivalent trees are convertible.  Both trees normalize to the pair-form of
their winding count, and equivalent pair-forms are convertible (`pairFormEquivConv`), so they meet. -/
theorem abelianGroupTreeConv_complete {source target : AbelianGroupTree}
    (windingHyp : windingEquiv (windingOf source) (windingOf target)) :
    AbelianGroupTreeConv source target :=
  (toPairFormConv source).trans
    ((pairFormEquivConv (windingOf source).positiveSlots (windingOf source).inverseSlots
        (windingOf target).positiveSlots (windingOf target).inverseSlots windingHyp).trans
      (AbelianGroupTreeConv.symm (toPairFormConv target)))

/-! ## The decision -/

/-- ★ **The decision** — convertibility in the walking abelian group (single generator) is exactly winding
equivalence of the difference pairs, an additive `Nat` check.  Since `windingEquiv` is decidable (`Nat.decEq`),
this biconditional decides the word problem. -/
theorem abelianGroupTreeConv_iff_windingEquiv (source target : AbelianGroupTree) :
    AbelianGroupTreeConv source target ↔ windingEquiv (windingOf source) (windingOf target) :=
  ⟨abelianGroupTreeConv_sound, abelianGroupTreeConv_complete⟩

/-- ★ **The decider** — a shipped `Decidable` for the walking abelian group's convertibility, built from the
winding decision: match on `Nat.decEq` of the two winding-difference sums, discharging `isTrue` by
completeness and `isFalse` by soundness.  A genuine decider (not `decidable_of_iff`), propext-free. -/
def decideAbelianGroupTreeConv (source target : AbelianGroupTree) :
    Decidable (AbelianGroupTreeConv source target) :=
  match Nat.decEq ((windingOf source).positiveSlots + (windingOf target).inverseSlots)
                  ((windingOf target).positiveSlots + (windingOf source).inverseSlots) with
  | isTrue windingEq => isTrue (abelianGroupTreeConv_complete windingEq)
  | isFalse windingNe => isFalse (fun conv => windingNe (abelianGroupTreeConv_sound conv))

/-! ## Groundings -/

/-- ★ **The decision in action (positive)** — a cancelling insertion `m(m(leaf, i leaf), leaf)` is convertible
to `leaf`: both wind to the integer `+1` (winding pairs `⟨2, 1⟩` and `⟨1, 0⟩`, equivalent since `2 + 0 =
1 + 1`), so they are convertible through the completeness leg with no explicit rewrite path — the
inverse-cancellation the count-based walker cannot see. -/
theorem abelianGroupCancellationHolds :
    AbelianGroupTreeConv
      (AbelianGroupTree.mulOp
        (AbelianGroupTree.mulOp AbelianGroupTree.leaf (AbelianGroupTree.invOp AbelianGroupTree.leaf))
        AbelianGroupTree.leaf)
      AbelianGroupTree.leaf :=
  abelianGroupTreeConv_complete rfl

/-- ★ **The decision in action (negative)** — a slot is NOT convertible to the unit: their winding numbers
differ (`+1` vs `0`; `1 + 0 ≠ 0 + 0`), so by soundness no convertibility can exist.  `Nat.noConfusion`. -/
theorem abelianGroupRejectsLeafUnit :
    ¬ AbelianGroupTreeConv AbelianGroupTree.leaf AbelianGroupTree.unitOp :=
  fun conv => Nat.noConfusion (abelianGroupTreeConv_sound conv)

/-- ★ **The inverse does real work** — `i(m(leaf, leaf)) ≈ m(i leaf, i leaf)`: the inverse distributes over a
product (valid precisely because the group is abelian).  Both wind to the integer `-2` (pair `⟨0, 2⟩`). -/
theorem abelianGroupInverseDistributes :
    AbelianGroupTreeConv
      (AbelianGroupTree.invOp (AbelianGroupTree.mulOp AbelianGroupTree.leaf AbelianGroupTree.leaf))
      (AbelianGroupTree.mulOp (AbelianGroupTree.invOp AbelianGroupTree.leaf)
        (AbelianGroupTree.invOp AbelianGroupTree.leaf)) :=
  AbelianGroupTreeConv.invHom AbelianGroupTree.leaf AbelianGroupTree.leaf

/-! ## The marker -/

/-- ★ **The walking abelian group is DECIDED (single generator).**  `= true` records that
`abelianGroupTreeConv_iff_windingEquiv` reduces the word problem to winding equivalence of difference pairs —
adjoining a formal inverse completes the commutative monoid's `ℕ` count to the integers `ℤ`, presented as
`ℕ²/~` with no signed type and no subtraction.  The COLOURED (multi-generator) free abelian group `ℤᵏ` = free
ℤ-module, decided by a winding VECTOR, is the honest successor wall. -/
def fxWalkingAbelianGroup_hasSingleGeneratorDecision : Bool := true

end FX1Poly.Polygraph
