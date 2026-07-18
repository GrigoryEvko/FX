import FX1Poly.Polygraph.TwoCategory.WalkingAbelianGroup.AbelianGroupSeed

/-! # WalkingAbelianGroup/TwoColourAbelianGroupSeed — the walking (free) abelian group on TWO generating
slots = walking ℤ²: signature, tree convertibility, and the FULL two-colour decision

The successor rung named as the honest wall in the single-generator sibling (`AbelianGroupSeed`).  The free
**abelian group** on TWO generating input slots `a`, `b` is not `ℤ` but `ℤ²` — the free ℤ-module on `{a, b}`.
A tree's class is determined by the PAIR (a-winding number, b-winding number), each an integer presented — as
in the sibling — WITHOUT a signed type and WITHOUT subtraction, as a difference pair
`⟨positiveSlots, inverseSlots⟩ : ℕ²` under `windingEquiv`.  Because that pair of windings is a COMPLETE
invariant, the word problem is decided by a CONJUNCTION of two winding equivalences.

## ★ Why this walker is FULLY DECIDED (two generators)

The single-generator sibling reduced the word problem to one winding number; here there are two generator
kinds (`leafA`, `leafB`), so the invariant is a pair of windings held as TWO separate `WindingCount` folds
(`windingAOf`, `windingBOf`) — every equality stays a plain additive `Nat` equality, dodging any propext
hazard.  The colour-agnostic winding algebra (`WindingCount`, `windingEquiv`, `windingMul`, `windingInv`,
their equivalence + congruence lemmas, and the pure-`Nat` arithmetic kit) is REUSED verbatim from the
sibling; only the TREE-level lemmas — over this two-colour carrier — are re-derived.  This file ships:

* **soundness** — convertible trees have `windingEquiv` a-windings AND `windingEquiv` b-windings
  (`twoColourAbelianGroupConv_soundA`, `twoColourAbelianGroupConv_soundB`);
* **normalization** — every tree reduces to `normalFormOf`, the product of an a-coloured pair-form and a
  b-coloured pair-form of its two windings (`toNormalFormConv`), grafting two normal forms via `normalMerge`;
* **completeness** — `windingEquiv` a-windings and `windingEquiv` b-windings ⟹ convertible
  (`twoColourAbelianGroupConv_complete`);
* **the decision** — the convertibility ⟺ conjunction-of-winding-equivalences biconditional
  (`twoColourAbelianGroupConv_iff_windingEquiv`) plus a shipped `Decidable`.

## ★ The honest wall

The `k`-generator (arbitrary alphabet) free abelian group is `ℤᵏ` = the free ℤ-module on the generator SET: a
tree's class is a winding VECTOR indexed by the generators, decided by componentwise winding equivalence over
that whole finite index set rather than a fixed pair.  Two generators is the last case whose invariant is a
fixed finite tuple of windings; the alphabet-parameterised case needs an indexed winding vector and is the
successor rung — NOT attempted here.  This file is the two-generator instance (= walking ℤ²), complete.

Raw Lean 4 + Init; the convertibility is an inductive `Prop`; per-declaration `#assert_no_axioms` gated in the
audit twin.  Free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`, `Nat.sub` — the
only arithmetic used is `Nat.add_comm` / `Nat.add_assoc` / `Nat.add_zero` (plus the reused sibling kit), all
propext-clean. -/

namespace FX1Poly.Polygraph

/-! ## The two-colour abelian-group tree carrier -/

/-- ★ The **tree carrier** of the walking abelian group on TWO generating slots: an un-indexed tree over the
two generators `a`, `b` plus the `{m, e, i}` group signature.  `leafA` and `leafB` are the two arity-1 input
slots; `unitOp` is the nullary generator `e`; `invOp` applies the unary inverse `i`; `mulOp` grafts two
subtrees under the binary generator `m`.  A closed tree's PAIR of winding numbers (its a-winding and
b-winding) is its complete convertibility invariant. -/
inductive TwoColourAbelianGroupTree where
  /-- The first arity-1 input slot — the `a` generator. -/
  | leafA
  /-- The second arity-1 input slot — the `b` generator. -/
  | leafB
  /-- The nullary generator `e : arity 0` (the group unit). -/
  | unitOp
  /-- The unary generator `i : arity 1` (the group inverse) applied to a subtree. -/
  | invOp : TwoColourAbelianGroupTree → TwoColourAbelianGroupTree
  /-- The binary generator `m : arity 2` grafting the left and right subtrees (`m(left, right)`). -/
  | mulOp : TwoColourAbelianGroupTree → TwoColourAbelianGroupTree → TwoColourAbelianGroupTree

/-! ## The two winding invariants (each a difference pair ℕ² presenting ℤ, reusing the sibling algebra) -/

/-- The **a-winding count** of a tree — the winding number of the `a` generator, a difference pair reusing the
sibling `WindingCount`.  `leafA ↦ ⟨1, 0⟩`, `leafB ↦ ⟨0, 0⟩`, `unitOp ↦ ⟨0, 0⟩`, `invOp` SWAPS via
`windingInv`, `mulOp` adds via `windingMul`.  Full-enumeration structural fold, propext-clean. -/
def windingAOf : TwoColourAbelianGroupTree → WindingCount
  | .leafA => ⟨1, 0⟩
  | .leafB => ⟨0, 0⟩
  | .unitOp => ⟨0, 0⟩
  | .invOp inner => windingInv (windingAOf inner)
  | .mulOp left right => windingMul (windingAOf left) (windingAOf right)

/-- The **b-winding count** of a tree — the winding number of the `b` generator.  `leafB ↦ ⟨1, 0⟩`,
`leafA ↦ ⟨0, 0⟩`, otherwise mirroring `windingAOf` (`invOp` swaps, `mulOp` adds). -/
def windingBOf : TwoColourAbelianGroupTree → WindingCount
  | .leafA => ⟨0, 0⟩
  | .leafB => ⟨1, 0⟩
  | .unitOp => ⟨0, 0⟩
  | .invOp inner => windingInv (windingBOf inner)
  | .mulOp left right => windingMul (windingBOf left) (windingBOf right)

/-- Smoke: a single `a`-slot has a-winding `⟨1, 0⟩`. -/
theorem windingAOf_leafA : windingAOf TwoColourAbelianGroupTree.leafA = ⟨1, 0⟩ := rfl

/-- Smoke: a single `a`-slot has b-winding `⟨0, 0⟩` (it is `b`-invisible). -/
theorem windingBOf_leafA : windingBOf TwoColourAbelianGroupTree.leafA = ⟨0, 0⟩ := rfl

/-- Smoke: an inverted `a`-slot has a-winding `⟨0, 1⟩` — the inverse swaps the difference pair. -/
theorem windingAOf_invLeafA :
    windingAOf (TwoColourAbelianGroupTree.invOp TwoColourAbelianGroupTree.leafA) = ⟨0, 1⟩ := rfl

/-! ## The two-colour abelian-group tree convertibility -/

/-- ★ The **tree convertibility** of the walking abelian group on two generators — the free convertibility of
the `{m, e, i}` signature over the two generators closed under the abelian-group laws (associativity,
left/right unit, commutativity, left/right inverse, and the inverse-homomorphism laws), the full congruences
`mulCongr` / `invCongr`, and `refl` / `symm` / `trans`.  Same shapes as the single-generator sibling over the
two-generator carrier.  Two trees denote the same element of the free abelian group on `{a, b}` exactly when
they are `TwoColourAbelianGroupTreeConv`-related. -/
inductive TwoColourAbelianGroupTreeConv : TwoColourAbelianGroupTree → TwoColourAbelianGroupTree → Prop where
  /-- **Associativity** `m(m(left, middle), right) ≈ m(left, m(middle, right))`. -/
  | assoc (left middle right : TwoColourAbelianGroupTree) :
      TwoColourAbelianGroupTreeConv
        (TwoColourAbelianGroupTree.mulOp (TwoColourAbelianGroupTree.mulOp left middle) right)
        (TwoColourAbelianGroupTree.mulOp left (TwoColourAbelianGroupTree.mulOp middle right))
  /-- **Left unit** `m(e, subtree) ≈ subtree`. -/
  | unitLeft (subtree : TwoColourAbelianGroupTree) :
      TwoColourAbelianGroupTreeConv (TwoColourAbelianGroupTree.mulOp TwoColourAbelianGroupTree.unitOp subtree)
        subtree
  /-- **Right unit** `m(subtree, e) ≈ subtree`. -/
  | unitRight (subtree : TwoColourAbelianGroupTree) :
      TwoColourAbelianGroupTreeConv (TwoColourAbelianGroupTree.mulOp subtree TwoColourAbelianGroupTree.unitOp)
        subtree
  /-- **Commutativity** `m(left, right) ≈ m(right, left)` — mixing the two colours freely. -/
  | commSwap (left right : TwoColourAbelianGroupTree) :
      TwoColourAbelianGroupTreeConv (TwoColourAbelianGroupTree.mulOp left right)
        (TwoColourAbelianGroupTree.mulOp right left)
  /-- **Left inverse** `m(i subtree, subtree) ≈ e`. -/
  | invLeft (subtree : TwoColourAbelianGroupTree) :
      TwoColourAbelianGroupTreeConv
        (TwoColourAbelianGroupTree.mulOp (TwoColourAbelianGroupTree.invOp subtree) subtree)
        TwoColourAbelianGroupTree.unitOp
  /-- **Right inverse** `m(subtree, i subtree) ≈ e`. -/
  | invRight (subtree : TwoColourAbelianGroupTree) :
      TwoColourAbelianGroupTreeConv
        (TwoColourAbelianGroupTree.mulOp subtree (TwoColourAbelianGroupTree.invOp subtree))
        TwoColourAbelianGroupTree.unitOp
  /-- **Inverse homomorphism** `i(m(treeA, treeB)) ≈ m(i treeA, i treeB)` (valid because the group is
  abelian, so the inverse distributes without reversing order). -/
  | invHom (treeA treeB : TwoColourAbelianGroupTree) :
      TwoColourAbelianGroupTreeConv (TwoColourAbelianGroupTree.invOp (TwoColourAbelianGroupTree.mulOp treeA treeB))
        (TwoColourAbelianGroupTree.mulOp (TwoColourAbelianGroupTree.invOp treeA)
          (TwoColourAbelianGroupTree.invOp treeB))
  /-- **Inverse of unit** `i e ≈ e`. -/
  | invUnit :
      TwoColourAbelianGroupTreeConv (TwoColourAbelianGroupTree.invOp TwoColourAbelianGroupTree.unitOp)
        TwoColourAbelianGroupTree.unitOp
  /-- **Inverse involution** `i(i subtree) ≈ subtree`. -/
  | invInvol (subtree : TwoColourAbelianGroupTree) :
      TwoColourAbelianGroupTreeConv
        (TwoColourAbelianGroupTree.invOp (TwoColourAbelianGroupTree.invOp subtree)) subtree
  /-- **Congruence under a grafting node** — into BOTH children. -/
  | mulCongr {leftOld leftNew rightOld rightNew : TwoColourAbelianGroupTree} :
      TwoColourAbelianGroupTreeConv leftOld leftNew → TwoColourAbelianGroupTreeConv rightOld rightNew →
      TwoColourAbelianGroupTreeConv (TwoColourAbelianGroupTree.mulOp leftOld rightOld)
        (TwoColourAbelianGroupTree.mulOp leftNew rightNew)
  /-- **Congruence under an inverse node**. -/
  | invCongr {innerOld innerNew : TwoColourAbelianGroupTree} :
      TwoColourAbelianGroupTreeConv innerOld innerNew →
      TwoColourAbelianGroupTreeConv (TwoColourAbelianGroupTree.invOp innerOld)
        (TwoColourAbelianGroupTree.invOp innerNew)
  /-- Reflexivity. -/
  | refl (tree : TwoColourAbelianGroupTree) : TwoColourAbelianGroupTreeConv tree tree
  /-- Symmetry. -/
  | symm {tree1 tree2 : TwoColourAbelianGroupTree} :
      TwoColourAbelianGroupTreeConv tree1 tree2 → TwoColourAbelianGroupTreeConv tree2 tree1
  /-- Transitivity. -/
  | trans {tree1 tree2 tree3 : TwoColourAbelianGroupTree} :
      TwoColourAbelianGroupTreeConv tree1 tree2 → TwoColourAbelianGroupTreeConv tree2 tree3 →
      TwoColourAbelianGroupTreeConv tree1 tree3

/-! ## Soundness: convertible ⟹ winding-equivalent (per colour) -/

/-- ★ **Soundness, a-component** — convertible trees have `windingEquiv` a-windings.  Every law preserves the
difference pair: the (co)unit / associativity / commutativity laws by `Nat.add_comm` / `add_assoc` /
`add_zero` (via the reused `natZeroAdd`), the inverse laws because the swap makes `m(i x, x)` wind
`⟨p + n, n + p⟩ ~ ⟨0, 0⟩`, the inverse-homomorphism laws by pure `rfl`, and the congruences by the reused
winding-congruence lemmas.  All arithmetic is propext-clean; no `Nat.sub`. -/
theorem twoColourAbelianGroupConv_soundA {source target : TwoColourAbelianGroupTree}
    (conv : TwoColourAbelianGroupTreeConv source target) :
    windingEquiv (windingAOf source) (windingAOf target) := by
  induction conv with
  | assoc left middle right =>
      exact (congrArg (fun positivePart =>
              positivePart + ((windingAOf left).inverseSlots
                + ((windingAOf middle).inverseSlots + (windingAOf right).inverseSlots)))
              (Nat.add_assoc (windingAOf left).positiveSlots (windingAOf middle).positiveSlots
                (windingAOf right).positiveSlots)).trans
        (congrArg (fun inversePart =>
              ((windingAOf left).positiveSlots
                + ((windingAOf middle).positiveSlots + (windingAOf right).positiveSlots)) + inversePart)
              (Nat.add_assoc (windingAOf left).inverseSlots (windingAOf middle).inverseSlots
                (windingAOf right).inverseSlots).symm)
  | unitLeft subtree =>
      exact (congrArg (fun positivePart => positivePart + (windingAOf subtree).inverseSlots)
              (natZeroAdd (windingAOf subtree).positiveSlots)).trans
        (congrArg (fun inversePart => (windingAOf subtree).positiveSlots + inversePart)
              (natZeroAdd (windingAOf subtree).inverseSlots).symm)
  | unitRight subtree => exact rfl
  | commSwap left right =>
      exact (congrArg (fun positivePart =>
              positivePart + ((windingAOf right).inverseSlots + (windingAOf left).inverseSlots))
              (Nat.add_comm (windingAOf left).positiveSlots (windingAOf right).positiveSlots)).trans
        (congrArg (fun inversePart =>
              ((windingAOf right).positiveSlots + (windingAOf left).positiveSlots) + inversePart)
              (Nat.add_comm (windingAOf right).inverseSlots (windingAOf left).inverseSlots))
  | invLeft subtree =>
      exact ((Nat.add_zero ((windingAOf subtree).inverseSlots + (windingAOf subtree).positiveSlots)).trans
              (Nat.add_comm (windingAOf subtree).inverseSlots (windingAOf subtree).positiveSlots)).trans
        (natZeroAdd ((windingAOf subtree).positiveSlots + (windingAOf subtree).inverseSlots)).symm
  | invRight subtree =>
      exact ((Nat.add_zero ((windingAOf subtree).positiveSlots + (windingAOf subtree).inverseSlots)).trans
              (Nat.add_comm (windingAOf subtree).positiveSlots (windingAOf subtree).inverseSlots)).trans
        (natZeroAdd ((windingAOf subtree).inverseSlots + (windingAOf subtree).positiveSlots)).symm
  | invHom treeA treeB => exact rfl
  | invUnit => exact rfl
  | invInvol subtree => exact rfl
  | @mulCongr leftOld leftNew rightOld rightNew _ _ ihLeft ihRight =>
      exact windingEquivMulCongr ihLeft ihRight
  | @invCongr innerOld innerNew _ ihInner =>
      exact windingEquivInvCongr ihInner
  | refl tree => exact windingEquivRefl (windingAOf tree)
  | symm _ ih => exact windingEquivSymm ih
  | trans _ _ ih1 ih2 => exact windingEquivTrans ih1 ih2

/-- ★ **Soundness, b-component** — convertible trees have `windingEquiv` b-windings.  Identical in shape to
the a-component, over `windingBOf`. -/
theorem twoColourAbelianGroupConv_soundB {source target : TwoColourAbelianGroupTree}
    (conv : TwoColourAbelianGroupTreeConv source target) :
    windingEquiv (windingBOf source) (windingBOf target) := by
  induction conv with
  | assoc left middle right =>
      exact (congrArg (fun positivePart =>
              positivePart + ((windingBOf left).inverseSlots
                + ((windingBOf middle).inverseSlots + (windingBOf right).inverseSlots)))
              (Nat.add_assoc (windingBOf left).positiveSlots (windingBOf middle).positiveSlots
                (windingBOf right).positiveSlots)).trans
        (congrArg (fun inversePart =>
              ((windingBOf left).positiveSlots
                + ((windingBOf middle).positiveSlots + (windingBOf right).positiveSlots)) + inversePart)
              (Nat.add_assoc (windingBOf left).inverseSlots (windingBOf middle).inverseSlots
                (windingBOf right).inverseSlots).symm)
  | unitLeft subtree =>
      exact (congrArg (fun positivePart => positivePart + (windingBOf subtree).inverseSlots)
              (natZeroAdd (windingBOf subtree).positiveSlots)).trans
        (congrArg (fun inversePart => (windingBOf subtree).positiveSlots + inversePart)
              (natZeroAdd (windingBOf subtree).inverseSlots).symm)
  | unitRight subtree => exact rfl
  | commSwap left right =>
      exact (congrArg (fun positivePart =>
              positivePart + ((windingBOf right).inverseSlots + (windingBOf left).inverseSlots))
              (Nat.add_comm (windingBOf left).positiveSlots (windingBOf right).positiveSlots)).trans
        (congrArg (fun inversePart =>
              ((windingBOf right).positiveSlots + (windingBOf left).positiveSlots) + inversePart)
              (Nat.add_comm (windingBOf right).inverseSlots (windingBOf left).inverseSlots))
  | invLeft subtree =>
      exact ((Nat.add_zero ((windingBOf subtree).inverseSlots + (windingBOf subtree).positiveSlots)).trans
              (Nat.add_comm (windingBOf subtree).inverseSlots (windingBOf subtree).positiveSlots)).trans
        (natZeroAdd ((windingBOf subtree).positiveSlots + (windingBOf subtree).inverseSlots)).symm
  | invRight subtree =>
      exact ((Nat.add_zero ((windingBOf subtree).positiveSlots + (windingBOf subtree).inverseSlots)).trans
              (Nat.add_comm (windingBOf subtree).positiveSlots (windingBOf subtree).inverseSlots)).trans
        (natZeroAdd ((windingBOf subtree).inverseSlots + (windingBOf subtree).positiveSlots)).symm
  | invHom treeA treeB => exact rfl
  | invUnit => exact rfl
  | invInvol subtree => exact rfl
  | @mulCongr leftOld leftNew rightOld rightNew _ _ ihLeft ihRight =>
      exact windingEquivMulCongr ihLeft ihRight
  | @invCongr innerOld innerNew _ ihInner =>
      exact windingEquivInvCongr ihInner
  | refl tree => exact windingEquivRefl (windingBOf tree)
  | symm _ ih => exact windingEquivSymm ih
  | trans _ _ ih1 ih2 => exact windingEquivTrans ih1 ih2

/-! ## Four comb families: positive / inverse right-combs, one pair per colour -/

/-- The **positive a-comb** of a given length: `combPosA 0 = e` and `combPosA (k+1) = m(leafA, combPosA k)`,
the canonical `k`-slot positive `a`-tree. -/
def combPosA : Nat → TwoColourAbelianGroupTree
  | 0 => TwoColourAbelianGroupTree.unitOp
  | Nat.succ predecessor => TwoColourAbelianGroupTree.mulOp TwoColourAbelianGroupTree.leafA (combPosA predecessor)

/-- The **inverse a-comb** of a given length: `combNegA 0 = e` and
`combNegA (k+1) = m(i leafA, combNegA k)`, the canonical `k`-slot inverse `a`-tree. -/
def combNegA : Nat → TwoColourAbelianGroupTree
  | 0 => TwoColourAbelianGroupTree.unitOp
  | Nat.succ predecessor =>
      TwoColourAbelianGroupTree.mulOp (TwoColourAbelianGroupTree.invOp TwoColourAbelianGroupTree.leafA)
        (combNegA predecessor)

/-- The **positive b-comb** of a given length: `combPosB 0 = e` and
`combPosB (k+1) = m(leafB, combPosB k)`, the canonical `k`-slot positive `b`-tree. -/
def combPosB : Nat → TwoColourAbelianGroupTree
  | 0 => TwoColourAbelianGroupTree.unitOp
  | Nat.succ predecessor => TwoColourAbelianGroupTree.mulOp TwoColourAbelianGroupTree.leafB (combPosB predecessor)

/-- The **inverse b-comb** of a given length: `combNegB 0 = e` and
`combNegB (k+1) = m(i leafB, combNegB k)`, the canonical `k`-slot inverse `b`-tree. -/
def combNegB : Nat → TwoColourAbelianGroupTree
  | 0 => TwoColourAbelianGroupTree.unitOp
  | Nat.succ predecessor =>
      TwoColourAbelianGroupTree.mulOp (TwoColourAbelianGroupTree.invOp TwoColourAbelianGroupTree.leafB)
        (combNegB predecessor)

/-! ## Per-colour pair-forms and the full two-colour normal form -/

/-- The **a-pair-form** `m(combPosA p, combNegA n)` — an (unreduced) difference of `p` positive and `n`
inverse `a`-slots.  Its a-winding is `⟨p, n⟩` and its b-winding is `⟨0, 0⟩`. -/
def pairFormA (positiveLength inverseLength : Nat) : TwoColourAbelianGroupTree :=
  TwoColourAbelianGroupTree.mulOp (combPosA positiveLength) (combNegA inverseLength)

/-- The **b-pair-form** `m(combPosB p, combNegB n)` — an (unreduced) difference of `p` positive and `n`
inverse `b`-slots.  Its b-winding is `⟨p, n⟩` and its a-winding is `⟨0, 0⟩`. -/
def pairFormB (positiveLength inverseLength : Nat) : TwoColourAbelianGroupTree :=
  TwoColourAbelianGroupTree.mulOp (combPosB positiveLength) (combNegB inverseLength)

/-- The **two-colour normal form** of a pair of windings: the product of the a-pair-form of the a-winding and
the b-pair-form of the b-winding.  Its a-winding is `aWinding` and its b-winding is `bWinding`, so it is the
canonical representative of the element `(aWinding, bWinding) ∈ ℤ²`. -/
def normalFormOf (aWinding bWinding : WindingCount) : TwoColourAbelianGroupTree :=
  TwoColourAbelianGroupTree.mulOp
    (pairFormA aWinding.positiveSlots aWinding.inverseSlots)
    (pairFormB bWinding.positiveSlots bWinding.inverseSlots)

/-- A syntactic tree equality lifts to convertibility (via `Eq.rec`, propext-clean).  Carrier-specific name to
avoid clashing with the single-generator sibling's `convOfTreeEq` in the shared namespace. -/
theorem twoColourConvOfTreeEq {left right : TwoColourAbelianGroupTree} (treeEq : left = right) :
    TwoColourAbelianGroupTreeConv left right := by
  cases treeEq
  exact TwoColourAbelianGroupTreeConv.refl left

/-- The **tree middle-four exchange** `m(m(A, B), m(C, D)) ≈ m(m(A, C), m(B, D))` — the associativity +
commutativity shuffle that regroups four subtrees, used by both pair-form merges and the normal merge.
Carrier-specific name to avoid clashing with the single-generator sibling's `convMiddleFour`. -/
theorem twoColourConvMiddleFour (treeA treeB treeC treeD : TwoColourAbelianGroupTree) :
    TwoColourAbelianGroupTreeConv
      (TwoColourAbelianGroupTree.mulOp (TwoColourAbelianGroupTree.mulOp treeA treeB)
        (TwoColourAbelianGroupTree.mulOp treeC treeD))
      (TwoColourAbelianGroupTree.mulOp (TwoColourAbelianGroupTree.mulOp treeA treeC)
        (TwoColourAbelianGroupTree.mulOp treeB treeD)) :=
  (TwoColourAbelianGroupTreeConv.assoc treeA treeB (TwoColourAbelianGroupTree.mulOp treeC treeD)).trans
    ((TwoColourAbelianGroupTreeConv.mulCongr (TwoColourAbelianGroupTreeConv.refl treeA)
        (TwoColourAbelianGroupTreeConv.symm (TwoColourAbelianGroupTreeConv.assoc treeB treeC treeD))).trans
      ((TwoColourAbelianGroupTreeConv.mulCongr (TwoColourAbelianGroupTreeConv.refl treeA)
          (TwoColourAbelianGroupTreeConv.mulCongr (TwoColourAbelianGroupTreeConv.commSwap treeB treeC)
            (TwoColourAbelianGroupTreeConv.refl treeD))).trans
        ((TwoColourAbelianGroupTreeConv.mulCongr (TwoColourAbelianGroupTreeConv.refl treeA)
            (TwoColourAbelianGroupTreeConv.assoc treeC treeB treeD)).trans
          (TwoColourAbelianGroupTreeConv.symm
            (TwoColourAbelianGroupTreeConv.assoc treeA treeC (TwoColourAbelianGroupTree.mulOp treeB treeD))))))

/-! ## The four comb-concatenation lemmas -/

/-- Grafting two positive a-combs concatenates them: `m(combPosA a, combPosA b) ≈ combPosA (a + b)`. -/
theorem combPosAConcat (leftLength rightLength : Nat) :
    TwoColourAbelianGroupTreeConv (TwoColourAbelianGroupTree.mulOp (combPosA leftLength) (combPosA rightLength))
      (combPosA (leftLength + rightLength)) := by
  induction rightLength with
  | zero => exact TwoColourAbelianGroupTreeConv.unitRight (combPosA leftLength)
  | succ predecessor ih =>
      exact (TwoColourAbelianGroupTreeConv.symm
              (TwoColourAbelianGroupTreeConv.assoc (combPosA leftLength) TwoColourAbelianGroupTree.leafA
                (combPosA predecessor))).trans
        ((TwoColourAbelianGroupTreeConv.mulCongr
            (TwoColourAbelianGroupTreeConv.commSwap (combPosA leftLength) TwoColourAbelianGroupTree.leafA)
            (TwoColourAbelianGroupTreeConv.refl (combPosA predecessor))).trans
          ((TwoColourAbelianGroupTreeConv.assoc TwoColourAbelianGroupTree.leafA (combPosA leftLength)
              (combPosA predecessor)).trans
            (TwoColourAbelianGroupTreeConv.mulCongr (TwoColourAbelianGroupTreeConv.refl TwoColourAbelianGroupTree.leafA) ih)))

/-- Grafting two inverse a-combs concatenates them: `m(combNegA a, combNegA b) ≈ combNegA (a + b)`. -/
theorem combNegAConcat (leftLength rightLength : Nat) :
    TwoColourAbelianGroupTreeConv (TwoColourAbelianGroupTree.mulOp (combNegA leftLength) (combNegA rightLength))
      (combNegA (leftLength + rightLength)) := by
  induction rightLength with
  | zero => exact TwoColourAbelianGroupTreeConv.unitRight (combNegA leftLength)
  | succ predecessor ih =>
      exact (TwoColourAbelianGroupTreeConv.symm
              (TwoColourAbelianGroupTreeConv.assoc (combNegA leftLength)
                (TwoColourAbelianGroupTree.invOp TwoColourAbelianGroupTree.leafA) (combNegA predecessor))).trans
        ((TwoColourAbelianGroupTreeConv.mulCongr
            (TwoColourAbelianGroupTreeConv.commSwap (combNegA leftLength)
              (TwoColourAbelianGroupTree.invOp TwoColourAbelianGroupTree.leafA))
            (TwoColourAbelianGroupTreeConv.refl (combNegA predecessor))).trans
          ((TwoColourAbelianGroupTreeConv.assoc (TwoColourAbelianGroupTree.invOp TwoColourAbelianGroupTree.leafA)
              (combNegA leftLength) (combNegA predecessor)).trans
            (TwoColourAbelianGroupTreeConv.mulCongr
              (TwoColourAbelianGroupTreeConv.refl (TwoColourAbelianGroupTree.invOp TwoColourAbelianGroupTree.leafA)) ih)))

/-- Grafting two positive b-combs concatenates them: `m(combPosB a, combPosB b) ≈ combPosB (a + b)`. -/
theorem combPosBConcat (leftLength rightLength : Nat) :
    TwoColourAbelianGroupTreeConv (TwoColourAbelianGroupTree.mulOp (combPosB leftLength) (combPosB rightLength))
      (combPosB (leftLength + rightLength)) := by
  induction rightLength with
  | zero => exact TwoColourAbelianGroupTreeConv.unitRight (combPosB leftLength)
  | succ predecessor ih =>
      exact (TwoColourAbelianGroupTreeConv.symm
              (TwoColourAbelianGroupTreeConv.assoc (combPosB leftLength) TwoColourAbelianGroupTree.leafB
                (combPosB predecessor))).trans
        ((TwoColourAbelianGroupTreeConv.mulCongr
            (TwoColourAbelianGroupTreeConv.commSwap (combPosB leftLength) TwoColourAbelianGroupTree.leafB)
            (TwoColourAbelianGroupTreeConv.refl (combPosB predecessor))).trans
          ((TwoColourAbelianGroupTreeConv.assoc TwoColourAbelianGroupTree.leafB (combPosB leftLength)
              (combPosB predecessor)).trans
            (TwoColourAbelianGroupTreeConv.mulCongr (TwoColourAbelianGroupTreeConv.refl TwoColourAbelianGroupTree.leafB) ih)))

/-- Grafting two inverse b-combs concatenates them: `m(combNegB a, combNegB b) ≈ combNegB (a + b)`. -/
theorem combNegBConcat (leftLength rightLength : Nat) :
    TwoColourAbelianGroupTreeConv (TwoColourAbelianGroupTree.mulOp (combNegB leftLength) (combNegB rightLength))
      (combNegB (leftLength + rightLength)) := by
  induction rightLength with
  | zero => exact TwoColourAbelianGroupTreeConv.unitRight (combNegB leftLength)
  | succ predecessor ih =>
      exact (TwoColourAbelianGroupTreeConv.symm
              (TwoColourAbelianGroupTreeConv.assoc (combNegB leftLength)
                (TwoColourAbelianGroupTree.invOp TwoColourAbelianGroupTree.leafB) (combNegB predecessor))).trans
        ((TwoColourAbelianGroupTreeConv.mulCongr
            (TwoColourAbelianGroupTreeConv.commSwap (combNegB leftLength)
              (TwoColourAbelianGroupTree.invOp TwoColourAbelianGroupTree.leafB))
            (TwoColourAbelianGroupTreeConv.refl (combNegB predecessor))).trans
          ((TwoColourAbelianGroupTreeConv.assoc (TwoColourAbelianGroupTree.invOp TwoColourAbelianGroupTree.leafB)
              (combNegB leftLength) (combNegB predecessor)).trans
            (TwoColourAbelianGroupTreeConv.mulCongr
              (TwoColourAbelianGroupTreeConv.refl (TwoColourAbelianGroupTree.invOp TwoColourAbelianGroupTree.leafB)) ih)))

/-! ## The two per-colour pair-form merges -/

/-- **a-pair-form merge** — a product of two a-pair-forms is a single a-pair-form with summed lengths:
`m(pairFormA p₁ n₁, pairFormA p₂ n₂) ≈ pairFormA (p₁ + p₂) (n₁ + n₂)`. -/
theorem pairFormAMerge (positiveOne inverseOne positiveTwo inverseTwo : Nat) :
    TwoColourAbelianGroupTreeConv
      (TwoColourAbelianGroupTree.mulOp (pairFormA positiveOne inverseOne) (pairFormA positiveTwo inverseTwo))
      (pairFormA (positiveOne + positiveTwo) (inverseOne + inverseTwo)) :=
  (twoColourConvMiddleFour (combPosA positiveOne) (combNegA inverseOne) (combPosA positiveTwo)
      (combNegA inverseTwo)).trans
    (TwoColourAbelianGroupTreeConv.mulCongr (combPosAConcat positiveOne positiveTwo)
      (combNegAConcat inverseOne inverseTwo))

/-- **b-pair-form merge** — a product of two b-pair-forms is a single b-pair-form with summed lengths:
`m(pairFormB p₁ n₁, pairFormB p₂ n₂) ≈ pairFormB (p₁ + p₂) (n₁ + n₂)`. -/
theorem pairFormBMerge (positiveOne inverseOne positiveTwo inverseTwo : Nat) :
    TwoColourAbelianGroupTreeConv
      (TwoColourAbelianGroupTree.mulOp (pairFormB positiveOne inverseOne) (pairFormB positiveTwo inverseTwo))
      (pairFormB (positiveOne + positiveTwo) (inverseOne + inverseTwo)) :=
  (twoColourConvMiddleFour (combPosB positiveOne) (combNegB inverseOne) (combPosB positiveTwo)
      (combNegB inverseTwo)).trans
    (TwoColourAbelianGroupTreeConv.mulCongr (combPosBConcat positiveOne positiveTwo)
      (combNegBConcat inverseOne inverseTwo))

/-! ## The four inverse-push lemmas and the two pair-form inverse-swaps -/

/-- Pushing an inverse through a positive a-comb yields the inverse a-comb: `i(combPosA k) ≈ combNegA k`. -/
theorem invCombPosA (combLength : Nat) :
    TwoColourAbelianGroupTreeConv (TwoColourAbelianGroupTree.invOp (combPosA combLength)) (combNegA combLength) := by
  induction combLength with
  | zero => exact TwoColourAbelianGroupTreeConv.invUnit
  | succ predecessor ih =>
      exact (TwoColourAbelianGroupTreeConv.invHom TwoColourAbelianGroupTree.leafA (combPosA predecessor)).trans
        (TwoColourAbelianGroupTreeConv.mulCongr
          (TwoColourAbelianGroupTreeConv.refl (TwoColourAbelianGroupTree.invOp TwoColourAbelianGroupTree.leafA)) ih)

/-- Pushing an inverse through an inverse a-comb yields the positive a-comb: `i(combNegA k) ≈ combPosA k`. -/
theorem invCombNegA (combLength : Nat) :
    TwoColourAbelianGroupTreeConv (TwoColourAbelianGroupTree.invOp (combNegA combLength)) (combPosA combLength) := by
  induction combLength with
  | zero => exact TwoColourAbelianGroupTreeConv.invUnit
  | succ predecessor ih =>
      exact (TwoColourAbelianGroupTreeConv.invHom (TwoColourAbelianGroupTree.invOp TwoColourAbelianGroupTree.leafA)
              (combNegA predecessor)).trans
        (TwoColourAbelianGroupTreeConv.mulCongr (TwoColourAbelianGroupTreeConv.invInvol TwoColourAbelianGroupTree.leafA) ih)

/-- Pushing an inverse through a positive b-comb yields the inverse b-comb: `i(combPosB k) ≈ combNegB k`. -/
theorem invCombPosB (combLength : Nat) :
    TwoColourAbelianGroupTreeConv (TwoColourAbelianGroupTree.invOp (combPosB combLength)) (combNegB combLength) := by
  induction combLength with
  | zero => exact TwoColourAbelianGroupTreeConv.invUnit
  | succ predecessor ih =>
      exact (TwoColourAbelianGroupTreeConv.invHom TwoColourAbelianGroupTree.leafB (combPosB predecessor)).trans
        (TwoColourAbelianGroupTreeConv.mulCongr
          (TwoColourAbelianGroupTreeConv.refl (TwoColourAbelianGroupTree.invOp TwoColourAbelianGroupTree.leafB)) ih)

/-- Pushing an inverse through an inverse b-comb yields the positive b-comb: `i(combNegB k) ≈ combPosB k`. -/
theorem invCombNegB (combLength : Nat) :
    TwoColourAbelianGroupTreeConv (TwoColourAbelianGroupTree.invOp (combNegB combLength)) (combPosB combLength) := by
  induction combLength with
  | zero => exact TwoColourAbelianGroupTreeConv.invUnit
  | succ predecessor ih =>
      exact (TwoColourAbelianGroupTreeConv.invHom (TwoColourAbelianGroupTree.invOp TwoColourAbelianGroupTree.leafB)
              (combNegB predecessor)).trans
        (TwoColourAbelianGroupTreeConv.mulCongr (TwoColourAbelianGroupTreeConv.invInvol TwoColourAbelianGroupTree.leafB) ih)

/-- **Inverting an a-pair-form swaps its lengths**: `i(pairFormA p n) ≈ pairFormA n p`. -/
theorem invPairFormASwap (positiveLength inverseLength : Nat) :
    TwoColourAbelianGroupTreeConv (TwoColourAbelianGroupTree.invOp (pairFormA positiveLength inverseLength))
      (pairFormA inverseLength positiveLength) :=
  (TwoColourAbelianGroupTreeConv.invHom (combPosA positiveLength) (combNegA inverseLength)).trans
    ((TwoColourAbelianGroupTreeConv.mulCongr (invCombPosA positiveLength) (invCombNegA inverseLength)).trans
      (TwoColourAbelianGroupTreeConv.commSwap (combNegA positiveLength) (combPosA inverseLength)))

/-- **Inverting a b-pair-form swaps its lengths**: `i(pairFormB p n) ≈ pairFormB n p`. -/
theorem invPairFormBSwap (positiveLength inverseLength : Nat) :
    TwoColourAbelianGroupTreeConv (TwoColourAbelianGroupTree.invOp (pairFormB positiveLength inverseLength))
      (pairFormB inverseLength positiveLength) :=
  (TwoColourAbelianGroupTreeConv.invHom (combPosB positiveLength) (combNegB inverseLength)).trans
    ((TwoColourAbelianGroupTreeConv.mulCongr (invCombPosB positiveLength) (invCombNegB inverseLength)).trans
      (TwoColourAbelianGroupTreeConv.commSwap (combNegB positiveLength) (combPosB inverseLength)))

/-! ## The full two-colour merge and normalization -/

/-- ★ **The full merge** — grafting two normal forms is convertible to the normal form of the componentwise
products of the two winding pairs: `m(normalFormOf a₁ b₁, normalFormOf a₂ b₂) ≈
normalFormOf (windingMul a₁ a₂) (windingMul b₁ b₂)`.  The genuinely-new four-way step: a
`twoColourConvMiddleFour` shuffle gathers the two a-pair-forms and the two b-pair-forms, then the per-colour
merges (`pairFormAMerge` / `pairFormBMerge`) collapse each side; the summed lengths are `windingMul`'s
components definitionally, so the target is reached with no transport. -/
theorem normalMerge (aWindingOne bWindingOne aWindingTwo bWindingTwo : WindingCount) :
    TwoColourAbelianGroupTreeConv
      (TwoColourAbelianGroupTree.mulOp (normalFormOf aWindingOne bWindingOne)
        (normalFormOf aWindingTwo bWindingTwo))
      (normalFormOf (windingMul aWindingOne aWindingTwo) (windingMul bWindingOne bWindingTwo)) :=
  (twoColourConvMiddleFour
      (pairFormA aWindingOne.positiveSlots aWindingOne.inverseSlots)
      (pairFormB bWindingOne.positiveSlots bWindingOne.inverseSlots)
      (pairFormA aWindingTwo.positiveSlots aWindingTwo.inverseSlots)
      (pairFormB bWindingTwo.positiveSlots bWindingTwo.inverseSlots)).trans
    (TwoColourAbelianGroupTreeConv.mulCongr
      (pairFormAMerge aWindingOne.positiveSlots aWindingOne.inverseSlots
        aWindingTwo.positiveSlots aWindingTwo.inverseSlots)
      (pairFormBMerge bWindingOne.positiveSlots bWindingOne.inverseSlots
        bWindingTwo.positiveSlots bWindingTwo.inverseSlots))

/-- ★ **Normalization** — every tree is convertible to the two-colour normal form of its own winding pair.
Induction on the tree: `leafA` / `leafB` / `unitOp` absorb units into the trivial normal-form shape; `invOp`
inverts the child's normal form and swaps each pair-form's lengths (`invPairFormASwap` / `invPairFormBSwap`);
`mulOp` normalizes both children (`mulCongr`) then grafts them with `normalMerge` — the merged windings are
`windingXOf (mulOp _ _)` definitionally, so no transport is needed. -/
theorem toNormalFormConv (tree : TwoColourAbelianGroupTree) :
    TwoColourAbelianGroupTreeConv tree (normalFormOf (windingAOf tree) (windingBOf tree)) := by
  induction tree with
  | leafA =>
      exact (((TwoColourAbelianGroupTreeConv.unitRight TwoColourAbelianGroupTree.leafA).symm).trans
              (TwoColourAbelianGroupTreeConv.unitRight
                (TwoColourAbelianGroupTree.mulOp TwoColourAbelianGroupTree.leafA
                  TwoColourAbelianGroupTree.unitOp)).symm).trans
        (((TwoColourAbelianGroupTreeConv.unitRight (pairFormA 1 0)).symm).trans
          (TwoColourAbelianGroupTreeConv.mulCongr (TwoColourAbelianGroupTreeConv.refl (pairFormA 1 0))
            (TwoColourAbelianGroupTreeConv.unitRight TwoColourAbelianGroupTree.unitOp).symm))
  | leafB =>
      exact (((TwoColourAbelianGroupTreeConv.unitRight TwoColourAbelianGroupTree.leafB).symm).trans
              (TwoColourAbelianGroupTreeConv.unitRight
                (TwoColourAbelianGroupTree.mulOp TwoColourAbelianGroupTree.leafB
                  TwoColourAbelianGroupTree.unitOp)).symm).trans
        (((TwoColourAbelianGroupTreeConv.unitLeft (pairFormB 1 0)).symm).trans
          (TwoColourAbelianGroupTreeConv.mulCongr
            (TwoColourAbelianGroupTreeConv.unitRight TwoColourAbelianGroupTree.unitOp).symm
            (TwoColourAbelianGroupTreeConv.refl (pairFormB 1 0))))
  | unitOp =>
      exact ((TwoColourAbelianGroupTreeConv.unitLeft TwoColourAbelianGroupTree.unitOp).symm).trans
        (TwoColourAbelianGroupTreeConv.mulCongr
          (TwoColourAbelianGroupTreeConv.unitLeft TwoColourAbelianGroupTree.unitOp).symm
          (TwoColourAbelianGroupTreeConv.unitLeft TwoColourAbelianGroupTree.unitOp).symm)
  | invOp inner ih =>
      exact ((TwoColourAbelianGroupTreeConv.invCongr ih).trans
          (TwoColourAbelianGroupTreeConv.invHom
            (pairFormA (windingAOf inner).positiveSlots (windingAOf inner).inverseSlots)
            (pairFormB (windingBOf inner).positiveSlots (windingBOf inner).inverseSlots))).trans
        (TwoColourAbelianGroupTreeConv.mulCongr
          (invPairFormASwap (windingAOf inner).positiveSlots (windingAOf inner).inverseSlots)
          (invPairFormBSwap (windingBOf inner).positiveSlots (windingBOf inner).inverseSlots))
  | mulOp left right ihLeft ihRight =>
      exact (TwoColourAbelianGroupTreeConv.mulCongr ihLeft ihRight).trans
        (normalMerge (windingAOf left) (windingBOf left) (windingAOf right) (windingBOf right))

/-! ## The per-colour pumps and pair-form equivalence -/

/-- **The a-pump** — an a-pair-form gains a cancelling positive/inverse `a`-slot pair:
`pairFormA p n ≈ pairFormA (p+1) (n+1)`.  Read backwards: the extra `leafA` and `i leafA` shuffle together
(`twoColourConvMiddleFour`), cancel (`invRight`), and the leftover unit is absorbed (`unitLeft`). -/
theorem pairFormAPump (positiveLength inverseLength : Nat) :
    TwoColourAbelianGroupTreeConv (pairFormA positiveLength inverseLength)
      (pairFormA (positiveLength + 1) (inverseLength + 1)) :=
  ((twoColourConvMiddleFour TwoColourAbelianGroupTree.leafA (combPosA positiveLength)
        (TwoColourAbelianGroupTree.invOp TwoColourAbelianGroupTree.leafA) (combNegA inverseLength)).trans
      ((TwoColourAbelianGroupTreeConv.mulCongr (TwoColourAbelianGroupTreeConv.invRight TwoColourAbelianGroupTree.leafA)
          (TwoColourAbelianGroupTreeConv.refl
            (TwoColourAbelianGroupTree.mulOp (combPosA positiveLength) (combNegA inverseLength)))).trans
        (TwoColourAbelianGroupTreeConv.unitLeft
          (TwoColourAbelianGroupTree.mulOp (combPosA positiveLength) (combNegA inverseLength))))).symm

/-- **The b-pump** — a b-pair-form gains a cancelling positive/inverse `b`-slot pair:
`pairFormB p n ≈ pairFormB (p+1) (n+1)`.  Same shape as `pairFormAPump` over the `b`-comb. -/
theorem pairFormBPump (positiveLength inverseLength : Nat) :
    TwoColourAbelianGroupTreeConv (pairFormB positiveLength inverseLength)
      (pairFormB (positiveLength + 1) (inverseLength + 1)) :=
  ((twoColourConvMiddleFour TwoColourAbelianGroupTree.leafB (combPosB positiveLength)
        (TwoColourAbelianGroupTree.invOp TwoColourAbelianGroupTree.leafB) (combNegB inverseLength)).trans
      ((TwoColourAbelianGroupTreeConv.mulCongr (TwoColourAbelianGroupTreeConv.invRight TwoColourAbelianGroupTree.leafB)
          (TwoColourAbelianGroupTreeConv.refl
            (TwoColourAbelianGroupTree.mulOp (combPosB positiveLength) (combNegB inverseLength)))).trans
        (TwoColourAbelianGroupTreeConv.unitLeft
          (TwoColourAbelianGroupTree.mulOp (combPosB positiveLength) (combNegB inverseLength))))).symm

/-- **Iterated a-pump** — `pairFormA p n ≈ pairFormA (p + steps) (n + steps)`.  Induction on `steps`. -/
theorem pairFormAPumpN (positiveLength inverseLength steps : Nat) :
    TwoColourAbelianGroupTreeConv (pairFormA positiveLength inverseLength)
      (pairFormA (positiveLength + steps) (inverseLength + steps)) := by
  induction steps with
  | zero => exact TwoColourAbelianGroupTreeConv.refl (pairFormA positiveLength inverseLength)
  | succ predecessor ih =>
      exact ih.trans (pairFormAPump (positiveLength + predecessor) (inverseLength + predecessor))

/-- **Iterated b-pump** — `pairFormB p n ≈ pairFormB (p + steps) (n + steps)`.  Induction on `steps`. -/
theorem pairFormBPumpN (positiveLength inverseLength steps : Nat) :
    TwoColourAbelianGroupTreeConv (pairFormB positiveLength inverseLength)
      (pairFormB (positiveLength + steps) (inverseLength + steps)) := by
  induction steps with
  | zero => exact TwoColourAbelianGroupTreeConv.refl (pairFormB positiveLength inverseLength)
  | succ predecessor ih =>
      exact ih.trans (pairFormBPump (positiveLength + predecessor) (inverseLength + predecessor))

/-- **a-pair-forms with equivalent windings are convertible** — pump each up by the other's inverse length to a
common a-pair-form, then join.  The hypothesis `p₁ + n₂ = p₂ + n₁` is exactly
`windingEquiv ⟨p₁,n₁⟩ ⟨p₂,n₂⟩`. -/
theorem pairFormAEquivConv (positiveOne inverseOne positiveTwo inverseTwo : Nat)
    (windingHyp : positiveOne + inverseTwo = positiveTwo + inverseOne) :
    TwoColourAbelianGroupTreeConv (pairFormA positiveOne inverseOne) (pairFormA positiveTwo inverseTwo) :=
  let pumpedOne := pairFormAPumpN positiveOne inverseOne inverseTwo
  let pumpedTwo := pairFormAPumpN positiveTwo inverseTwo inverseOne
  let commonEq :
      pairFormA (positiveOne + inverseTwo) (inverseOne + inverseTwo)
        = pairFormA (positiveTwo + inverseOne) (inverseTwo + inverseOne) :=
    (congrArg (fun positivePart => pairFormA positivePart (inverseOne + inverseTwo)) windingHyp).trans
      (congrArg (fun inversePart => pairFormA (positiveTwo + inverseOne) inversePart)
        (Nat.add_comm inverseOne inverseTwo))
  pumpedOne.trans ((twoColourConvOfTreeEq commonEq).trans (TwoColourAbelianGroupTreeConv.symm pumpedTwo))

/-- **b-pair-forms with equivalent windings are convertible** — the `b`-colour mirror of `pairFormAEquivConv`. -/
theorem pairFormBEquivConv (positiveOne inverseOne positiveTwo inverseTwo : Nat)
    (windingHyp : positiveOne + inverseTwo = positiveTwo + inverseOne) :
    TwoColourAbelianGroupTreeConv (pairFormB positiveOne inverseOne) (pairFormB positiveTwo inverseTwo) :=
  let pumpedOne := pairFormBPumpN positiveOne inverseOne inverseTwo
  let pumpedTwo := pairFormBPumpN positiveTwo inverseTwo inverseOne
  let commonEq :
      pairFormB (positiveOne + inverseTwo) (inverseOne + inverseTwo)
        = pairFormB (positiveTwo + inverseOne) (inverseTwo + inverseOne) :=
    (congrArg (fun positivePart => pairFormB positivePart (inverseOne + inverseTwo)) windingHyp).trans
      (congrArg (fun inversePart => pairFormB (positiveTwo + inverseOne) inversePart)
        (Nat.add_comm inverseOne inverseTwo))
  pumpedOne.trans ((twoColourConvOfTreeEq commonEq).trans (TwoColourAbelianGroupTreeConv.symm pumpedTwo))

/-! ## Completeness and the decision -/

/-- ★ **Completeness** — trees with `windingEquiv` a-windings and `windingEquiv` b-windings are convertible.
Both trees normalize (`toNormalFormConv`); the a-pair-forms meet via `pairFormAEquivConv` (the a-hypothesis
IS the `windingEquiv` unfolded), the b-pair-forms via `pairFormBEquivConv`; `mulCongr` combines them into a
convertibility of normal forms; trans through the reversed target normalization joins them. -/
theorem twoColourAbelianGroupConv_complete {source target : TwoColourAbelianGroupTree}
    (aHyp : windingEquiv (windingAOf source) (windingAOf target))
    (bHyp : windingEquiv (windingBOf source) (windingBOf target)) :
    TwoColourAbelianGroupTreeConv source target :=
  (toNormalFormConv source).trans
    ((TwoColourAbelianGroupTreeConv.mulCongr
        (pairFormAEquivConv (windingAOf source).positiveSlots (windingAOf source).inverseSlots
          (windingAOf target).positiveSlots (windingAOf target).inverseSlots aHyp)
        (pairFormBEquivConv (windingBOf source).positiveSlots (windingBOf source).inverseSlots
          (windingBOf target).positiveSlots (windingBOf target).inverseSlots bHyp)).trans
      (TwoColourAbelianGroupTreeConv.symm (toNormalFormConv target)))

/-- ★ **The decision** — convertibility in the walking abelian group on two generators is exactly the
conjunction of the two winding equivalences (the a-windings coincide AND the b-windings coincide).  Since each
winding equivalence is decidable (`Nat.decEq`), this biconditional decides the word problem. -/
theorem twoColourAbelianGroupConv_iff_windingEquiv (source target : TwoColourAbelianGroupTree) :
    TwoColourAbelianGroupTreeConv source target ↔
      (windingEquiv (windingAOf source) (windingAOf target)
        ∧ windingEquiv (windingBOf source) (windingBOf target)) :=
  ⟨fun conv => ⟨twoColourAbelianGroupConv_soundA conv, twoColourAbelianGroupConv_soundB conv⟩,
   fun pair => twoColourAbelianGroupConv_complete pair.1 pair.2⟩

/-- ★ **The decider** — a shipped `Decidable` for the two-colour convertibility, built from the two winding
decisions: match the a-winding decision, then (when it holds) the b-winding decision, discharging `isTrue` by
completeness and each `isFalse` by the matching soundness component.  Full-enumeration nested matches (no
wildcard over the `Decidable` inductive), a genuine decider, propext-free. -/
def decideTwoColourAbelianGroupTreeConv (source target : TwoColourAbelianGroupTree) :
    Decidable (TwoColourAbelianGroupTreeConv source target) :=
  match Nat.decEq ((windingAOf source).positiveSlots + (windingAOf target).inverseSlots)
                  ((windingAOf target).positiveSlots + (windingAOf source).inverseSlots) with
  | isFalse aNe => isFalse (fun conv => aNe (twoColourAbelianGroupConv_soundA conv))
  | isTrue aEq =>
      match Nat.decEq ((windingBOf source).positiveSlots + (windingBOf target).inverseSlots)
                      ((windingBOf target).positiveSlots + (windingBOf source).inverseSlots) with
      | isFalse bNe => isFalse (fun conv => bNe (twoColourAbelianGroupConv_soundB conv))
      | isTrue bEq => isTrue (twoColourAbelianGroupConv_complete aEq bEq)

/-- The two-colour convertibility as a `Decidable` INSTANCE, so the `decide` tactic and instance resolution
fire on it — mirroring the single-generator sibling.  A definitional alias of the shipped
`decideTwoColourAbelianGroupTreeConv`, hence propext-free. -/
instance instDecidableTwoColourAbelianGroupTreeConv (source target : TwoColourAbelianGroupTree) :
    Decidable (TwoColourAbelianGroupTreeConv source target) :=
  decideTwoColourAbelianGroupTreeConv source target

/-! ## Groundings -/

/-- ★ **The decision in action (positive, cross-colour cancellation)** — `m(m(leafA, i leafA), leafB) ≈ leafB`:
the `a` slot and its inverse cancel while the `b` slot survives.  Both sides have a-winding `~ ⟨0,0⟩` (LHS
`⟨1,1⟩`, RHS `⟨0,0⟩`) and equal b-winding (`⟨1,0⟩`), so they meet through the completeness leg with no explicit
rewrite path — the inverse-cancellation the count-based walker cannot see. -/
theorem twoColourAbelianGroupCancellationHolds :
    TwoColourAbelianGroupTreeConv
      (TwoColourAbelianGroupTree.mulOp
        (TwoColourAbelianGroupTree.mulOp TwoColourAbelianGroupTree.leafA
          (TwoColourAbelianGroupTree.invOp TwoColourAbelianGroupTree.leafA))
        TwoColourAbelianGroupTree.leafB)
      TwoColourAbelianGroupTree.leafB :=
  twoColourAbelianGroupConv_complete rfl rfl

/-- ★ **The decision in action (negative)** — `leafA` is NOT convertible to `leafB`: their a-windings differ
(`⟨1,0⟩` vs `⟨0,0⟩`; `1 + 0 ≠ 0 + 0`), so by the a-soundness component no convertibility can exist.
`Nat.noConfusion`. -/
theorem twoColourAbelianGroupRejectsLeafAB :
    ¬ TwoColourAbelianGroupTreeConv TwoColourAbelianGroupTree.leafA TwoColourAbelianGroupTree.leafB :=
  fun conv => Nat.noConfusion (twoColourAbelianGroupConv_soundA conv)

/-- ★ **The inverse does real work (cross-colour)** — `i(m(leafA, leafB)) ≈ m(i leafA, i leafB)`: the inverse
distributes over a mixed-colour product (valid precisely because the group is abelian). -/
theorem twoColourAbelianGroupInverseDistributes :
    TwoColourAbelianGroupTreeConv
      (TwoColourAbelianGroupTree.invOp
        (TwoColourAbelianGroupTree.mulOp TwoColourAbelianGroupTree.leafA TwoColourAbelianGroupTree.leafB))
      (TwoColourAbelianGroupTree.mulOp (TwoColourAbelianGroupTree.invOp TwoColourAbelianGroupTree.leafA)
        (TwoColourAbelianGroupTree.invOp TwoColourAbelianGroupTree.leafB)) :=
  TwoColourAbelianGroupTreeConv.invHom TwoColourAbelianGroupTree.leafA TwoColourAbelianGroupTree.leafB

/-! ## The marker -/

/-- ★ **The walking abelian group on TWO generators is DECIDED.**  `= true` records that
`twoColourAbelianGroupConv_iff_windingEquiv` reduces the two-colour word problem to a PAIR of winding
equivalences — the coincidence of the a-winding AND b-winding difference pairs in `ℤ²` = the free ℤ-module on
`{a, b}` — with soundness (per colour), normalization to the a-pair-form/b-pair-form canonical form, and
completeness all shipped, presented with no signed type and no subtraction.  The honest successor is the
`k`-generator (arbitrary alphabet) free abelian group `ℤᵏ`, whose invariant is a winding VECTOR indexed by the
generator set rather than a fixed pair, decided by componentwise winding equivalence. -/
def fxWalkingAbelianGroup_hasTwoColourDecision : Bool := true

end FX1Poly.Polygraph
