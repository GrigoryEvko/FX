import FX1Poly.Polygraph.TwoCategory.WalkingSemilattice.SemilatticeSeed

/-! # WalkingSemilattice/TwoColourSemilatticeSeed — the walking (bounded) semilattice on TWO generators: the coloured decision

The presentation of the free **bounded semilattice** = idempotent commutative monoid on TWO generating
slots `a` and `b`, as a signature plus a tree convertibility: the binary join `m : arity 2`, the bottom
`e : arity 0`, and the two input slots, with the FIVE relations — associativity, left unit, right unit,
commutativity, and **idempotency** `m(x, x) ≈ x`.

## ★ Why this walker is the honest successor of the single-generator rung

The sibling `SemilatticeSeed` decides the SINGLE-generator free bounded semilattice: idempotency collapses
the commutative monoid's `ℕ` leaf count to the two-element lattice `{⊥, ⊤}`, so a tree's class is a single
`SlotPresence`.  The COLOURED (multi-generator) free bounded semilattice is the finite POWERSET of the
generator set (join = union).  For two generators this powerset is the lattice `{absent, present}²` — a
tree's class is the PAIR `(is a present?, is b present?)`.  So the complete invariant is TWO independent
slot-presence folds (`presenceAOf`, `presenceBOf`), reusing the sibling's `SlotPresence` type and `slotJoin`
algebra unchanged; convertibility is exactly equality of BOTH presences.  This file ships the two soundness
theorems, the four canonical normal forms indexed by the presence pair, the two coloured prepend lemmas
(the real content: grafting a coloured leaf joins that colour to `present`), the merge lemma, normalization,
completeness, and the shipped decision.

## ★ The honest wall

The `n`-COLOUR free bounded semilattice is the powerset of the whole `n`-element generator set, decided by
finite-set (sorted-distinct-list) equality — the successor rung, not attempted here.

Raw Lean 4 + Init; the convertibility is an inductive `Prop`; per-declaration `#assert_no_axioms` gated in
the audit twin.  Free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1Poly.Polygraph

/-! ## The two-colour semilattice tree carrier -/

/-- ★ The **tree carrier** of the walking bounded semilattice on two generators: an un-indexed planar tree
over two distinct input slots.  `leafA` and `leafB` are the two input slots; `unitOp` is the bottom `⊥`;
`mulOp` joins two subtrees under the binary join `m`.  A closed tree's complete convertibility invariant is
the PAIR — whether it contains any `leafA`, and whether it contains any `leafB`. -/
inductive TwoColourSemilatticeTree where
  /-- The first input slot, colour `a`. -/
  | leafA
  /-- The second input slot, colour `b`. -/
  | leafB
  /-- The bottom generator `⊥ : arity 0`. -/
  | unitOp
  /-- The binary join `m : arity 2` of the left and right subtrees. -/
  | mulOp : TwoColourSemilatticeTree → TwoColourSemilatticeTree → TwoColourSemilatticeTree

/-! ## The two presence folds (reusing the sibling's `SlotPresence` and `slotJoin`) -/

/-- The **colour-`a` presence** of a tree — `present` iff it contains at least one `leafA`.  A
full-enumeration structural fold onto the reused two-valued `SlotPresence`, joining children with the reused
`slotJoin`.  Half of the complete two-colour invariant. -/
def presenceAOf : TwoColourSemilatticeTree → SlotPresence
  | .leafA => SlotPresence.present
  | .leafB => SlotPresence.absent
  | .unitOp => SlotPresence.absent
  | .mulOp left right => slotJoin (presenceAOf left) (presenceAOf right)

/-- The **colour-`b` presence** of a tree — `present` iff it contains at least one `leafB`.  The mirror of
`presenceAOf`; the other half of the complete two-colour invariant. -/
def presenceBOf : TwoColourSemilatticeTree → SlotPresence
  | .leafA => SlotPresence.absent
  | .leafB => SlotPresence.present
  | .unitOp => SlotPresence.absent
  | .mulOp left right => slotJoin (presenceBOf left) (presenceBOf right)

/-- Smoke: colour `a` is present in the `a` slot. -/
theorem presenceAOf_leafA : presenceAOf TwoColourSemilatticeTree.leafA = SlotPresence.present := rfl

/-- Smoke: colour `b` is absent from the `a` slot — the two colours are independent. -/
theorem presenceBOf_leafA : presenceBOf TwoColourSemilatticeTree.leafA = SlotPresence.absent := rfl

/-- Smoke: colour `b` is present in the `b` slot. -/
theorem presenceBOf_leafB : presenceBOf TwoColourSemilatticeTree.leafB = SlotPresence.present := rfl

/-! ## The two-colour semilattice tree convertibility -/

/-- ★ The **tree convertibility** of the walking bounded semilattice on two generators — the free
convertibility of the `{m, e}` signature closed under the five semilattice laws (associativity, left/right
unit, commutativity, **idempotency**), the full tree-congruence, and `refl` / `symm` / `trans`.  Identical
constructors to the single-generator sibling, over the two-slot carrier. -/
inductive TwoColourSemilatticeTreeConv : TwoColourSemilatticeTree → TwoColourSemilatticeTree → Prop where
  /-- **Associativity**. -/
  | assoc (left middle right : TwoColourSemilatticeTree) :
      TwoColourSemilatticeTreeConv
        (TwoColourSemilatticeTree.mulOp (TwoColourSemilatticeTree.mulOp left middle) right)
        (TwoColourSemilatticeTree.mulOp left (TwoColourSemilatticeTree.mulOp middle right))
  /-- **Left unit** `m(⊥, subtree) ≈ subtree`. -/
  | unitLeft (subtree : TwoColourSemilatticeTree) :
      TwoColourSemilatticeTreeConv (TwoColourSemilatticeTree.mulOp TwoColourSemilatticeTree.unitOp subtree) subtree
  /-- **Right unit** `m(subtree, ⊥) ≈ subtree`. -/
  | unitRight (subtree : TwoColourSemilatticeTree) :
      TwoColourSemilatticeTreeConv (TwoColourSemilatticeTree.mulOp subtree TwoColourSemilatticeTree.unitOp) subtree
  /-- **Commutativity** `m(left, right) ≈ m(right, left)`. -/
  | commSwap (left right : TwoColourSemilatticeTree) :
      TwoColourSemilatticeTreeConv
        (TwoColourSemilatticeTree.mulOp left right) (TwoColourSemilatticeTree.mulOp right left)
  /-- **Idempotency** `m(subtree, subtree) ≈ subtree` — the relation the commutative monoid lacks. -/
  | idem (subtree : TwoColourSemilatticeTree) :
      TwoColourSemilatticeTreeConv (TwoColourSemilatticeTree.mulOp subtree subtree) subtree
  /-- **Congruence under a join node** — into BOTH children. -/
  | mulCongr {leftOld leftNew rightOld rightNew : TwoColourSemilatticeTree} :
      TwoColourSemilatticeTreeConv leftOld leftNew → TwoColourSemilatticeTreeConv rightOld rightNew →
      TwoColourSemilatticeTreeConv
        (TwoColourSemilatticeTree.mulOp leftOld rightOld) (TwoColourSemilatticeTree.mulOp leftNew rightNew)
  /-- Reflexivity. -/
  | refl (tree : TwoColourSemilatticeTree) : TwoColourSemilatticeTreeConv tree tree
  /-- Symmetry. -/
  | symm {tree1 tree2 : TwoColourSemilatticeTree} :
      TwoColourSemilatticeTreeConv tree1 tree2 → TwoColourSemilatticeTreeConv tree2 tree1
  /-- Transitivity. -/
  | trans {tree1 tree2 tree3 : TwoColourSemilatticeTree} :
      TwoColourSemilatticeTreeConv tree1 tree2 → TwoColourSemilatticeTreeConv tree2 tree3 →
      TwoColourSemilatticeTreeConv tree1 tree3

/-! ## Soundness: convertible ⟹ equal in BOTH colour presences -/

/-- ★ **Soundness, colour `a`** — convertible trees have equal colour-`a` presence.  Each law preserves
`presenceAOf`: associativity / commutativity / idempotency / right-unit by the `slotJoin` algebra, left-unit
by the definitional `slotJoin absent x = x`, and the congruence by the inductive hypotheses.  Propext-clean. -/
theorem twoColourSemilatticeConv_soundA {source target : TwoColourSemilatticeTree}
    (conv : TwoColourSemilatticeTreeConv source target) : presenceAOf source = presenceAOf target := by
  induction conv with
  | assoc left middle right =>
      exact slotJoinAssoc (presenceAOf left) (presenceAOf middle) (presenceAOf right)
  | unitLeft subtree => exact rfl
  | unitRight subtree => exact slotJoinAbsentRight (presenceAOf subtree)
  | commSwap left right => exact slotJoinComm (presenceAOf left) (presenceAOf right)
  | idem subtree => exact slotJoinSelf (presenceAOf subtree)
  | @mulCongr leftOld leftNew rightOld rightNew _ _ ihLeft ihRight =>
      exact (congrArg (fun leftPresence => slotJoin leftPresence (presenceAOf rightOld)) ihLeft).trans
        (congrArg (fun rightPresence => slotJoin (presenceAOf leftNew) rightPresence) ihRight)
  | refl tree => exact rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- ★ **Soundness, colour `b`** — convertible trees have equal colour-`b` presence.  The mirror of
`twoColourSemilatticeConv_soundA` on `presenceBOf`. -/
theorem twoColourSemilatticeConv_soundB {source target : TwoColourSemilatticeTree}
    (conv : TwoColourSemilatticeTreeConv source target) : presenceBOf source = presenceBOf target := by
  induction conv with
  | assoc left middle right =>
      exact slotJoinAssoc (presenceBOf left) (presenceBOf middle) (presenceBOf right)
  | unitLeft subtree => exact rfl
  | unitRight subtree => exact slotJoinAbsentRight (presenceBOf subtree)
  | commSwap left right => exact slotJoinComm (presenceBOf left) (presenceBOf right)
  | idem subtree => exact slotJoinSelf (presenceBOf subtree)
  | @mulCongr leftOld leftNew rightOld rightNew _ _ ihLeft ihRight =>
      exact (congrArg (fun leftPresence => slotJoin leftPresence (presenceBOf rightOld)) ihLeft).trans
        (congrArg (fun rightPresence => slotJoin (presenceBOf leftNew) rightPresence) ihRight)
  | refl tree => exact rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ## Normal forms indexed by the presence pair -/

/-- The **normal form** of a presence pair — the four canonical trees of the powerset lattice `{a, b}`:
`(absent, absent) ↦ ⊥`, `(present, absent) ↦ a`, `(absent, present) ↦ b`, `(present, present) ↦ m(a, b)`. -/
def normalOfPresences : SlotPresence → SlotPresence → TwoColourSemilatticeTree
  | .absent, .absent => TwoColourSemilatticeTree.unitOp
  | .present, .absent => TwoColourSemilatticeTree.leafA
  | .absent, .present => TwoColourSemilatticeTree.leafB
  | .present, .present => TwoColourSemilatticeTree.mulOp TwoColourSemilatticeTree.leafA TwoColourSemilatticeTree.leafB

/-! ## The two coloured prepend lemmas — the real content -/

/-- ★ **Prepend colour `a`** — grafting a `leafA` onto a normal form joins colour `a` to `present`, leaving
colour `b` fixed.  Four explicit paths (`slotJoin present _` is definitionally `present`): right-unit
absorbing `⊥`, refl, idempotency of `a`, and — when `a` is already present — reassociating and folding the
duplicate `a` by idempotency. -/
theorem prependLeafA (presenceA presenceB : SlotPresence) :
    TwoColourSemilatticeTreeConv
      (TwoColourSemilatticeTree.mulOp TwoColourSemilatticeTree.leafA (normalOfPresences presenceA presenceB))
      (normalOfPresences (slotJoin SlotPresence.present presenceA) presenceB) := by
  cases presenceA <;> cases presenceB
  · exact TwoColourSemilatticeTreeConv.unitRight TwoColourSemilatticeTree.leafA
  · exact TwoColourSemilatticeTreeConv.refl
      (TwoColourSemilatticeTree.mulOp TwoColourSemilatticeTree.leafA TwoColourSemilatticeTree.leafB)
  · exact TwoColourSemilatticeTreeConv.idem TwoColourSemilatticeTree.leafA
  · exact TwoColourSemilatticeTreeConv.trans
      (TwoColourSemilatticeTreeConv.symm
        (TwoColourSemilatticeTreeConv.assoc
          TwoColourSemilatticeTree.leafA TwoColourSemilatticeTree.leafA TwoColourSemilatticeTree.leafB))
      (TwoColourSemilatticeTreeConv.mulCongr
        (TwoColourSemilatticeTreeConv.idem TwoColourSemilatticeTree.leafA)
        (TwoColourSemilatticeTreeConv.refl TwoColourSemilatticeTree.leafB))

/-- ★ **Prepend colour `b`** — grafting a `leafB` onto a normal form joins colour `b` to `present`, leaving
colour `a` fixed.  The mirror of `prependLeafA`: right-unit, idempotency of `b`, commuting the pair into the
canonical `m(a, b)` order, and — when `b` is already present — commuting, reassociating, and folding the
duplicate `b`. -/
theorem prependLeafB (presenceA presenceB : SlotPresence) :
    TwoColourSemilatticeTreeConv
      (TwoColourSemilatticeTree.mulOp TwoColourSemilatticeTree.leafB (normalOfPresences presenceA presenceB))
      (normalOfPresences presenceA (slotJoin SlotPresence.present presenceB)) := by
  cases presenceA <;> cases presenceB
  · exact TwoColourSemilatticeTreeConv.unitRight TwoColourSemilatticeTree.leafB
  · exact TwoColourSemilatticeTreeConv.idem TwoColourSemilatticeTree.leafB
  · exact TwoColourSemilatticeTreeConv.commSwap TwoColourSemilatticeTree.leafB TwoColourSemilatticeTree.leafA
  · exact TwoColourSemilatticeTreeConv.trans
      (TwoColourSemilatticeTreeConv.trans
        (TwoColourSemilatticeTreeConv.commSwap TwoColourSemilatticeTree.leafB
          (TwoColourSemilatticeTree.mulOp TwoColourSemilatticeTree.leafA TwoColourSemilatticeTree.leafB))
        (TwoColourSemilatticeTreeConv.assoc
          TwoColourSemilatticeTree.leafA TwoColourSemilatticeTree.leafB TwoColourSemilatticeTree.leafB))
      (TwoColourSemilatticeTreeConv.mulCongr
        (TwoColourSemilatticeTreeConv.refl TwoColourSemilatticeTree.leafA)
        (TwoColourSemilatticeTreeConv.idem TwoColourSemilatticeTree.leafB))

/-! ## The merge lemma -/

/-- ★ **Merge** — joining two normal forms reduces to the normal form of their componentwise `slotJoin`.
Dispatch on the LEFT presence pair via the two prepends: `⊥` collapses by left-unit; a single left colour is
one prepend; the full `m(a, b)` left reassociates and threads both prepends. -/
theorem semilatticeMerge (presenceA1 presenceB1 presenceA2 presenceB2 : SlotPresence) :
    TwoColourSemilatticeTreeConv
      (TwoColourSemilatticeTree.mulOp (normalOfPresences presenceA1 presenceB1) (normalOfPresences presenceA2 presenceB2))
      (normalOfPresences (slotJoin presenceA1 presenceA2) (slotJoin presenceB1 presenceB2)) := by
  cases presenceA1 <;> cases presenceB1
  · exact TwoColourSemilatticeTreeConv.unitLeft (normalOfPresences presenceA2 presenceB2)
  · exact prependLeafB presenceA2 presenceB2
  · exact prependLeafA presenceA2 presenceB2
  · exact TwoColourSemilatticeTreeConv.trans
      (TwoColourSemilatticeTreeConv.trans
        (TwoColourSemilatticeTreeConv.assoc
          TwoColourSemilatticeTree.leafA TwoColourSemilatticeTree.leafB
          (normalOfPresences presenceA2 presenceB2))
        (TwoColourSemilatticeTreeConv.mulCongr
          (TwoColourSemilatticeTreeConv.refl TwoColourSemilatticeTree.leafA)
          (prependLeafB presenceA2 presenceB2)))
      (prependLeafA presenceA2 (slotJoin SlotPresence.present presenceB2))

/-! ## Normalization, completeness, and the decision -/

/-- ★ **Normalization** — every tree is convertible to the normal form of its presence pair.  Induction on
the tree: `leafA` / `leafB` / `unitOp` are already normal, and `mulOp` normalizes both children and joins
them via `semilatticeMerge` (whose merged presences are definitionally `presenceAOf`/`presenceBOf` of the
join node). -/
theorem twoColourSemilatticeReducesToNormal (tree : TwoColourSemilatticeTree) :
    TwoColourSemilatticeTreeConv tree (normalOfPresences (presenceAOf tree) (presenceBOf tree)) := by
  induction tree with
  | leafA => exact TwoColourSemilatticeTreeConv.refl TwoColourSemilatticeTree.leafA
  | leafB => exact TwoColourSemilatticeTreeConv.refl TwoColourSemilatticeTree.leafB
  | unitOp => exact TwoColourSemilatticeTreeConv.refl TwoColourSemilatticeTree.unitOp
  | mulOp left right ihLeft ihRight =>
      exact TwoColourSemilatticeTreeConv.trans
        (TwoColourSemilatticeTreeConv.mulCongr ihLeft ihRight)
        (semilatticeMerge (presenceAOf left) (presenceBOf left) (presenceAOf right) (presenceBOf right))

/-- ★ **Completeness** — equal presence pair implies convertibility, through the common normal form.  Both
sides reduce to `normalOfPresences` of their presence pair; the two equalities equate those normal forms via
nested `congrArg`. -/
theorem twoColourSemilatticeConv_complete {source target : TwoColourSemilatticeTree}
    (eqA : presenceAOf source = presenceAOf target) (eqB : presenceBOf source = presenceBOf target) :
    TwoColourSemilatticeTreeConv source target := by
  have sourceReduces : TwoColourSemilatticeTreeConv source
      (normalOfPresences (presenceAOf source) (presenceBOf source)) :=
    twoColourSemilatticeReducesToNormal source
  have targetReduces : TwoColourSemilatticeTreeConv target
      (normalOfPresences (presenceAOf target) (presenceBOf target)) :=
    twoColourSemilatticeReducesToNormal target
  have normalEq : normalOfPresences (presenceAOf source) (presenceBOf source)
      = normalOfPresences (presenceAOf target) (presenceBOf target) :=
    (congrArg (fun presenceA => normalOfPresences presenceA (presenceBOf source)) eqA).trans
      (congrArg (fun presenceB => normalOfPresences (presenceAOf target) presenceB) eqB)
  exact TwoColourSemilatticeTreeConv.trans sourceReduces
    (normalEq.symm ▸ TwoColourSemilatticeTreeConv.symm targetReduces)

/-- ★ **The decision** — convertibility in the walking bounded semilattice on two generators is exactly
equality of BOTH colour presences: the powerset lattice `{a, b}` of the generator set. -/
theorem twoColourSemilatticeConv_iff_presences (source target : TwoColourSemilatticeTree) :
    TwoColourSemilatticeTreeConv source target ↔
      (presenceAOf source = presenceAOf target ∧ presenceBOf source = presenceBOf target) :=
  ⟨fun conv => ⟨twoColourSemilatticeConv_soundA conv, twoColourSemilatticeConv_soundB conv⟩,
    fun presencesEq => twoColourSemilatticeConv_complete presencesEq.left presencesEq.right⟩

/-- ★ **The decider** — a shipped `Decidable` for the two-colour convertibility, built from the two
slot-presence decisions (reusing the sibling's `slotPresenceDecEq`): both `isTrue` discharge by
completeness, either `isFalse` refutes via the matching soundness.  Propext-free. -/
def decideTwoColourSemilatticeTreeConv (source target : TwoColourSemilatticeTree) :
    Decidable (TwoColourSemilatticeTreeConv source target) :=
  match slotPresenceDecEq (presenceAOf source) (presenceAOf target),
        slotPresenceDecEq (presenceBOf source) (presenceBOf target) with
  | isTrue eqA, isTrue eqB => isTrue (twoColourSemilatticeConv_complete eqA eqB)
  | isFalse neA, _ => isFalse (fun conv => neA (twoColourSemilatticeConv_soundA conv))
  | _, isFalse neB => isFalse (fun conv => neB (twoColourSemilatticeConv_soundB conv))

/-- The two-colour convertibility as a `Decidable` INSTANCE, so the `decide` tactic and instance resolution
fire on it.  A definitional alias of the shipped `decideTwoColourSemilatticeTreeConv`, hence propext-free. -/
instance instDecidableTwoColourSemilatticeTreeConv (source target : TwoColourSemilatticeTree) :
    Decidable (TwoColourSemilatticeTreeConv source target) :=
  decideTwoColourSemilatticeTreeConv source target

/-! ## Groundings -/

/-- ★ **Two-colour commutation (positive)** — the two colours in either order are convertible: `m(a, b)` and
`m(b, a)` share the presence pair `(present, present)`, so they are convertible through completeness with no
explicit rewrite path. -/
theorem twoColourSemilatticeSwapConvertible :
    TwoColourSemilatticeTreeConv
      (TwoColourSemilatticeTree.mulOp TwoColourSemilatticeTree.leafA TwoColourSemilatticeTree.leafB)
      (TwoColourSemilatticeTree.mulOp TwoColourSemilatticeTree.leafB TwoColourSemilatticeTree.leafA) :=
  twoColourSemilatticeConv_complete rfl rfl

/-- ★ **Repeated-colour collapse (positive)** — `m(m(a, a), b)` collapses to `m(a, b)`: idempotency erases
the duplicate `a` while colour `b` is untouched, so both share the presence pair `(present, present)` and
are convertible through completeness — the count-collapse the commutative-monoid walker cannot see. -/
theorem twoColourSemilatticeCollapsesRepeatedColour :
    TwoColourSemilatticeTreeConv
      (TwoColourSemilatticeTree.mulOp
        (TwoColourSemilatticeTree.mulOp TwoColourSemilatticeTree.leafA TwoColourSemilatticeTree.leafA)
        TwoColourSemilatticeTree.leafB)
      (TwoColourSemilatticeTree.mulOp TwoColourSemilatticeTree.leafA TwoColourSemilatticeTree.leafB) :=
  twoColourSemilatticeConv_complete rfl rfl

/-- ★ **Idempotency does real work** — a whole two-colour subtree joined with itself collapses:
`m(m(a, b), m(a, b)) ≈ m(a, b)`, the direct idempotency move. -/
theorem twoColourSemilatticeIdemPairHolds :
    TwoColourSemilatticeTreeConv
      (TwoColourSemilatticeTree.mulOp
        (TwoColourSemilatticeTree.mulOp TwoColourSemilatticeTree.leafA TwoColourSemilatticeTree.leafB)
        (TwoColourSemilatticeTree.mulOp TwoColourSemilatticeTree.leafA TwoColourSemilatticeTree.leafB))
      (TwoColourSemilatticeTree.mulOp TwoColourSemilatticeTree.leafA TwoColourSemilatticeTree.leafB) :=
  TwoColourSemilatticeTreeConv.idem
    (TwoColourSemilatticeTree.mulOp TwoColourSemilatticeTree.leafA TwoColourSemilatticeTree.leafB)

/-- ★ **The decision in action (negative)** — a lone `a` slot is NOT convertible to `m(a, b)`: their
colour-`b` presence differs (`absent ≠ present`), so by colour-`b` soundness no convertibility exists.
`SlotPresence.noConfusion`. -/
theorem twoColourSemilatticeRejectsMissingColour :
    ¬ TwoColourSemilatticeTreeConv TwoColourSemilatticeTree.leafA
        (TwoColourSemilatticeTree.mulOp TwoColourSemilatticeTree.leafA TwoColourSemilatticeTree.leafB) :=
  fun conv => SlotPresence.noConfusion (twoColourSemilatticeConv_soundB conv)

/-! ## The marker -/

/-- ★ **The walking bounded semilattice on two generators is DECIDED.**  `= true` records that
`twoColourSemilatticeConv_iff_presences` reduces the coloured word problem to equality of a PAIR of
two-valued slot-presences — the powerset lattice `{a, b}` of the two-element generator set (join = union).
The honest successor is the `n`-COLOUR bounded semilattice: the powerset of the whole generator set, decided
by finite-subset equality. -/
def fxWalkingSemilattice_hasTwoColourDecision : Bool := true

end FX1Poly.Polygraph
