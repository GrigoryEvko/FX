/-! # WalkingSemilattice/SemilatticeSeed — the walking (bounded) semilattice: signature, relation, and the FULL single-generator decision

The presentation of the free **bounded semilattice** = idempotent commutative monoid on one generating
slot, as a signature plus a tree convertibility: the binary join `m : arity 2`, the bottom `e : arity 0`,
and the input slot, with the FIVE relations — associativity, left unit, right unit, commutativity, and
**idempotency** `m(x, x) ≈ x`.

## ★ Why this walker is FULLY DECIDED — and why the model is two-valued, not `ℕ`

The sibling `WalkingCommutativeMonoid` on one generator has word problem `(ℕ, +, 0)` — leaf COUNT.  Adding
idempotency collapses the count: `m(leaf, leaf) ≈ leaf`, so `n` copies of the slot join to a single slot.
The free bounded semilattice on one generator is therefore the two-element lattice `{⊥, ⊤}` — a tree's class
is determined entirely by whether it contains ANY slot.  So the complete invariant is a two-valued
`SlotPresence` (`slotPresenceOf`), and `SemilatticeTreeConv a b ↔ slotPresenceOf a = slotPresenceOf b`
decides convertibility.  This file ships soundness, normalization to `⊥`/`⊤`, completeness, and the decision.

The invariant is a purpose-built 2-element type (not `Bool`) so its join algebra is proved by plain
case-analysis on the type's constructors — no `Bool`/`decide` machinery in the substrate.

## ★ The honest wall

The COLOURED (multi-generator) free bounded semilattice is the finite POWERSET of the generator set (join =
union), decided by set (sorted-distinct-list) equality — the successor rung, not attempted here.

Raw Lean 4 + Init; the convertibility is an inductive `Prop`; per-declaration `#assert_no_axioms` gated in
the audit twin.  Free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1Poly.Polygraph

/-! ## The semilattice tree carrier -/

/-- ★ The **tree carrier** of the walking bounded semilattice: an un-indexed planar tree over the two
generators.  `leaf` is an input slot; `unitOp` is the bottom `⊥`; `mulOp` joins two subtrees under the
binary join `m`.  For the single-generator semilattice, whether a closed tree contains ANY `leaf` is its
complete convertibility invariant. -/
inductive SemilatticeTree where
  /-- An input slot. -/
  | leaf
  /-- The bottom generator `⊥ : arity 0`. -/
  | unitOp
  /-- The binary join `m : arity 2` of the left and right subtrees. -/
  | mulOp : SemilatticeTree → SemilatticeTree → SemilatticeTree

/-! ## The two-valued invariant and its join algebra -/

/-- The **slot-presence** value — the two elements of the free single-generator bounded semilattice:
`absent` (bottom `⊥`) and `present` (the single slot `⊤`). -/
inductive SlotPresence where
  /-- No slot — the bottom `⊥`. -/
  | absent
  /-- At least one slot — the top `⊤`. -/
  | present

/-- The semilattice **join** on slot-presence: `absent` is the identity, `present` absorbs.  Recursion on
the first argument, propext-clean. -/
def slotJoin : SlotPresence → SlotPresence → SlotPresence
  | .absent, other => other
  | .present, _ => .present

/-- `slotJoin` is associative. -/
theorem slotJoinAssoc (a b c : SlotPresence) : slotJoin (slotJoin a b) c = slotJoin a (slotJoin b c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- `slotJoin` is commutative. -/
theorem slotJoinComm (a b : SlotPresence) : slotJoin a b = slotJoin b a := by
  cases a <;> cases b <;> rfl

/-- `slotJoin` is idempotent. -/
theorem slotJoinSelf (a : SlotPresence) : slotJoin a a = a := by
  cases a <;> rfl

/-- `absent` is a right identity for `slotJoin` (it is a left identity definitionally). -/
theorem slotJoinAbsentRight (a : SlotPresence) : slotJoin a SlotPresence.absent = a := by
  cases a <;> rfl

/-- The **slot-presence invariant** of a tree — `present` iff it contains at least one `leaf`.
`leaf ↦ present`, `unitOp ↦ absent`, `mulOp l r ↦ slotJoin (…l) (…r)`.  A full-enumeration structural fold,
propext-clean.  For the single-generator semilattice this is the COMPLETE convertibility invariant. -/
def slotPresenceOf : SemilatticeTree → SlotPresence
  | .leaf => SlotPresence.present
  | .unitOp => SlotPresence.absent
  | .mulOp left right => slotJoin (slotPresenceOf left) (slotPresenceOf right)

/-- Smoke: a single slot is present. -/
theorem slotPresenceOf_leaf : slotPresenceOf SemilatticeTree.leaf = SlotPresence.present := rfl

/-- Smoke: the bottom contains no slot. -/
theorem slotPresenceOf_unit : slotPresenceOf SemilatticeTree.unitOp = SlotPresence.absent := rfl

/-! ## The semilattice tree convertibility -/

/-- ★ The **tree convertibility** of the walking bounded semilattice — the free convertibility of the
`{m, e}` signature closed under the five semilattice laws (associativity, left/right unit, commutativity,
**idempotency**), the full tree-congruence, and `refl` / `symm` / `trans`. -/
inductive SemilatticeTreeConv : SemilatticeTree → SemilatticeTree → Prop where
  /-- **Associativity**. -/
  | assoc (left middle right : SemilatticeTree) :
      SemilatticeTreeConv
        (SemilatticeTree.mulOp (SemilatticeTree.mulOp left middle) right)
        (SemilatticeTree.mulOp left (SemilatticeTree.mulOp middle right))
  /-- **Left unit** `m(⊥, subtree) ≈ subtree`. -/
  | unitLeft (subtree : SemilatticeTree) :
      SemilatticeTreeConv (SemilatticeTree.mulOp SemilatticeTree.unitOp subtree) subtree
  /-- **Right unit** `m(subtree, ⊥) ≈ subtree`. -/
  | unitRight (subtree : SemilatticeTree) :
      SemilatticeTreeConv (SemilatticeTree.mulOp subtree SemilatticeTree.unitOp) subtree
  /-- **Commutativity** `m(left, right) ≈ m(right, left)`. -/
  | commSwap (left right : SemilatticeTree) :
      SemilatticeTreeConv (SemilatticeTree.mulOp left right) (SemilatticeTree.mulOp right left)
  /-- **Idempotency** `m(subtree, subtree) ≈ subtree` — the relation the commutative monoid lacks. -/
  | idem (subtree : SemilatticeTree) :
      SemilatticeTreeConv (SemilatticeTree.mulOp subtree subtree) subtree
  /-- **Congruence under a join node** — into BOTH children. -/
  | mulCongr {leftOld leftNew rightOld rightNew : SemilatticeTree} :
      SemilatticeTreeConv leftOld leftNew → SemilatticeTreeConv rightOld rightNew →
      SemilatticeTreeConv (SemilatticeTree.mulOp leftOld rightOld) (SemilatticeTree.mulOp leftNew rightNew)
  /-- Reflexivity. -/
  | refl (tree : SemilatticeTree) : SemilatticeTreeConv tree tree
  /-- Symmetry. -/
  | symm {tree1 tree2 : SemilatticeTree} : SemilatticeTreeConv tree1 tree2 → SemilatticeTreeConv tree2 tree1
  /-- Transitivity. -/
  | trans {tree1 tree2 tree3 : SemilatticeTree} :
      SemilatticeTreeConv tree1 tree2 → SemilatticeTreeConv tree2 tree3 → SemilatticeTreeConv tree1 tree3

/-! ## Soundness: convertible ⟹ equal slot-presence -/

/-- ★ **Soundness** — convertible trees have equal slot-presence.  Each law preserves `slotPresenceOf`:
associativity / commutativity / idempotency / right-unit by the `slotJoin` algebra, left-unit by the
definitional `slotJoin absent x = x`, and the congruence by the inductive hypotheses.  All propext-clean. -/
theorem semilatticeTreeConv_sound {source target : SemilatticeTree}
    (conv : SemilatticeTreeConv source target) : slotPresenceOf source = slotPresenceOf target := by
  induction conv with
  | assoc left middle right =>
      exact slotJoinAssoc (slotPresenceOf left) (slotPresenceOf middle) (slotPresenceOf right)
  | unitLeft subtree => exact rfl
  | unitRight subtree => exact slotJoinAbsentRight (slotPresenceOf subtree)
  | commSwap left right => exact slotJoinComm (slotPresenceOf left) (slotPresenceOf right)
  | idem subtree => exact slotJoinSelf (slotPresenceOf subtree)
  | @mulCongr leftOld leftNew rightOld rightNew _ _ ihLeft ihRight =>
      exact (congrArg (fun leftPresence => slotJoin leftPresence (slotPresenceOf rightOld)) ihLeft).trans
        (congrArg (fun rightPresence => slotJoin (slotPresenceOf leftNew) rightPresence) ihRight)
  | refl tree => exact rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ## Normalization: every tree reduces to ⊥ or a single slot -/

/-- The **normal form** of a slot-presence: `absent ↦ unitOp` (bottom), `present ↦ leaf` (the single slot). -/
def normalOf : SlotPresence → SemilatticeTree
  | .absent => SemilatticeTree.unitOp
  | .present => SemilatticeTree.leaf

/-- Joining two normal forms reduces to the normal form of their `slotJoin`: a four-case fact (⊥⊥→⊥ by
unit, ⊥⊤/⊤⊥→⊤ by unit, ⊤⊤→⊤ by idempotency), the whole point of idempotency. -/
theorem semilatticeMulNormal (leftPresence rightPresence : SlotPresence) :
    SemilatticeTreeConv
      (SemilatticeTree.mulOp (normalOf leftPresence) (normalOf rightPresence))
      (normalOf (slotJoin leftPresence rightPresence)) := by
  cases leftPresence <;> cases rightPresence
  · exact SemilatticeTreeConv.unitLeft SemilatticeTree.unitOp
  · exact SemilatticeTreeConv.unitLeft SemilatticeTree.leaf
  · exact SemilatticeTreeConv.unitRight SemilatticeTree.leaf
  · exact SemilatticeTreeConv.idem SemilatticeTree.leaf

/-- ★ **Normalization** — every tree is convertible to `normalOf (slotPresenceOf tree)` (`⊥` or a single
slot).  Induction on the tree: `leaf` and `unitOp` are already normal, and `mulOp` normalizes both children
and joins them via `semilatticeMulNormal`. -/
theorem semilatticeTreeReducesToNormal (tree : SemilatticeTree) :
    SemilatticeTreeConv tree (normalOf (slotPresenceOf tree)) := by
  induction tree with
  | leaf => exact SemilatticeTreeConv.refl SemilatticeTree.leaf
  | unitOp => exact SemilatticeTreeConv.refl SemilatticeTree.unitOp
  | mulOp left right ihLeft ihRight =>
      exact SemilatticeTreeConv.trans
        (SemilatticeTreeConv.mulCongr ihLeft ihRight)
        (semilatticeMulNormal (slotPresenceOf left) (slotPresenceOf right))

/-! ## Completeness and the decision -/

/-- ★ **Completeness** — equal slot-presence implies convertibility, through the common normal form. -/
theorem semilatticeTreeConv_complete {source target : SemilatticeTree}
    (presenceEq : slotPresenceOf source = slotPresenceOf target) : SemilatticeTreeConv source target := by
  have sourceReduces : SemilatticeTreeConv source (normalOf (slotPresenceOf source)) :=
    semilatticeTreeReducesToNormal source
  have targetReduces : SemilatticeTreeConv target (normalOf (slotPresenceOf target)) :=
    semilatticeTreeReducesToNormal target
  have normalEq : normalOf (slotPresenceOf source) = normalOf (slotPresenceOf target) :=
    congrArg normalOf presenceEq
  exact SemilatticeTreeConv.trans sourceReduces (normalEq.symm ▸ SemilatticeTreeConv.symm targetReduces)

/-- ★ **The decision** — convertibility in the walking bounded semilattice (single generator) is exactly
equality of the two-valued slot-presence, a trivially decidable check. -/
theorem semilatticeTreeConv_iff_slotPresence (source target : SemilatticeTree) :
    SemilatticeTreeConv source target ↔ slotPresenceOf source = slotPresenceOf target :=
  ⟨semilatticeTreeConv_sound, semilatticeTreeConv_complete⟩

/-! ## Groundings -/

/-- ★ **Idempotency does real work** — `m(leaf, leaf) ≈ leaf`, the move UNAVAILABLE in the commutative
monoid (where `m(leaf, leaf)` has leaf count 2, not 1). -/
theorem semilatticeIdemHolds :
    SemilatticeTreeConv (SemilatticeTree.mulOp SemilatticeTree.leaf SemilatticeTree.leaf) SemilatticeTree.leaf :=
  SemilatticeTreeConv.idem SemilatticeTree.leaf

/-- ★ **The decision in action (positive)** — a doubly-joined slot `m(m(leaf, leaf), leaf)` collapses to a
single slot `m(leaf, ⊥)`: both have slot-presence `present`, so they are convertible through completeness,
with no explicit rewrite path — the idempotent collapse the count-based walker cannot see. -/
theorem semilatticeDecidesEqualPresence :
    SemilatticeTreeConv
      (SemilatticeTree.mulOp (SemilatticeTree.mulOp SemilatticeTree.leaf SemilatticeTree.leaf) SemilatticeTree.leaf)
      (SemilatticeTree.mulOp SemilatticeTree.leaf SemilatticeTree.unitOp) :=
  semilatticeTreeConv_complete rfl

/-- ★ **The decision in action (negative)** — a slot is NOT convertible to bottom: their slot-presence
values differ (`present ≠ absent`), so by soundness no convertibility exists.  `SlotPresence.noConfusion`. -/
theorem semilatticeRejectsUnequalPresence :
    ¬ SemilatticeTreeConv SemilatticeTree.leaf SemilatticeTree.unitOp :=
  fun conv => SlotPresence.noConfusion (semilatticeTreeConv_sound conv)

/-! ## The marker -/

/-- ★ **The walking bounded semilattice is DECIDED (single generator).**  `= true` records that
`semilatticeTreeConv_iff_slotPresence` reduces the word problem to equality of the two-valued slot-presence
— idempotency collapses the commutative monoid's `ℕ` count to the two-element lattice `{⊥, ⊤}`.  The
COLOURED (multi-generator) bounded semilattice, decided by finite-set equality, is the honest successor
wall. -/
def fxWalkingSemilattice_hasSingleGeneratorDecision : Bool := true

end FX1Poly.Polygraph
