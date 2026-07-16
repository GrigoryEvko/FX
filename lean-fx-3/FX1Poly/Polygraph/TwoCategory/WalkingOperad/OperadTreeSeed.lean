/-! # WalkingOperad/OperadTreeSeed — the walking (planar, single-coloured) operad for MONOIDS: signature + tree-pasting relation

The presentation of the free planar (non-symmetric) single-coloured operad `Ass_unital` presenting MONOIDS as a
signature: two generating operations — a binary multiplication `m : arity 2` and a nullary unit `e : arity 0` —
together with the operad identity `id ∈ operad(1)` (an arity-1 input slot).  The relations imposed on the free
operad are the monoid laws, phrased as tree-pasting (grafting) convertibilities:

* **associativity** `m∘(m, id) = m∘(id, m)` — `m(m(x,y),z) ≈ m(x, m(y,z))`;
* **left unit** `m∘(e, id) = id` — `m(e, x) ≈ x`;
* **right unit** `m∘(id, e) = id` — `m(x, e) ≈ x`.

## ★ Why a NEW carrier — an operad is not a category

The generic 2-computad substrate (`FX1Poly/Polygraph/Computad/Signature.lean`) has `ModalityPath`, the free
CATEGORY: linear composable words, single-input composition by concatenation.  An operad composes by GRAFTING /
tree substitution — operations carry ARITIES (n inputs, 1 output), and the free planar operad's arity-`n` part
is the set of planar trees with `n` leaves whose internal nodes are arity-matched generators.  `ModalityPath`
captures only the arity-1 sub-operad (a one-object category = a monoid); the binary `m : 2 → 1` has NO
`ModalityPath` representation.  So brick 1 introduces a fresh inductive tree carrier `OperadTree` and does NOT
instantiate `ModeSignature` (a 2-computad over a category, not a multicategory).

## ★ Why the carrier is UN-INDEXED (not `Tree : Nat → Type`)

If the carrier were arity-indexed, the associativity relation would be HETEROGENEOUS — LHS index `(a+b)+c`,
RHS index `a+(b+c)`, not definitionally equal — forcing a transport along `Nat.add_assoc` (a propext-leak
hazard and a proof headache).  Un-indexed carrier ⟹ homogeneous `OperadTreeConv` ⟹ `arityOf` is a genuine
`Nat` structural fold (exactly the braid-permutation analogy: `BraidThreePermutation`).

## Scope — BRICK 1

This file ships the SIGNATURE (generators + arities, the arity-slot occupancy view) and the monoid-law
tree-pasting convertibility.  The soundness invariant `arityOf : OperadTree → Nat` (leaf / total-arity count)
and the SOUNDNESS theorem (convertible trees ⟹ equal arity) live in `OperadTreeArity`.  The FULL word-problem
DECISION (right-comb normal form for the arity-generic free operad) is WP-OPERAD BRICK 2 — NOT attempted here.

Raw Lean 4 + Init; the convertibility is an inductive `Prop`; per-declaration `#assert_no_axioms` gated in the
audit twin.  Free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1Poly.Polygraph

/-! ## The operad tree carrier -/

/-- ★ The **operad-tree carrier** of the walking monoid operad: an UN-INDEXED planar tree over the two monoid
generators.  `leaf` is an arity-1 input slot (the operad identity `id ∈ operad(1)`); `unitOp` is the nullary
generator `e : arity 0`; `mulOp` grafts two subtrees under the binary generator `m : arity 2`.  A closed
`OperadTree` is exactly a planar-tree operation of the free `{m, e}` operad, and its number of `leaf`s is its
total arity. -/
inductive OperadTree where
  /-- An arity-1 input slot — the operad identity `id ∈ operad(1)`. -/
  | leaf
  /-- The nullary generator `e : arity 0` (the monoid unit). -/
  | unitOp
  /-- The binary generator `m : arity 2` grafting the left and right subtrees (`m(left, right)`). -/
  | mulOp : OperadTree → OperadTree → OperadTree

/-! ## The generating operations and their arities -/

/-- The two generating operations of the monoid operad: `mul` (the binary `m`) and `unit` (the nullary `e`). -/
inductive OperadGenerator where
  /-- The binary multiplication generator `m`. -/
  | mul
  /-- The nullary unit generator `e`. -/
  | unit

/-- The **arity** of each generator: `mul ↦ 2`, `unit ↦ 0`.  A full-enumeration structural fold (no wildcard),
propext-clean. -/
def generatorArity : OperadGenerator → Nat
  | .mul => 2
  | .unit => 0

/-- Smoke: the multiplication generator has arity 2. -/
theorem generatorArity_mul : generatorArity OperadGenerator.mul = 2 := rfl

/-- Smoke: the unit generator has arity 0. -/
theorem generatorArity_unit : generatorArity OperadGenerator.unit = 0 := rfl

/-! ## The arity-slot signature (orientation-only occupancy view)

The signature of a single-coloured operad is, per arity `n`, the SET of arity-`n` generators.  For the monoid
operad that set is a singleton at arities 0 and 2 and empty elsewhere; below it is the arity-indexed family
`OperadSignature := Nat → Type` with `0, 2 ↦ Unit` and everything else `↦ Empty`.  This is the ORIENTATION-only
signature; brick 1 does NOT build the generic arity-`n` vector-node tree from an arbitrary such signature —
that (the free operad on an arbitrary signature) is a later, arity-generic brick. -/

/-- A single-coloured operad **signature**: an arity-indexed family of generator sets. -/
def OperadSignature := Nat → Type

/-- ★ The **monoid-operad signature**: one binary generator (`m : arity 2 ↦ Unit`), one nullary generator
(`e : arity 0 ↦ Unit`), and NO generators at any other arity (`↦ Empty`).  Arity 1 is `Empty` — there is no
generator of arity 1; the arity-1 slot is exactly the operad identity (`leaf`), not a generator. -/
def monoidOperadSignature : OperadSignature := fun arity =>
  match arity with
  | 0 => Unit
  | 2 => Unit
  | _ => Empty

/-- Smoke: there is a generator at arity 2 (the binary `m`). -/
theorem monoidOperadSignature_two : monoidOperadSignature 2 = Unit := rfl

/-- Smoke: there is a generator at arity 0 (the nullary `e`). -/
theorem monoidOperadSignature_zero : monoidOperadSignature 0 = Unit := rfl

/-- Smoke: there is NO generator at arity 1 — the arity-1 slot is the operad identity (`leaf`), not a
generator. -/
theorem monoidOperadSignature_one : monoidOperadSignature 1 = Empty := rfl

/-- Smoke: there is NO generator at arity 3 (the signature has only the binary and nullary generators). -/
theorem monoidOperadSignature_three : monoidOperadSignature 3 = Empty := rfl

/-! ## Concrete sample trees -/

/-- The associativity relation's left-hand tree `m(m(leaf, leaf), leaf)` — a left-nested product of three
input slots. -/
def operadAssocLeftTree : OperadTree :=
  OperadTree.mulOp (OperadTree.mulOp OperadTree.leaf OperadTree.leaf) OperadTree.leaf

/-- The associativity relation's right-hand tree `m(leaf, m(leaf, leaf))` — the right-nested product of the
same three input slots. -/
def operadAssocRightTree : OperadTree :=
  OperadTree.mulOp OperadTree.leaf (OperadTree.mulOp OperadTree.leaf OperadTree.leaf)

/-- The left-unit relation's left-hand tree `m(unitOp, leaf)` — the unit multiplied on the left of an input
slot. -/
def operadUnitLeftTree : OperadTree :=
  OperadTree.mulOp OperadTree.unitOp OperadTree.leaf

/-- The right-unit relation's left-hand tree `m(leaf, unitOp)` — the unit multiplied on the right of an input
slot. -/
def operadUnitRightTree : OperadTree :=
  OperadTree.mulOp OperadTree.leaf OperadTree.unitOp

/-! ## The monoid-law tree-pasting convertibility -/

/-- ★ The **tree-pasting convertibility** of the walking monoid operad — the free-operad convertibility of the
`{m, e}` signature closed under the three monoid laws (associativity, left unit, right unit), the FULL
tree-congruence (reaching into BOTH children of a `mulOp`), and `refl` / `symm` / `trans`.  Two trees denote the
same operation of the monoid operad exactly when they are `OperadTreeConv`-related.  The `mulCongr` generator is
the tree analog of the braid walker's single-slot `consCongr`: it whiskers a convertibility under a grafting
node, and (with the root-firing laws + `symm` / `trans`) generates the full operad congruence. -/
inductive OperadTreeConv : OperadTree → OperadTree → Prop where
  /-- **Associativity** `m(m(left, middle), right) ≈ m(left, m(middle, right))` — grafting is associative. -/
  | assoc (left middle right : OperadTree) :
      OperadTreeConv
        (OperadTree.mulOp (OperadTree.mulOp left middle) right)
        (OperadTree.mulOp left (OperadTree.mulOp middle right))
  /-- **Left unit** `m(unitOp, subtree) ≈ subtree` — the nullary unit is a left identity for grafting. -/
  | unitLeft (subtree : OperadTree) :
      OperadTreeConv (OperadTree.mulOp OperadTree.unitOp subtree) subtree
  /-- **Right unit** `m(subtree, unitOp) ≈ subtree` — the nullary unit is a right identity for grafting. -/
  | unitRight (subtree : OperadTree) :
      OperadTreeConv (OperadTree.mulOp subtree OperadTree.unitOp) subtree
  /-- **Congruence under a grafting node** — reaching into BOTH children: `leftOld ≈ leftNew` and
  `rightOld ≈ rightNew` give `m(leftOld, rightOld) ≈ m(leftNew, rightNew)`.  The tree analog of the braid
  walker's `consCongr`; makes the root-firing laws generate the full operad congruence. -/
  | mulCongr {leftOld leftNew rightOld rightNew : OperadTree} :
      OperadTreeConv leftOld leftNew → OperadTreeConv rightOld rightNew →
      OperadTreeConv (OperadTree.mulOp leftOld rightOld) (OperadTree.mulOp leftNew rightNew)
  /-- Reflexivity. -/
  | refl (tree : OperadTree) : OperadTreeConv tree tree
  /-- Symmetry. -/
  | symm {tree1 tree2 : OperadTree} : OperadTreeConv tree1 tree2 → OperadTreeConv tree2 tree1
  /-- Transitivity. -/
  | trans {tree1 tree2 tree3 : OperadTree} :
      OperadTreeConv tree1 tree2 → OperadTreeConv tree2 tree3 → OperadTreeConv tree1 tree3

/-- ★ **Associativity holds** — `m(m(leaf, leaf), leaf) ≈ m(leaf, m(leaf, leaf))` (at the three input-slot
operands): the grafting-associativity move. -/
theorem operadAssocHolds :
    OperadTreeConv operadAssocLeftTree operadAssocRightTree :=
  OperadTreeConv.assoc OperadTree.leaf OperadTree.leaf OperadTree.leaf

/-- ★ **Left unit holds** — `m(unitOp, leaf) ≈ leaf`: the unit is absorbed on the left. -/
theorem operadUnitLeftHolds :
    OperadTreeConv operadUnitLeftTree OperadTree.leaf :=
  OperadTreeConv.unitLeft OperadTree.leaf

/-- ★ **Right unit holds** — `m(leaf, unitOp) ≈ leaf`: the unit is absorbed on the right. -/
theorem operadUnitRightHolds :
    OperadTreeConv operadUnitRightTree OperadTree.leaf :=
  OperadTreeConv.unitRight OperadTree.leaf

/-- Smoke: the left-unit law fires WHISKERED under a grafting node — `m(m(unitOp, leaf), leaf) ≈ m(leaf, leaf)`
— exercising the full tree-congruence `mulCongr` (left child rewritten by the unit law, right child by `refl`). -/
theorem operadUnitLeftWhiskeredHolds :
    OperadTreeConv
      (OperadTree.mulOp operadUnitLeftTree OperadTree.leaf)
      (OperadTree.mulOp OperadTree.leaf OperadTree.leaf) :=
  OperadTreeConv.mulCongr operadUnitLeftHolds (OperadTreeConv.refl OperadTree.leaf)

end FX1Poly.Polygraph
