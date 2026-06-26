import FX1Poly.Tier0.Term.Core.RawTerm

/-! # FX1Poly/Tier0/Term/RawTermSize — the structural size of a raw term + child strict-decrease

A STRUCTURAL size measure on `RawTerm` / `RawTermChildren`, mutual over the well-scoped mutual inductive (exactly
as `RawCell.dim` is structural over `RawCell`).  Every `mkGen` cell is strictly larger than its children spine,
and every child in a `childCons` is strictly smaller than the cell containing it.

This is the well-foundedness foundation for STRUCTURAL-FUEL recursion over raw terms (the propext-safe substitute
for `WellFounded.fix`, which leaks `propext` + `Quot.sound` here): a fuel bound `subterm.size ≤ n` lets a proof
recurse from a `mkGen` cell into its children (all of size `< n`) by ordinary induction on the `Nat` fuel.  It is
the measure the subject-reduction self-reference (`UnionChildSubjectReduction`, the SR full arc's last open node)
is to be discharged against — the congruence closer re-types a STEPPED CHILD, which is strictly smaller than the
stepping cell, so a fuel-bounded single-step SR supplies it.

## Zero-axiom

Mutual STRUCTURAL recursion with a constant `Nat` motive (no `termination_by`, no `WellFounded.fix`, no fuel) +
`rfl` unfolders + clean `Nat` order lemmas (`Nat.lt_succ_self`, `Nat.lt_succ_of_le`, `Nat.le_add_right`).  No
`axiom`, `sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, `omega`.  Per-declaration audit-gated in
`FX1PolyAudit/`. -/

namespace FX1Poly.Core

mutual
  /-- The structural size of a raw term: one plus the size of its children spine.  Mutual STRUCTURAL recursion
  with constant `Nat` motive — propext-clean, exactly as `RawCell.dim`. -/
  def RawTerm.size {scope : Nat} : RawTerm scope → Nat
    | .mkGen _generator _payload children => children.size + 1

  /-- The structural size of a children spine: the sum of the children's sizes, one per `childCons`. -/
  def RawTermChildren.size {shifts : List Nat} {scope : Nat} :
      RawTermChildren shifts scope → Nat
    | .childNil => 0
    | .childCons childHead childTail => childHead.size + childTail.size + 1
end

/-- Unfolder: a `mkGen` cell's size is one plus its children spine's size. -/
theorem RawTerm.size_mkGen {scope : Nat} (generator : Generator) (payload : generator.payload scope)
    (children : RawTermChildren generator.binderShifts scope) :
    (RawTerm.mkGen generator payload children).size = children.size + 1 := rfl

/-- Unfolder: the empty children spine has size zero. -/
theorem RawTermChildren.size_childNil {scope : Nat} :
    (RawTermChildren.childNil : RawTermChildren [] scope).size = 0 := rfl

/-- Unfolder: a `childCons` spine's size is the head's size plus the tail spine's size plus one. -/
theorem RawTermChildren.size_childCons {scope shift : Nat} {restShifts : List Nat}
    (childHead : RawTerm (scope + shift)) (childTail : RawTermChildren restShifts scope) :
    (RawTermChildren.childCons childHead childTail).size = childHead.size + childTail.size + 1 := rfl

/-- ★ A children spine is STRICTLY smaller than the `mkGen` cell built over it — the cell adds one node. -/
theorem RawTermChildren.size_lt_mkGen {scope : Nat} (generator : Generator) (payload : generator.payload scope)
    (children : RawTermChildren generator.binderShifts scope) :
    children.size < (RawTerm.mkGen generator payload children).size :=
  Nat.lt_succ_self children.size

/-- ★ The HEAD child of a `childCons` is strictly smaller than the spine — the spine adds the head plus a node. -/
theorem RawTermChildren.childHead_size_lt {scope shift : Nat} {restShifts : List Nat}
    (childHead : RawTerm (scope + shift)) (childTail : RawTermChildren restShifts scope) :
    childHead.size < (RawTermChildren.childCons childHead childTail).size :=
  Nat.lt_succ_of_le (Nat.le_add_right childHead.size childTail.size)

/-- The TAIL spine of a `childCons` is strictly smaller than the spine. -/
theorem RawTermChildren.childTail_size_lt {scope shift : Nat} {restShifts : List Nat}
    (childHead : RawTerm (scope + shift)) (childTail : RawTermChildren restShifts scope) :
    childTail.size < (RawTermChildren.childCons childHead childTail).size :=
  Nat.lt_succ_of_le (Nat.le_add_left childTail.size childHead.size)

/-- ★ **The child strict-decrease, transitively.**  The HEAD child of a `childCons` spine is strictly smaller
than ANY `mkGen` cell built over that very spine — chaining `childHead_size_lt` (head `<` spine) through
`size_lt_mkGen` (spine `<` cell).  This is the well-foundedness step a fuel-bounded single-step SR recurses on
once the cell's children are exposed as a concrete `childCons` (so the spine `children` is literally
`childCons childHead childTail`). -/
theorem RawTerm.childHead_size_lt_ofConsSpine {scope shift : Nat} {restShifts : List Nat}
    (generator : Generator) (payload : generator.payload scope)
    (childHead : RawTerm (scope + shift)) (childTail : RawTermChildren restShifts scope)
    (children : RawTermChildren generator.binderShifts scope)
    (spineIsCons : children.size = (RawTermChildren.childCons childHead childTail).size) :
    childHead.size < (RawTerm.mkGen generator payload children).size := by
  rw [RawTerm.size_mkGen, spineIsCons, RawTermChildren.size_childCons]
  exact Nat.lt_succ_of_le (Nat.le_succ_of_le (Nat.le_add_right childHead.size childTail.size))

end FX1Poly.Core
