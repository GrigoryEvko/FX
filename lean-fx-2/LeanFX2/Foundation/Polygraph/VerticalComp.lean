import LeanFX2.Foundation.Polygraph.ParallelPair

/-! # `VerticalChain` — sequential composition of `PolyCell` generators.

Burroni 1993 §1.1 / §2 free strict ω-category presentation: vertical
composition `α ∗_n β` of two `(n+2)`-cells along their `(n+1)`-boundary
requires `t_{n+1}(α) = s_{n+1}(β)` (target of α equals source of β at
the next-lower dimension).

`PolyCell` itself is the polygraph — only generators (atomic `atom` /
`arrow` / `cell` constructors) inhabit it.  Free vertical composites
live in `VerticalChain`: a finite sequence of `(n+2)`-cells each
linking to the next via cellSource / cellTarget identification.

## Construction

`VerticalChain startCell endCell` (at fixed `dim`, `sv`, `tv`):

* `identity startCell` — the empty / identity chain at `startCell`.
* `cons stepWitness sourceMatches targetMatches tail` — extend a chain
  starting at `midCell` to one starting at `startCell` by prepending an
  `(n+2)`-cell `stepWitness` with `cellSource = startCell` and
  `cellTarget = midCell`.

## Operations shipped here (K11.4 minimal scope)

* `VerticalChain.length` — number of `(n+2)`-cells composed.
* `VerticalChain.append` — sequential concatenation of two chains
  meeting at a shared midpoint.
* `VerticalChain.length_identity_eq_zero` — identity chain has length 0.
* `VerticalChain.length_cons_eq_succ_length_tail` — length of cons
  equals one plus length of tail.
* `VerticalChain.length_append_eq_sum_of_lengths` — append distributes
  length over sum.
* `VerticalChain.append_identity_left/right` — identity is left/right
  unit for append.

Verified zero-axiom via `#print axioms` per declaration. -/

namespace LeanFX2.Foundation.Polygraph

/-- A free vertical chain of `(dim+2)`-cells composing sequentially
from `startCell` to `endCell`. -/
inductive VerticalChain :
    {dim sv tv : Nat} →
    (startCell endCell : PolyCell (dim + 1) sv tv) →
    Type
  | identity {dim sv tv : Nat} (anchorCell : PolyCell (dim + 1) sv tv) :
      VerticalChain anchorCell anchorCell
  | cons {dim sv tv : Nat}
         {startCell midCell endCell : PolyCell (dim + 1) sv tv}
         (stepWitness : PolyCell (dim + 2) sv tv)
         (sourceMatches : cellSource stepWitness = startCell)
         (targetMatches : cellTarget stepWitness = midCell)
         (tailChain : VerticalChain midCell endCell) :
      VerticalChain startCell endCell

namespace VerticalChain

/-- Number of `(dim+2)`-cells composed in a chain.  Identity has
length 0; each `cons` adds one. -/
def length {dim sv tv : Nat}
    {startCell endCell : PolyCell (dim + 1) sv tv}
    (chain : VerticalChain startCell endCell) : Nat :=
  match chain with
  | identity _ => 0
  | cons _ _ _ tailChain => tailChain.length + 1

@[simp] theorem length_identity_eq_zero {dim sv tv : Nat}
    (anchorCell : PolyCell (dim + 1) sv tv) :
    (identity anchorCell).length = 0 := rfl

@[simp] theorem length_cons_eq_succ_length_tail {dim sv tv : Nat}
    {startCell midCell endCell : PolyCell (dim + 1) sv tv}
    (stepWitness : PolyCell (dim + 2) sv tv)
    (sourceMatches : cellSource stepWitness = startCell)
    (targetMatches : cellTarget stepWitness = midCell)
    (tailChain : VerticalChain midCell endCell) :
    (cons stepWitness sourceMatches targetMatches tailChain).length =
      tailChain.length + 1 := rfl

/-- Sequential concatenation of two vertical chains meeting at a
shared midpoint. -/
def append {dim sv tv : Nat}
    {startCell midCell endCell : PolyCell (dim + 1) sv tv}
    (firstChain : VerticalChain startCell midCell)
    (secondChain : VerticalChain midCell endCell) :
    VerticalChain startCell endCell :=
  match firstChain with
  | identity _ => secondChain
  | cons stepWitness sourceMatches targetMatches restChain =>
    cons stepWitness sourceMatches targetMatches (append restChain secondChain)

@[simp] theorem append_identity_left {dim sv tv : Nat}
    {startCell endCell : PolyCell (dim + 1) sv tv}
    (chain : VerticalChain startCell endCell) :
    append (identity startCell) chain = chain := rfl

theorem append_cons_unfold {dim sv tv : Nat}
    {startCell midCellInner midCell endCell : PolyCell (dim + 1) sv tv}
    (stepWitness : PolyCell (dim + 2) sv tv)
    (sourceMatches : cellSource stepWitness = startCell)
    (targetMatches : cellTarget stepWitness = midCellInner)
    (restChain : VerticalChain midCellInner midCell)
    (secondChain : VerticalChain midCell endCell) :
    append (cons stepWitness sourceMatches targetMatches restChain)
           secondChain =
    cons stepWitness sourceMatches targetMatches
         (append restChain secondChain) := rfl

theorem append_identity_right {dim sv tv : Nat}
    {startCell endCell : PolyCell (dim + 1) sv tv}
    (chain : VerticalChain startCell endCell) :
    append chain (identity endCell) = chain := by
  induction chain with
  | identity _ => rfl
  | cons stepWitness sourceMatches targetMatches restChain ih =>
    rw [append_cons_unfold, ih]

theorem length_append_eq_sum_of_lengths {dim sv tv : Nat}
    {startCell midCell endCell : PolyCell (dim + 1) sv tv}
    (firstChain : VerticalChain startCell midCell)
    (secondChain : VerticalChain midCell endCell) :
    (firstChain.append secondChain).length =
      firstChain.length + secondChain.length := by
  induction firstChain with
  | identity _ =>
    rw [append_identity_left, length_identity_eq_zero, Nat.zero_add]
  | cons stepWitness sourceMatches targetMatches restChain ih =>
    rw [append_cons_unfold,
        length_cons_eq_succ_length_tail,
        length_cons_eq_succ_length_tail,
        ih,
        Nat.add_right_comm]

/-- Sequential composition of two vertically composable
`(dim+2)`-cells.  Returns a length-2 chain. -/
def composeTwoCells {dim sv tv : Nat}
    {startCell midCell endCell : PolyCell (dim + 1) sv tv}
    (firstCell secondCell : PolyCell (dim + 2) sv tv)
    (firstSourceMatches : cellSource firstCell = startCell)
    (firstTargetMatches : cellTarget firstCell = midCell)
    (secondSourceMatches : cellSource secondCell = midCell)
    (secondTargetMatches : cellTarget secondCell = endCell) :
    VerticalChain startCell endCell :=
  cons firstCell firstSourceMatches firstTargetMatches
    (cons secondCell secondSourceMatches secondTargetMatches
      (identity endCell))

theorem composeTwoCells_length_eq_two {dim sv tv : Nat}
    {startCell midCell endCell : PolyCell (dim + 1) sv tv}
    (firstCell secondCell : PolyCell (dim + 2) sv tv)
    (firstSourceMatches : cellSource firstCell = startCell)
    (firstTargetMatches : cellTarget firstCell = midCell)
    (secondSourceMatches : cellSource secondCell = midCell)
    (secondTargetMatches : cellTarget secondCell = endCell) :
    (composeTwoCells firstCell secondCell
        firstSourceMatches firstTargetMatches
        secondSourceMatches secondTargetMatches).length = 2 := by
  show (cons firstCell firstSourceMatches firstTargetMatches
         (cons secondCell secondSourceMatches secondTargetMatches
           (identity endCell))).length = 2
  rw [length_cons_eq_succ_length_tail,
      length_cons_eq_succ_length_tail,
      length_identity_eq_zero]

end VerticalChain

end LeanFX2.Foundation.Polygraph
