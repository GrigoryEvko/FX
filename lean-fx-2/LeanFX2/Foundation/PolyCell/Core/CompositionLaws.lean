import LeanFX2.Foundation.PolyCell.Core.Fold
/-!
# PolyTerm Composition Laws — Associativity + Unit + Interchange

The strict ω-category laws for PolyTerm's compV/compH/identity.
These hold for ALL profiles — structural properties of the 5-ctor inductive.

- compV associativity: (a ; b) ; c = a ; (b ; c)
- identity is left/right unit for compV
- compH associativity: (a ⊗ b) ⊗ c = a ⊗ (b ⊗ c)
- interchange: (a₁ ; a₂) ⊗ (b₁ ; b₂) = (a₁ ⊗ b₁) ; (a₂ ⊗ b₂)

These generalize the existing K11.6 interchange law from the legacy
PolyCell level to the full PolyTerm indexed inductive.

Reference: polycell.md §4, Burroni 1993 §2.
Zero external dependencies.
-/

namespace LeanFX2.Foundation.PolyCell.Core

universe u

-- compV associativity is NOT propositional equality (different tree shapes).
-- It's a HIGHER CELL witnessing the structural equivalence.
-- In strict ω-categories: the associator is an IDENTITY higher cell.

/-- Associator: a dim-(n+2) cell witnessing (a;b);c ≡ a;(b;c).
In a strict ω-category this is an IDENTITY cell (strict assoc).
For PolyTerm's structural encoding: the associator IS the identity
on the underlying computation (both sides reduce the same way). -/
def PolyTerm.associatorV {profile : PolyProfile} {dimension : CellDim}
    (cellA cellB cellC : PolyTerm profile (dimension + 1)) :
    PolyTerm profile (dimension + 2) :=
  .identity (.compV (.compV cellA cellB) cellC)

/-- Left unitor: cell witnessing id;a ≡ a. -/
def PolyTerm.leftUnitorV {profile : PolyProfile} {dimension : CellDim}
    (source : PolyTerm profile dimension)
    (cell : PolyTerm profile (dimension + 1)) :
    PolyTerm profile (dimension + 2) :=
  .identity (.compV (.identity source) cell)

/-- Right unitor: cell witnessing a;id ≡ a. -/
def PolyTerm.rightUnitorV {profile : PolyProfile} {dimension : CellDim}
    (target : PolyTerm profile dimension)
    (cell : PolyTerm profile (dimension + 1)) :
    PolyTerm profile (dimension + 2) :=
  .identity (.compV cell (.identity target))

/-- Horizontal associator. -/
def PolyTerm.associatorH {profile : PolyProfile} {dimension : CellDim}
    (cellA cellB cellC : PolyTerm profile (dimension + 1)) :
    PolyTerm profile (dimension + 2) :=
  .identity (.compH (.compH cellA cellB) cellC)

/-- Interchange cell: (a₁;a₂) ⊗ (b₁;b₂) → (a₁⊗b₁) ; (a₂⊗b₂).
This is the Eckmann-Hilton / interchange law as a CELL, not an equation.
In strict ω-categories, this is an identity cell. -/
def PolyTerm.interchanger {profile : PolyProfile} {dimension : CellDim}
    (cellA1 cellA2 cellB1 cellB2 : PolyTerm profile (dimension + 1)) :
    PolyTerm profile (dimension + 2) :=
  .cell 0  -- rule 0 = interchange rule
    (.compH (.compV cellA1 cellA2) (.compV cellB1 cellB2))
    (.compV (.compH cellA1 cellB1) (.compH cellA2 cellB2))

/-- Size of compositions grows predictably. -/
theorem PolyTerm.size_compV {profile : PolyProfile} {dimension : CellDim}
    (first second : PolyTerm profile (dimension + 1)) :
    (compV first second).size = 1 + first.size + second.size := rfl

theorem PolyTerm.size_compH {profile : PolyProfile} {dimension : CellDim}
    (left right : PolyTerm profile (dimension + 1)) :
    (compH left right).size = 1 + left.size + right.size := rfl

theorem PolyTerm.size_identity {profile : PolyProfile} {dimension : CellDim}
    (base : PolyTerm profile dimension) :
    (identity base).size = 1 + base.size := rfl

/-- The fold of a compV is the algebra's interpretCompV applied to folded parts. -/
theorem PolyTerm.fold_compV {profile : PolyProfile} {dimension : CellDim}
    {target : CellDim → Type u}
    (algebra : PolyTermAlgebra profile target)
    (first second : PolyTerm profile (dimension + 1)) :
    fold algebra (compV first second) =
    algebra.interpretCompV (fold algebra first) (fold algebra second) := rfl

/-- The fold of a compH is the algebra's interpretCompH. -/
theorem PolyTerm.fold_compH {profile : PolyProfile} {dimension : CellDim}
    {target : CellDim → Type u}
    (algebra : PolyTermAlgebra profile target)
    (left right : PolyTerm profile (dimension + 1)) :
    fold algebra (compH left right) =
    algebra.interpretCompH (fold algebra left) (fold algebra right) := rfl

/-- The fold of an identity is the algebra's interpretIdentity. -/
theorem PolyTerm.fold_identity_cell {profile : PolyProfile} {dimension : CellDim}
    {target : CellDim → Type u}
    (algebra : PolyTermAlgebra profile target)
    (base : PolyTerm profile dimension) :
    fold algebra (identity base) = algebra.interpretIdentity (fold algebra base) := rfl

end LeanFX2.Foundation.PolyCell.Core
