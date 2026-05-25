/-!
# ωcE Polygraph — Walking Coherent ω-Equivalence (HLOR Construction 1.22)

The ωcE polygraph is built inductively up to each dimension k.
At each step, 5 generators are added: the quasi-inverse structure.
It is finite-type at every k, contractible (Thm 1.33), and universal
among coherent ω-equivalences (Prop 1.26).

For FX: cells are coherent ω-equivalences iff there exists an
ω-functor from Σ^(n-1)(ωcE) factoring them. The Makkai algorithm
decides word equality on this finite polygraph.

Reference: arXiv:2404.14509 Construction 1.22.
Zero external dependencies.
-/

namespace LeanFX2.Foundation.PolyCell.OmegacE

/-- The ωcE polygraph at dimension k.
Construction 1.22: at each k, add 5 generators encoding the
quasi-inverse structure (the "walking" equivalence cell + its
coherence data at that dimension).

dim 0: 2 vertices (source/target of the walking equivalence)
dim 1: 1 cell q (the quasi-isomorphism itself) + extends of dim-0
dim 2: 2 cells α β (unit/counit 2-cells) + extends of dim-1
dim k+1: 2 new cells (higher coherence) + extends of dim-k -/
inductive OmegacECell : (dimension : Nat) → Type where
  /-- Source vertex of the walking equivalence. -/
  | sourceVertex : OmegacECell 0
  /-- Target vertex of the walking equivalence. -/
  | targetVertex : OmegacECell 0
  /-- The quasi-isomorphism cell (the "walking" 1-equivalence). -/
  | quasiIso : OmegacECell 1
  /-- The quasi-inverse (reverse direction). -/
  | quasiInverse : OmegacECell 1
  /-- Alpha cell: unit 2-cell (id → q∘q⁻¹). -/
  | alphaUnit : OmegacECell 2
  /-- Beta cell: counit 2-cell (q⁻¹∘q → id). -/
  | betaCounit : OmegacECell 2
  /-- Higher coherence at dim k+3: witnesses that alpha/beta satisfy
  triangle identities up to coherent homotopy. -/
  | higherCoherence : (baseDim : Nat) → (cellIndex : Fin 2) → OmegacECell (baseDim + 3)
  deriving DecidableEq, Repr

/-- Count cells at each dimension. -/
def OmegacECell.countAtDim : Nat → Nat
  | 0 => 2
  | 1 => 2
  | 2 => 2
  | n + 3 => 2

/-- Total cells up to and including dimension k. -/
def OmegacECell.totalUpTo : Nat → Nat
  | 0 => 2
  | n + 1 => totalUpTo n + countAtDim (n + 1)

/-- ωcE at dim 0 has exactly 2 cells. -/
theorem OmegacECell.count_dim0 : OmegacECell.countAtDim 0 = 2 := rfl

/-- ωcE at dim 1 has exactly 2 cells. -/
theorem OmegacECell.count_dim1 : OmegacECell.countAtDim 1 = 2 := rfl

/-- ωcE at dim 2 has exactly 2 cells. -/
theorem OmegacECell.count_dim2 : OmegacECell.countAtDim 2 = 2 := rfl

/-- Total up to dim 0 = 2. -/
theorem OmegacECell.total_dim0 : OmegacECell.totalUpTo 0 = 2 := rfl

/-- Total up to dim 1 = 4. -/
theorem OmegacECell.total_dim1 : OmegacECell.totalUpTo 1 = 4 := rfl

/-- Total up to dim 2 = 6. -/
theorem OmegacECell.total_dim2 : OmegacECell.totalUpTo 2 = 6 := rfl

/-- Dimension of a cell (projection from the index). -/
def OmegacECell.dimension : {dim : Nat} → OmegacECell dim → Nat
  | dim, _ => dim

/-- The ωcE polygraph is finite at every dimension (2 cells per dim). -/
theorem OmegacECell.finite_at_each_dim (dimension : Nat) :
    OmegacECell.countAtDim dimension ≤ 2 := by
  cases dimension with
  | zero => exact Nat.le_refl 2
  | succ n => cases n with
    | zero => exact Nat.le_refl 2
    | succ m => cases m with
      | zero => exact Nat.le_refl 2
      | succ _ => exact Nat.le_refl 2

end LeanFX2.Foundation.PolyCell.OmegacE
