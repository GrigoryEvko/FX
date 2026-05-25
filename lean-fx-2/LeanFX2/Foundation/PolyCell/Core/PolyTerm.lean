import LeanFX2.Foundation.PolyCell.Core.PolyProfile
/-!
# PolyTerm — THE 5-Constructor Universal Cell Type

The single indexed inductive that REPLACES the current 75-ctor Term +
112-ctor Step + 133-ctor Step.par with 5 structural constructors.

Features (Π, Σ, modal, cubical, etc.) are NOT constructors — they are
entries in the profile's algebra. Adding a new feature = adding one
Generator value. Zero cascade.

The 5 constructors:
- atom: dim-0 generators (terms and types)
- cell: dim-(n+1) generators (reductions and coherences)
- compV: vertical composition (sequential reduction chains)
- compH: horizontal composition (parallel/concurrent cells)
- identity: degenerate higher cell (identity on a lower cell)

Reference: polycell.md §4.
Zero external dependencies.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- Cell dimension. -/
abbrev CellDim := Nat

/-- A cell identifier within a profile (which generator produced it). -/
abbrev CellId := Nat

/-- THE universal cell type. Parameterized by PolyProfile, indexed by
dimension. This is the type that collapses the cascade:

- Current FX: 75 Term ctors + 112 Step ctors + 133 Step.par ctors = 320+
- PolyTerm: 5 structural ctors, REGARDLESS of generator count.

Induction over PolyTerm is ALWAYS a 5-case split. Adding generators
to the profile does NOT add constructors — it adds values to `cellId`. -/
inductive PolyTerm (profile : PolyProfile) : (dimension : CellDim) → Type where
  /-- Dim-0 generator: an atomic cell (term or type). The `cellId`
  identifies WHICH of the profile's generators produced this cell.
  Payload carries the generator-specific data (children, binders, etc.). -/
  | atom :
    (cellId : CellId) →
    (payload : Nat) →
    PolyTerm profile 0

  /-- Dim-(n+1) generator: a reduction/coherence cell between lower cells.
  `ruleId` identifies the reduction rule (Step label).
  `source` and `target` are the cells it connects. -/
  | cell :
    {dimension : CellDim} →
    (ruleId : CellId) →
    (source : PolyTerm profile dimension) →
    (target : PolyTerm profile dimension) →
    PolyTerm profile (dimension + 1)

  /-- Vertical composition: sequential composition of two cells sharing
  an intermediate boundary (target of first = source of second). -/
  | compV :
    {dimension : CellDim} →
    (first : PolyTerm profile (dimension + 1)) →
    (second : PolyTerm profile (dimension + 1)) →
    PolyTerm profile (dimension + 1)

  /-- Horizontal composition: parallel composition of two cells at the
  same dimension (disjoint footprints composed via Gray tensor). -/
  | compH :
    {dimension : CellDim} →
    (left : PolyTerm profile (dimension + 1)) →
    (right : PolyTerm profile (dimension + 1)) →
    PolyTerm profile (dimension + 1)

  /-- Identity: the degenerate (n+1)-cell on an n-cell (does nothing). -/
  | identity :
    {dimension : CellDim} →
    (base : PolyTerm profile dimension) →
    PolyTerm profile (dimension + 1)

/-- Dimension of a PolyTerm (extracted from index). -/
def PolyTerm.dim {profile : PolyProfile} {dimension : CellDim} :
    PolyTerm profile dimension → CellDim := fun _ => dimension

/-- Is this an atomic (generator-level) cell? -/
def PolyTerm.isAtom {profile : PolyProfile} {dimension : CellDim} :
    PolyTerm profile dimension → Bool
  | .atom _ _ => true
  | _ => false

/-- Is this a composite cell (built via compV/compH/identity)? -/
def PolyTerm.isComposite {profile : PolyProfile} {dimension : CellDim} :
    PolyTerm profile dimension → Bool
  | .compV _ _ => true
  | .compH _ _ => true
  | .identity _ => true
  | _ => false

/-- Structural size (for well-founded recursion). -/
def PolyTerm.size {profile : PolyProfile} {dimension : CellDim} :
    PolyTerm profile dimension → Nat
  | .atom _ _ => 1
  | .cell _ source target => 1 + source.size + target.size
  | .compV first second => 1 + first.size + second.size
  | .compH left right => 1 + left.size + right.size
  | .identity base => 1 + base.size

/-- Size is always positive. -/
theorem PolyTerm.size_pos {profile : PolyProfile} {dimension : CellDim}
    (term : PolyTerm profile dimension) : term.size > 0 := by
  cases term <;> unfold size <;> omega

/-- Every FX term is a PolyTerm at dim 0. -/
abbrev FXCell (profile : PolyProfile) := PolyTerm profile

/-- Type cells: dim-0 atoms that represent types. -/
def PolyTerm.isTypeCell {profile : PolyProfile} :
    PolyTerm profile 0 → Bool
  | .atom cellId _ => cellId ≥ 64  -- type-code generators are ids 64-77
  | _ => false

/-- Term cells: dim-0 atoms that represent values. -/
def PolyTerm.isTermCell {profile : PolyProfile} :
    PolyTerm profile 0 → Bool
  | .atom cellId _ => cellId < 64  -- term generators are ids 0-63
  | _ => false

/-- Step cells: dim-1 cells (non-identity). -/
def PolyTerm.isStepCell {profile : PolyProfile} :
    PolyTerm profile 1 → Bool
  | .cell _ _ _ => true
  | .identity _ => false
  | _ => true

end LeanFX2.Foundation.PolyCell.Core
