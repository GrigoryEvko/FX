import LeanFX2.Foundation.PolyCell.Core.PolyProfile
/-!
# PolyTerm — Structural Cell Syntax

This file defines the small indexed syntax that the PolyCell plan wants to
grow into the future cell substrate.  The current implementation is only the
structural core: constructor ids and payloads are `Nat`, boundary compatibility
is not indexed into the type, and no legacy replacement bridge is present here.

Features (Π, Σ, modal, cubical, etc.) are NOT constructors — they are
intended to be entries in the profile's algebra.  The present file does not
yet prove that adding such entries avoids every legacy cascade.

The 5 constructors:
- atom: dim-0 generators (terms and types)
- cell: dim-(n+1) generators (reductions and coherences)
- compV: vertical composition (sequential reduction chains)
- compH: horizontal composition (parallel/concurrent cells)
- identity: degenerate higher cell (identity on a lower cell)

Reference target: polycell.md §4.
Zero external dependencies.
-/

namespace LeanFX2.Foundation.PolyCell.Core

/-- Cell dimension. -/
abbrev CellDim := Nat

/-- A cell identifier within a profile (which generator produced it). -/
abbrev CellId := Nat

/-- Structural cell syntax parameterized by a profile and indexed by dimension.
Induction over this syntax has five constructor cases.  Generator-specific
well-formedness, payload decoding, and boundary checks are deliberately outside
this inductive until the corresponding profile axes are mechanized. -/
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
  | .cell _ _ _ => false
  | .compV _ _ => false
  | .compH _ _ => false
  | .identity _ => false

/-- Is this a composite cell (built via compV/compH/identity)? -/
def PolyTerm.isComposite {profile : PolyProfile} {dimension : CellDim} :
    PolyTerm profile dimension → Bool
  | .compV _ _ => true
  | .compH _ _ => true
  | .identity _ => true
  | .atom _ _ => false
  | .cell _ _ _ => false

/-- Is this an identity cell? -/
def PolyTerm.isIdentity {profile : PolyProfile} {dimension : CellDim} :
    PolyTerm profile dimension → Bool
  | .identity _ => true
  | .atom _ _ => false
  | .cell _ _ _ => false
  | .compV _ _ => false
  | .compH _ _ => false

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
  cases term with
  | atom _ _ =>
      exact Nat.zero_lt_one
  | cell _ source target =>
      dsimp [PolyTerm.size]
      exact Nat.add_pos_left
        (Nat.add_pos_left Nat.zero_lt_one source.size) target.size
  | compV first second =>
      dsimp [PolyTerm.size]
      exact Nat.add_pos_left
        (Nat.add_pos_left Nat.zero_lt_one first.size) second.size
  | compH left right =>
      dsimp [PolyTerm.size]
      exact Nat.add_pos_left
        (Nat.add_pos_left Nat.zero_lt_one left.size) right.size
  | identity base =>
      dsimp [PolyTerm.size]
      exact Nat.add_pos_left Nat.zero_lt_one base.size

/-- Retarget a structural cell from one profile parameter to another.

The current `PolyTerm` syntax stores generator ids and payloads as structural
data, so this operation only changes the profile parameter and preserves the
tree exactly.  It is not a semantic interpretation between two profiles. -/
def PolyTerm.retargetProfile {sourceProfile targetProfile : PolyProfile}
    {dimension : CellDim} :
    PolyTerm sourceProfile dimension → PolyTerm targetProfile dimension
  | .atom cellId payload => .atom cellId payload
  | .cell ruleId source target =>
      .cell ruleId source.retargetProfile target.retargetProfile
  | .compV first second =>
      .compV first.retargetProfile second.retargetProfile
  | .compH left right =>
      .compH left.retargetProfile right.retargetProfile
  | .identity base =>
      .identity base.retargetProfile

/-- Retargeting within the same profile is the identity on structural cells. -/
theorem PolyTerm.retargetProfile_self {profile : PolyProfile}
    {dimension : CellDim}
    (term : PolyTerm profile dimension) :
    term.retargetProfile (targetProfile := profile) = term := by
  induction term with
  | atom _ _ => rfl
  | cell _ _ _ sourceInduction targetInduction =>
      dsimp [PolyTerm.retargetProfile]
      rw [sourceInduction, targetInduction]
  | compV _ _ firstInduction secondInduction =>
      dsimp [PolyTerm.retargetProfile]
      rw [firstInduction, secondInduction]
  | compH _ _ leftInduction rightInduction =>
      dsimp [PolyTerm.retargetProfile]
      rw [leftInduction, rightInduction]
  | identity _ baseInduction =>
      dsimp [PolyTerm.retargetProfile]
      rw [baseInduction]

/-- Structural profile retargeting composes exactly. -/
theorem PolyTerm.retargetProfile_comp
    {sourceProfile middleProfile targetProfile : PolyProfile}
    {dimension : CellDim}
    (term : PolyTerm sourceProfile dimension) :
    (term.retargetProfile (targetProfile := middleProfile)).retargetProfile
      (targetProfile := targetProfile) =
    term.retargetProfile (targetProfile := targetProfile) := by
  induction term with
  | atom _ _ => rfl
  | cell _ _ _ sourceInduction targetInduction =>
      dsimp [PolyTerm.retargetProfile]
      rw [sourceInduction, targetInduction]
  | compV _ _ firstInduction secondInduction =>
      dsimp [PolyTerm.retargetProfile]
      rw [firstInduction, secondInduction]
  | compH _ _ leftInduction rightInduction =>
      dsimp [PolyTerm.retargetProfile]
      rw [leftInduction, rightInduction]
  | identity _ baseInduction =>
      dsimp [PolyTerm.retargetProfile]
      rw [baseInduction]

/-- Retargeting to a profile and then back to the source profile is identity. -/
theorem PolyTerm.retargetProfile_roundtrip
    {sourceProfile targetProfile : PolyProfile}
    {dimension : CellDim}
    (term : PolyTerm sourceProfile dimension) :
    (term.retargetProfile (targetProfile := targetProfile)).retargetProfile
      (targetProfile := sourceProfile) = term := by
  rw [PolyTerm.retargetProfile_comp, PolyTerm.retargetProfile_self]

/-- Every FX term is a PolyTerm at dim 0. -/
abbrev FXCell (profile : PolyProfile) := PolyTerm profile

/-- Provisional type-cell recognizer using the current raw id range convention. -/
def PolyTerm.isTypeCell {profile : PolyProfile} :
    PolyTerm profile 0 → Bool
  | .atom cellId _ => cellId ≥ 64  -- type-code generators are ids 64-77

/-- Provisional term-cell recognizer using the current raw id range convention. -/
def PolyTerm.isTermCell {profile : PolyProfile} :
    PolyTerm profile 0 → Bool
  | .atom cellId _ => cellId < 64  -- term generators are ids 0-63

/-- Provisional dim-1 step recognizer.  It has no thinness or boundary check. -/
def PolyTerm.isStepCell {profile : PolyProfile} :
    PolyTerm profile 1 → Bool := fun term =>
  match term.isIdentity with
  | true => false
  | false => true

end LeanFX2.Foundation.PolyCell.Core
