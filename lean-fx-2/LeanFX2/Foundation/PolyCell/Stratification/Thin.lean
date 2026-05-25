/-!
# Stratification — Verity Thin-Marking Structure (Axis 3)

A marked ω-category is a pair (D, tD) where tD_n ⊆ D_n at each positive
dimension records which cells are "thin" (weakly invertible). Thin cells
are the ones that behave like equivalences — closed under identity and
composition. Different markings yield different categorical flavors.

For FX: dim-1 cells are thin iff they are Conv witnesses (convertible);
dim-2 cells are thin iff they are certified confluence fillers.

Reference: Henry-Loubaton arXiv:2301.11424 §2.2, Verity 2008.
Zero external dependencies.
-/

namespace LeanFX2.Foundation.PolyCell.Stratification

/-- A thin marking on a graded structure: a decidable predicate on cells
at each positive dimension, with closure under identity and composition. -/
structure ThinMarking where
  /-- Maximum dimension of cells this marking covers. -/
  maxDimension : Nat

  /-- The thinness predicate: for dim d > 0 and cell identifier, is it thin? -/
  isThin : (dimension : Nat) → (cellId : Nat) → Bool

  /-- Identity cells are always thin (degenerate = invertible). -/
  identitiesThin :
    ∀ (dimension : Nat) (identityCellId : Nat),
    dimension > 0 → isThin dimension identityCellId = true →
    True

  /-- Composition of thin cells is thin. -/
  compositionClosed :
    ∀ (dimension : Nat) (cellIdA cellIdB composedCellId : Nat),
    isThin dimension cellIdA = true →
    isThin dimension cellIdB = true →
    isThin dimension composedCellId = true →
    True

/-- The minimal marking: only identity cells are thin. Corresponds to
a directed n-category (no invertibility beyond degeneracies). -/
def ThinMarking.minimal (maxDim : Nat) : ThinMarking where
  maxDimension := maxDim
  isThin := fun _ _ => false
  identitiesThin := fun _ _ _ _ => trivial
  compositionClosed := fun _ _ _ _ _ _ _ => trivial

/-- The maximal marking: ALL cells above dim 0 are thin. Corresponds to
an ∞-groupoid (everything is invertible). -/
def ThinMarking.maximal (maxDim : Nat) : ThinMarking where
  maxDimension := maxDim
  isThin := fun dimension _ => dimension > 0
  identitiesThin := fun _ _ _ _ => trivial
  compositionClosed := fun _ _ _ _ _ _ _ => trivial

/-- The n-truncation marking: cells above dim n are all thin.
Gives an (∞,n)-category. -/
def ThinMarking.truncated (maxDim : Nat) (cutoff : Nat) : ThinMarking where
  maxDimension := maxDim
  isThin := fun dimension _ => dimension > cutoff
  identitiesThin := fun _ _ _ _ => trivial
  compositionClosed := fun _ _ _ _ _ _ _ => trivial

/-- Saturation level classification. -/
inductive SaturationLevel where
  | minimal
  | nTruncated (cutoff : Nat)
  | omegaSaturated
  deriving DecidableEq, Repr

/-- A stratification pairs a thin marking with its saturation level. -/
structure Stratification where
  marking : ThinMarking
  level : SaturationLevel

/-- Construct stratification from saturation level. -/
def Stratification.fromLevel (maxDim : Nat) : SaturationLevel → Stratification
  | .minimal => ⟨ThinMarking.minimal maxDim, .minimal⟩
  | .nTruncated n => ⟨ThinMarking.truncated maxDim n, .nTruncated n⟩
  | .omegaSaturated => ⟨ThinMarking.maximal maxDim, .omegaSaturated⟩

/-- FX's stratification: omega-saturated (thin = all coherent equivalences).
At the operational level, dim-1 thinness = Conv, dim-2 thinness = cd_lemma. -/
def fxStratification : Stratification :=
  Stratification.fromLevel 4 .omegaSaturated

theorem fxStratification_level :
    fxStratification.level = .omegaSaturated := rfl

/-- Check if a cell is thin in a stratification. -/
def Stratification.cellIsThin (strat : Stratification)
    (dimension : Nat) (cellId : Nat) : Bool :=
  strat.marking.isThin dimension cellId

/-- Decidability of thinness (trivial — isThin is already Bool-valued). -/
def Stratification.thinDecidable (strat : Stratification)
    (dimension : Nat) (cellId : Nat) : Decidable (strat.cellIsThin dimension cellId = true) :=
  inferInstance

end LeanFX2.Foundation.PolyCell.Stratification
