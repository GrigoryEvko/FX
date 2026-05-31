/-!
# Stratification — Thin-Marking Scaffold (Axis 3)

This file implements the current finite identifier-level thin-marking
scaffold.  It has Bool-valued thinness predicates, a `ThinMarking` record,
minimal/maximal/truncated examples, and a saturation-level label.

It does not construct Verity/Riehl saturation, does not connect dim-1
thinness to `Conv`, and does not connect dim-2 thinness to certified
confluence fillers.

Reference: Henry-Loubaton arXiv:2301.11424 §2.2, Verity 2008.
Zero external dependencies.
-/

namespace FX1Poly.Stratification

/-- Construction ledger for the current Axis 3 stratification subsystem. -/
inductive StratificationConstructionLevel where
  /-- Positive-dimension and cell-identifier predicates are available. -/
  | cellIdentifierPredicates
  /-- The thin-marking record is available. -/
  | thinMarkingRecord
  /-- Minimal, maximal, and truncated finite scaffold markings exist. -/
  | finiteScaffoldMarkings
  /-- Saturation-level labels and `fromLevel` bookkeeping are available. -/
  | saturationLevelBookkeeping
  /-- Source/target closure laws for thin cells have been supplied. -/
  | boundaryClosureLaws
  /-- FX `Conv` and confluence fillers have been bridged to thinness. -/
  | fxConvConfluenceThinnessBridge
  /-- Verity/Riehl complicial stratification rules have been mechanized. -/
  | verityComplicialStratification
  /-- The canonical saturated marking has been constructed from fillers. -/
  | canonicalSaturatedMarking
  deriving DecidableEq, Repr

/-- Whether the level includes positive-dimension and cell-id predicates. -/
def StratificationConstructionLevel.hasCellIdentifierPredicates :
    StratificationConstructionLevel → Bool
  | .cellIdentifierPredicates => true
  | .thinMarkingRecord => true
  | .finiteScaffoldMarkings => true
  | .saturationLevelBookkeeping => true
  | .boundaryClosureLaws => true
  | .fxConvConfluenceThinnessBridge => true
  | .verityComplicialStratification => true
  | .canonicalSaturatedMarking => true

/-- Whether the level includes the thin-marking record. -/
def StratificationConstructionLevel.hasThinMarkingRecord :
    StratificationConstructionLevel → Bool
  | .cellIdentifierPredicates => false
  | .thinMarkingRecord => true
  | .finiteScaffoldMarkings => true
  | .saturationLevelBookkeeping => true
  | .boundaryClosureLaws => true
  | .fxConvConfluenceThinnessBridge => true
  | .verityComplicialStratification => true
  | .canonicalSaturatedMarking => true

/-- Whether the level includes minimal/maximal/truncated finite markings. -/
def StratificationConstructionLevel.hasFiniteScaffoldMarkings :
    StratificationConstructionLevel → Bool
  | .cellIdentifierPredicates => false
  | .thinMarkingRecord => false
  | .finiteScaffoldMarkings => true
  | .saturationLevelBookkeeping => true
  | .boundaryClosureLaws => true
  | .fxConvConfluenceThinnessBridge => true
  | .verityComplicialStratification => true
  | .canonicalSaturatedMarking => true

/-- Whether the level includes saturation-label bookkeeping. -/
def StratificationConstructionLevel.hasSaturationLevelBookkeeping :
    StratificationConstructionLevel → Bool
  | .cellIdentifierPredicates => false
  | .thinMarkingRecord => false
  | .finiteScaffoldMarkings => false
  | .saturationLevelBookkeeping => true
  | .boundaryClosureLaws => true
  | .fxConvConfluenceThinnessBridge => true
  | .verityComplicialStratification => true
  | .canonicalSaturatedMarking => true

/-- Whether the level includes source/target closure laws for thin cells. -/
def StratificationConstructionLevel.hasBoundaryClosureLaws :
    StratificationConstructionLevel → Bool
  | .cellIdentifierPredicates => false
  | .thinMarkingRecord => false
  | .finiteScaffoldMarkings => false
  | .saturationLevelBookkeeping => false
  | .boundaryClosureLaws => true
  | .fxConvConfluenceThinnessBridge => true
  | .verityComplicialStratification => true
  | .canonicalSaturatedMarking => true

/-- Whether the level bridges FX Conv/confluence fillers to thinness. -/
def StratificationConstructionLevel.hasFXConvConfluenceThinnessBridge :
    StratificationConstructionLevel → Bool
  | .cellIdentifierPredicates => false
  | .thinMarkingRecord => false
  | .finiteScaffoldMarkings => false
  | .saturationLevelBookkeeping => false
  | .boundaryClosureLaws => false
  | .fxConvConfluenceThinnessBridge => true
  | .verityComplicialStratification => true
  | .canonicalSaturatedMarking => true

/-- Whether the level includes Verity/Riehl complicial rules. -/
def StratificationConstructionLevel.hasVerityComplicialStratification :
    StratificationConstructionLevel → Bool
  | .cellIdentifierPredicates => false
  | .thinMarkingRecord => false
  | .finiteScaffoldMarkings => false
  | .saturationLevelBookkeeping => false
  | .boundaryClosureLaws => false
  | .fxConvConfluenceThinnessBridge => false
  | .verityComplicialStratification => true
  | .canonicalSaturatedMarking => true

/-- Whether the canonical saturated marking has been constructed. -/
def StratificationConstructionLevel.hasCanonicalSaturatedMarking :
    StratificationConstructionLevel → Bool
  | .cellIdentifierPredicates => false
  | .thinMarkingRecord => false
  | .finiteScaffoldMarkings => false
  | .saturationLevelBookkeeping => false
  | .boundaryClosureLaws => false
  | .fxConvConfluenceThinnessBridge => false
  | .verityComplicialStratification => false
  | .canonicalSaturatedMarking => true

/-- FX Axis 3 currently reaches saturation-label bookkeeping only. -/
def fxStratificationConstructionLevel : StratificationConstructionLevel :=
  .saturationLevelBookkeeping

theorem fxStratificationConstructionLevel_eq :
    fxStratificationConstructionLevel =
      StratificationConstructionLevel.saturationLevelBookkeeping := rfl

theorem fxStratification_hasCellIdentifierPredicates :
    fxStratificationConstructionLevel.hasCellIdentifierPredicates = true :=
  rfl

theorem fxStratification_hasThinMarkingRecord :
    fxStratificationConstructionLevel.hasThinMarkingRecord = true := rfl

theorem fxStratification_hasFiniteScaffoldMarkings :
    fxStratificationConstructionLevel.hasFiniteScaffoldMarkings = true := rfl

theorem fxStratification_hasSaturationLevelBookkeeping :
    fxStratificationConstructionLevel.hasSaturationLevelBookkeeping = true :=
  rfl

theorem fxStratification_hasNoBoundaryClosureLaws :
    fxStratificationConstructionLevel.hasBoundaryClosureLaws = false := rfl

theorem fxStratification_hasNoFXConvConfluenceThinnessBridge :
    fxStratificationConstructionLevel.hasFXConvConfluenceThinnessBridge =
      false := rfl

theorem fxStratification_hasNoVerityComplicialStratification :
    fxStratificationConstructionLevel.hasVerityComplicialStratification =
      false := rfl

theorem fxStratification_hasNoCanonicalSaturatedMarking :
    fxStratificationConstructionLevel.hasCanonicalSaturatedMarking =
      false := rfl

/-- Positive dimensions are the dimensions where thinness is meaningful. -/
def isPositiveDimension (dimension : Nat) : Bool :=
  decide (dimension > 0)

/-- Dimension zero is not a positive-dimensional thinness stratum. -/
theorem isPositiveDimension_zero :
    isPositiveDimension 0 = false := rfl

/-- Every successor dimension is positive for the finite scaffold predicates. -/
theorem isPositiveDimension_succ (dimension : Nat) :
    isPositiveDimension (dimension + 1) = true := by
  dsimp only [isPositiveDimension]
  exact decide_eq_true (Nat.succ_pos dimension)

/-- Current finite-cell scaffold convention: cell id `0` is the degenerate
identity cell at every positive dimension. -/
def isIdentityCellId (cellId : Nat) : Bool :=
  cellId == 0

/-- Cell id zero is the scaffold identity identifier. -/
theorem isIdentityCellId_zero :
    isIdentityCellId 0 = true := rfl

/-- No successor cell id is the scaffold identity identifier. -/
theorem isIdentityCellId_succ (cellId : Nat) :
    isIdentityCellId (cellId + 1) = false := rfl

/-- Minimal thinness: exactly the scaffold identity cells in positive
dimensions. -/
def minimalThinBool (dimension : Nat) (cellId : Nat) : Bool :=
  isPositiveDimension dimension && isIdentityCellId cellId

/-- Minimal scaffold thinness marks no dimension-zero cell. -/
theorem minimalThinBool_zero (cellId : Nat) :
    minimalThinBool 0 cellId = false := rfl

/-- Minimal scaffold thinness marks the identity cell at positive dimensions. -/
theorem minimalThinBool_identity {dimension : Nat}
    (dimensionPositive : dimension > 0) :
    minimalThinBool dimension 0 = true := by
  dsimp only [minimalThinBool, isPositiveDimension, isIdentityCellId]
  rw [decide_eq_true dimensionPositive]
  rfl

/-- Maximal thinness: every positive-dimensional cell is thin. -/
def maximalThinBool (dimension : Nat) (_cellId : Nat) : Bool :=
  isPositiveDimension dimension

/-- Maximal scaffold thinness still marks no dimension-zero cell. -/
theorem maximalThinBool_zero (cellId : Nat) :
    maximalThinBool 0 cellId = false := rfl

/-- Maximal scaffold thinness marks every positive-dimensional cell. -/
theorem maximalThinBool_positive {dimension cellId : Nat}
    (dimensionPositive : dimension > 0) :
    maximalThinBool dimension cellId = true := by
  dsimp only [maximalThinBool, isPositiveDimension]
  exact decide_eq_true dimensionPositive

/-- Truncated thinness: identity cells plus all cells above the cutoff. -/
def truncatedThinBool (cutoff dimension cellId : Nat) : Bool :=
  isPositiveDimension dimension &&
    (isIdentityCellId cellId || decide (dimension > cutoff))

/-- Truncated scaffold thinness marks identity cells at positive dimensions. -/
theorem truncatedThinBool_identity (cutoff : Nat) {dimension : Nat}
    (dimensionPositive : dimension > 0) :
    truncatedThinBool cutoff dimension 0 = true := by
  dsimp only [truncatedThinBool, isPositiveDimension, isIdentityCellId]
  rw [decide_eq_true dimensionPositive]
  rfl

/-- Truncated scaffold thinness marks every cell above the cutoff. -/
theorem truncatedThinBool_aboveCutoff (cutoff dimension cellId : Nat)
    (dimensionAboveCutoff : dimension > cutoff) :
    truncatedThinBool cutoff dimension cellId = true := by
  have dimensionPositive : dimension > 0 :=
    Nat.lt_of_le_of_lt (Nat.zero_le cutoff) dimensionAboveCutoff
  dsimp only [truncatedThinBool, isPositiveDimension]
  rw [decide_eq_true dimensionPositive]
  rw [decide_eq_true dimensionAboveCutoff]
  cases isIdentityCellId cellId <;> rfl

/-- Current scaffold composition on cell identifiers.

This is not the final categorical composition law. It is the explicit
placeholder operation the thinness ledger closes over, so the ledger no
longer accepts empty `True` proofs. -/
def firstProjectionComposeCellId
    (_dimension cellIdA _cellIdB : Nat) : Nat :=
  cellIdA

/-- The current scaffold composition projects the left cell identifier. -/
theorem firstProjectionComposeCellId_eq_left
    (dimension cellIdA cellIdB : Nat) :
    firstProjectionComposeCellId dimension cellIdA cellIdB = cellIdA := rfl

/-- A thin marking on a graded structure: a decidable predicate on cells
at each positive dimension, with closure under identity and composition. -/
structure ThinMarking where
  /-- Maximum dimension of cells this marking covers. -/
  maxDimension : Nat

  /-- The thinness predicate: for dim d > 0 and cell identifier, is it thin? -/
  isThin : (dimension : Nat) → (cellId : Nat) → Bool

  /-- The distinguished scaffold identity cell id for a dimension. -/
  identityCellId : (dimension : Nat) → Nat

  /-- Identifier-level composition operation used by the current scaffold. -/
  composeCellId : (dimension : Nat) → (cellIdA cellIdB : Nat) → Nat

  /-- Identity cells are always thin (degenerate = invertible). -/
  identitiesThin :
    ∀ (dimension : Nat),
    dimension > 0 → isThin dimension (identityCellId dimension) = true

  /-- Composition of thin cells is thin. -/
  compositionClosed :
    ∀ (dimension : Nat) (cellIdA cellIdB : Nat),
    isThin dimension cellIdA = true →
    isThin dimension cellIdB = true →
    isThin dimension (composeCellId dimension cellIdA cellIdB) = true

/-- The minimal marking: only identity cells are thin. Corresponds to
a directed n-category (no invertibility beyond degeneracies). -/
def ThinMarking.minimal (maxDim : Nat) : ThinMarking where
  maxDimension := maxDim
  isThin := minimalThinBool
  identityCellId := fun _ => 0
  composeCellId := firstProjectionComposeCellId
  identitiesThin := by
    intro dimension dimensionPositive
    dsimp only [minimalThinBool, isPositiveDimension, isIdentityCellId]
    rw [decide_eq_true dimensionPositive]
    rfl
  compositionClosed := by
    intro dimension cellIdA _cellIdB cellIdAThin _cellIdBThin
    dsimp only [firstProjectionComposeCellId]
    exact cellIdAThin

/-- The maximal marking: every cell above dim 0 is thin. Corresponds to
an ∞-groupoid (everything is invertible). -/
def ThinMarking.maximal (maxDim : Nat) : ThinMarking where
  maxDimension := maxDim
  isThin := maximalThinBool
  identityCellId := fun _ => 0
  composeCellId := firstProjectionComposeCellId
  identitiesThin := by
    intro dimension dimensionPositive
    dsimp only [maximalThinBool, isPositiveDimension]
    exact decide_eq_true dimensionPositive
  compositionClosed := by
    intro dimension cellIdA _cellIdB cellIdAThin _cellIdBThin
    dsimp only [firstProjectionComposeCellId]
    exact cellIdAThin

/-- The n-truncation marking: cells above dim n are all thin.
Gives an (∞,n)-category. -/
def ThinMarking.truncated (maxDim : Nat) (cutoff : Nat) : ThinMarking where
  maxDimension := maxDim
  isThin := truncatedThinBool cutoff
  identityCellId := fun _ => 0
  composeCellId := firstProjectionComposeCellId
  identitiesThin := by
    intro dimension dimensionPositive
    dsimp only [truncatedThinBool, isPositiveDimension, isIdentityCellId]
    rw [decide_eq_true dimensionPositive]
    rfl
  compositionClosed := by
    intro dimension cellIdA _cellIdB cellIdAThin _cellIdBThin
    dsimp only [firstProjectionComposeCellId]
    exact cellIdAThin

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

/-- FX's current stratification scaffold uses the omega-saturated label with
the maximal finite identifier marking.  This is not yet the operational
Conv/cd-lemma thinness bridge. -/
def fxStratification : Stratification :=
  Stratification.fromLevel 4 .omegaSaturated

theorem fxStratification_level :
    fxStratification.level = .omegaSaturated := rfl

/-- Check if a cell is thin in a stratification. -/
def Stratification.cellIsThin (strat : Stratification)
    (dimension : Nat) (cellId : Nat) : Bool :=
  strat.marking.isThin dimension cellId

/-- Current FX scaffold thinness is the maximal finite identifier marking:
every positive-dimensional identifier is thin.  This is not an operational
`Conv` bridge. -/
theorem fxStratification_cellIsThin_positive {dimension cellId : Nat}
    (dimensionPositive : dimension > 0) :
    fxStratification.cellIsThin dimension cellId = true := by
  dsimp only [fxStratification, Stratification.fromLevel,
    Stratification.cellIsThin, ThinMarking.maximal, maximalThinBool,
    isPositiveDimension]
  exact decide_eq_true dimensionPositive

/-- Current FX scaffold thinness marks no dimension-zero identifier. -/
theorem fxStratification_cellIsThin_zero (cellId : Nat) :
    fxStratification.cellIsThin 0 cellId = false := rfl

/-- Decidability of thinness (trivial — isThin is already Bool-valued). -/
def Stratification.thinDecidable (strat : Stratification)
    (dimension : Nat) (cellId : Nat) : Decidable (strat.cellIsThin dimension cellId = true) :=
  inferInstance

end FX1Poly.Stratification
