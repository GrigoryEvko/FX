import FX1Poly.Shape.RegularDirectedComplex
import FX1Poly.Algebra.IsUnivalent
import FX1Poly.Stratification.Thin
import FX1Poly.Saturation.CubicalCategory
import FX1Poly.Enrichment.Rung
import FX1Poly.Gray.GrayTensor
import FX1Poly.Modal.CohesiveFocus
import FX1Poly.ProfileFibration.ProfileMorphism
import FX1Poly.OmegacE.OmegacEAt
import FX1Poly.Tier0.Type.Universe.UniverseConfig
import FX1Poly.SSC.Backbone
import FX1Poly.STC.Modalities
/-!
# PolyProfile — The 13-Field Ledger Assembling All Axes

The central structure of the current PolyCell scaffold: a PolyProfile
bundles the implemented axis outputs and construction ledgers into one
object.  A populated field records data that exists now; a construction
ledger records which stronger categorical packages are still absent.

FX kernel = one specific PolyProfile instance (fxProfile).
Every future feature = a ProfileExtension over fxProfile.

Reference: polycell.md §4.
Zero external dependencies (all imports are PolyCell-internal).
-/

namespace FX1Poly.Core

open Shape Algebra Stratification Saturation Enrichment Gray
     Modal ProfileFibration OmegacE Universe SSC STC

/-- PolyProfile bundles the currently implemented data and honesty ledgers
across all 13 axes. -/
structure PolyProfile where
  /-- AXIS 1: Per-dimension cell shape family. -/
  shapeMaxDim : Nat

  /-- AXIS 1 construction ledger.  `shapeMaxDim` is only a finite dimension
  budget; this records which shape objects have actually been built. -/
  shapeConstructionLevel : ShapeConstructionLevel

  /-- AXIS 2: Algebraic structure (polynomial universe). -/
  algebraUniverse : PolynomialUniverse

  /-- AXIS 3: Thin-marking stratification. -/
  stratification : Stratification.Stratification

  /-- AXIS 3 construction ledger. -/
  stratificationConstructionLevel : StratificationConstructionLevel

  /-- AXIS 4: Cubical category structure for saturation. -/
  saturationCells : CubicalCells

  /-- AXIS 4 construction ledger.  This records how much saturation
  machinery has actually been constructed for the profile. -/
  saturationConstructionLevel : SaturationConstructionLevel

  /-- AXIS 5: Per-dimension enrichment level. -/
  enrichment : Enrichment.Enrichment

  /-- AXIS 5 construction ledger. -/
  enrichmentConstructionLevel : EnrichmentConstructionLevel

  /-- AXIS 6: Gray module (tensor product structure). -/
  grayModule : GrayModule

  /-- AXIS 7: finite cohesive-focus count. -/
  cohesiveFocusCount : Nat

  /-- AXIS 7 construction ledger. -/
  modalConstructionLevel : ModalConstructionLevel

  /-- AXIS 8: Profile fibration depth. -/
  fibrationTower : ProfileTower

  /-- AXIS 8 construction ledger. -/
  fibrationConstructionLevel : ProfileFibrationConstructionLevel

  /-- AXIS 9: ωcE cell dimension bound. -/
  omegacEDimBound : Nat

  /-- AXIS 9 construction ledger. -/
  omegacEConstructionLevel : OmegacEConstructionLevel

  /-- AXIS 10: Universe configuration. -/
  universeConfig : UniverseConfig

  /-- AXIS 11: Single-substitution calculus backbone. -/
  sscBackbone : SingleSubstitutionBackbone

  /-- AXIS 12: STC model record. -/
  stcModel : STCModel

  /-- AXIS 12 construction ledger. -/
  stcConstructionLevel : STCConstructionLevel

/-- The FX kernel profile: all 13 axes populated with FX-specific choices. -/
def fxProfile : PolyProfile where
  shapeMaxDim := 4
  shapeConstructionLevel := Shape.fxShapeConstructionLevel
  algebraUniverse := Algebra.fxAlgebraUniverse
  stratification := Stratification.fxStratification
  stratificationConstructionLevel :=
    Stratification.fxStratificationConstructionLevel
  saturationCells := Saturation.finiteIdentifierCubicalCells
  saturationConstructionLevel := .finiteIdentifierCells
  enrichment := Enrichment.fxEnrichment
  enrichmentConstructionLevel := Enrichment.fxEnrichmentConstructionLevel
  grayModule := Gray.fxGrayModule
  cohesiveFocusCount := Modal.fxCohesiveFocusCount
  modalConstructionLevel := Modal.fxModalConstructionLevel
  fibrationTower := .base
  fibrationConstructionLevel :=
    ProfileFibration.fxProfileFibrationConstructionLevel
  omegacEDimBound := 3
  omegacEConstructionLevel := OmegacE.fxOmegacEConstructionLevel
  universeConfig := Universe.fxUniverseConfig
  sscBackbone := SSC.fxSSCBackbone
  stcModel := STC.canonicalSTCModel
  stcConstructionLevel := STC.fxSTCConstructionLevel

/-- FX profile HAS the Axis 12 bool canonicity theorem
(`canonicityViaSTC`, BRIDGED to the kernel's syntactic canonicity
witness). -/
theorem fxProfile_stcHasCanonicityTheorem :
    fxProfile.stcConstructionLevel.hasCanonicityTheorem = true := rfl

/-- FX profile HAS the Axis 12 normalization theorem
(`normalizationViaSTC`, BRIDGED to the kernel's computed
normalizer). -/
theorem fxProfile_stcHasNormalizationTheorem :
    fxProfile.stcConstructionLevel.hasNormalizationTheorem = true := rfl

end FX1Poly.Core
