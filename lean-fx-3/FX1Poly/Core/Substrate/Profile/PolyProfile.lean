import FX1Poly.Dimensions.Cohesion.CohesiveFocus
import FX1Poly.ProfileFibration.ProfileMorphism
import FX1Poly.Polygraph.Rewriting.WordSystems.OmegacEAt
import FX1Poly.Axis.Type.Universe.UniverseConfig
import FX1Poly.Axis.Term.SSC.Backbone
import FX1Poly.STC.Modalities
/-!
# PolyProfile — The Axis Ledger Assembling the Live Axes

The central structure of the current PolyCell scaffold: a PolyProfile
bundles the implemented axis outputs and construction ledgers into one
object.  A populated field records data that exists now; a construction
ledger records which stronger categorical packages are still absent.

FX kernel = one specific PolyProfile instance (fxProfile).
Every future feature = a ProfileExtension over fxProfile.

The §3.1-3.6 imported-(∞,ω)-math scaffold axes (shape / polynomial /
stratification / saturation / enrichment / Gray) have been dropped from
the ledger; they are to be redone natively inside the cell-sort axis
directories (Axis/Context|Mode|Term|Type) rather than carried as
standalone scaffold fields.

Reference: polycell.md §4.
Zero external dependencies (all imports are PolyCell-internal).
-/

namespace FX1Poly.Core

open Modal ProfileFibration OmegacE Universe SSC STC

/-- PolyProfile bundles the currently implemented data and honesty ledgers
across the live axes (7-12). -/
structure PolyProfile where
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

/-- The FX kernel profile: the live axes populated with FX-specific choices. -/
def fxProfile : PolyProfile where
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
