/-!
# Gray Tensor Product (Axis 6 — Al-Agl-Brown-Steiner + Loubaton)

The asymmetric monoidal product on strict ω-categories.  This file
records only the Axis 6 construction ledger and the FX
active-dimension count; it does not construct the tensor itself
(vertical/horizontal composition + interchange).

Reference: ABGMMM book §17, Loubaton arXiv:2207.08504 §2.3.
-/

namespace FX1Poly.Gray

/-- How much of Axis 6 has actually been constructed.

This ledger separates a computable Gray-module record from the real
complicial acyclicity and saturation-compatibility theorems. -/
inductive GrayConstructionLevel where
  /-- Only active dimensions are recorded; no Gray tensor laws are claimed. -/
  | dimensionLedgerOnly
  /-- Strict omega-category Gray tensor laws have been supplied. -/
  | strictOmegaTensor
  /-- Complicial acyclicity conditions have been supplied. -/
  | complicialAcyclicity
  /-- Complicial data has been linked to the saturation axis. -/
  | saturationCompatibleComplicial
  deriving DecidableEq, Repr

/-- Whether this Axis 6 level includes strict Gray tensor laws. -/
def GrayConstructionLevel.hasStrictOmegaTensor : GrayConstructionLevel → Bool
  | .dimensionLedgerOnly => false
  | .strictOmegaTensor => true
  | .complicialAcyclicity => true
  | .saturationCompatibleComplicial => true

/-- Whether this Axis 6 level includes complicial acyclicity. -/
def GrayConstructionLevel.hasComplicialAcyclicity : GrayConstructionLevel → Bool
  | .dimensionLedgerOnly => false
  | .strictOmegaTensor => false
  | .complicialAcyclicity => true
  | .saturationCompatibleComplicial => true

/-- Whether this Axis 6 level is linked to the saturation axis. -/
def GrayConstructionLevel.hasSaturationCompatibility : GrayConstructionLevel → Bool
  | .dimensionLedgerOnly => false
  | .strictOmegaTensor => false
  | .complicialAcyclicity => false
  | .saturationCompatibleComplicial => true

/-- A Gray module: the minimal structure needed for the complicial
Gray tensor product.  A full version is a truncation-compatible tensor;
this structure records only the truncation level and the construction
ledger. -/
structure GrayModule where
  /-- Truncation level (how many dimensions are "active"). -/
  activeDimensions : Nat
  /-- Axis 6 construction ledger. -/
  constructionLevel : GrayConstructionLevel

/-- The FX Gray module currently records only its 4 active operational
dimensions.  It does not claim strict Gray tensor laws or complicial
acyclicity yet. -/
def fxGrayModule : GrayModule where
  activeDimensions := 4
  constructionLevel := .dimensionLedgerOnly

/-- FX Gray currently has only the dimension ledger. -/
theorem fxGrayModule_constructionLevel :
    fxGrayModule.constructionLevel =
      GrayConstructionLevel.dimensionLedgerOnly := rfl

/-- FX Gray currently has no constructed strict tensor law package. -/
theorem fxGrayModule_hasNoStrictOmegaTensor :
    fxGrayModule.constructionLevel.hasStrictOmegaTensor = false := rfl

/-- FX Gray currently has no constructed complicial acyclicity witness. -/
theorem fxGrayModule_hasNoComplicialAcyclicity :
    fxGrayModule.constructionLevel.hasComplicialAcyclicity = false := rfl

/-- FX Gray currently has no link theorem from Axis 4 saturation to Axis 6
complicial data. -/
theorem fxGrayModule_hasNoSaturationCompatibility :
    fxGrayModule.constructionLevel.hasSaturationCompatibility = false := rfl

end FX1Poly.Gray
