import FX1Poly.Tier0.ModeOmega.ModeTheory

/-!
# Mode Theory — MTT-normalization view (re-export over Tier0/ModeOmega)

The mode 2-category substrate (objects=modes, 1-cells=modalities, 2-cells=coherences; Gratzer
arXiv:2301.11842 §2) is now native to `Tier0/ModeOmega/ModeTheory.lean`, so the sealed mode ω-category
no longer imports this higher MTTNorm layer.  This module re-exports that substrate under the historical
`FX1Poly.MTTNorm` namespace and adds the MTT-normalization Axis-13 readiness ledger (which records how far
the Gratzer-normalization route has been mechanized — interface only, no FX conversion decision yet).

Reference: arXiv:2301.11842 §2.  Zero external dependencies beyond `Tier0/ModeOmega/ModeTheory`.
-/

namespace FX1Poly.MTTNorm

-- The mode-theory substrate is defined natively in `Tier0/ModeOmega/ModeTheory.lean`; re-export it under
-- the `FX1Poly.MTTNorm` namespace so the historical consumers (Core.PolyProfile, the MTT machinery) keep
-- resolving `MTTNorm.fxModeTheory`, `MTTNorm.ModeTheory`, etc. — the dependency arrow now points
-- MTTNorm → Tier0, not the reverse.
export FX1Poly.Tier0.ModeOmega
  (ModeTheory ModeTheoryRigid GratzerReady
   TrivialMode TrivialModality trivialModeTheory trivialGratzerReady
   FXModeAtom FXModeShift FXModePath
   fxModeTheory fxModeTheoryRigid fxGratzerReady)

/-- Honesty ledger for Axis 13.  Each level records a strictly stronger
mechanized package than the previous one. -/
inductive MTTNormConstructionLevel where
  /-- Mode-theory category interface only. -/
  | modeCategoryInterface : MTTNormConstructionLevel
  /-- Trivial one-object mode theory is constructed. -/
  | trivialModeTheory : MTTNormConstructionLevel
  /-- Finite FX mode paths and category laws are constructed. -/
  | finiteFXModePathCategory : MTTNormConstructionLevel
  /-- `GratzerReady` record is populated for the finite FX mode category. -/
  | gratzerReadinessRecord : MTTNormConstructionLevel
  /-- MTT syntax has been translated over the mode theory. -/
  | mttSyntaxTranslation : MTTNormConstructionLevel
  /-- Gratzer normalization theorem is mechanized. -/
  | gratzerNormalizationTheorem : MTTNormConstructionLevel
  /-- FX conversion decidability theorem is derived. -/
  | fxConversionDecidableTheorem : MTTNormConstructionLevel
  deriving DecidableEq, Repr

/-- Axis 13 has the mode-category interface at every ledger level. -/
def MTTNormConstructionLevel.hasModeCategoryInterface :
    MTTNormConstructionLevel → Bool
  | .modeCategoryInterface => true
  | .trivialModeTheory => true
  | .finiteFXModePathCategory => true
  | .gratzerReadinessRecord => true
  | .mttSyntaxTranslation => true
  | .gratzerNormalizationTheorem => true
  | .fxConversionDecidableTheorem => true

/-- Axis 13 has the trivial mode theory from this level onward. -/
def MTTNormConstructionLevel.hasTrivialModeTheory :
    MTTNormConstructionLevel → Bool
  | .modeCategoryInterface => false
  | .trivialModeTheory => true
  | .finiteFXModePathCategory => true
  | .gratzerReadinessRecord => true
  | .mttSyntaxTranslation => true
  | .gratzerNormalizationTheorem => true
  | .fxConversionDecidableTheorem => true

/-- Axis 13 has finite FX mode paths and laws from this level onward. -/
def MTTNormConstructionLevel.hasFiniteFXModePathCategory :
    MTTNormConstructionLevel → Bool
  | .modeCategoryInterface => false
  | .trivialModeTheory => false
  | .finiteFXModePathCategory => true
  | .gratzerReadinessRecord => true
  | .mttSyntaxTranslation => true
  | .gratzerNormalizationTheorem => true
  | .fxConversionDecidableTheorem => true

/-- Axis 13 has a populated `GratzerReady` input record from this level onward. -/
def MTTNormConstructionLevel.hasGratzerReadinessRecord :
    MTTNormConstructionLevel → Bool
  | .modeCategoryInterface => false
  | .trivialModeTheory => false
  | .finiteFXModePathCategory => false
  | .gratzerReadinessRecord => true
  | .mttSyntaxTranslation => true
  | .gratzerNormalizationTheorem => true
  | .fxConversionDecidableTheorem => true

/-- Axis 13 has an MTT syntax translation from this level onward. -/
def MTTNormConstructionLevel.hasMTTSyntaxTranslation :
    MTTNormConstructionLevel → Bool
  | .modeCategoryInterface => false
  | .trivialModeTheory => false
  | .finiteFXModePathCategory => false
  | .gratzerReadinessRecord => false
  | .mttSyntaxTranslation => true
  | .gratzerNormalizationTheorem => true
  | .fxConversionDecidableTheorem => true

/-- Axis 13 has the Gratzer normalization theorem from this level onward. -/
def MTTNormConstructionLevel.hasGratzerNormalizationTheorem :
    MTTNormConstructionLevel → Bool
  | .modeCategoryInterface => false
  | .trivialModeTheory => false
  | .finiteFXModePathCategory => false
  | .gratzerReadinessRecord => false
  | .mttSyntaxTranslation => false
  | .gratzerNormalizationTheorem => true
  | .fxConversionDecidableTheorem => true

/-- Axis 13 has the FX conversion-decidability theorem only at the final level. -/
def MTTNormConstructionLevel.hasFXConversionDecidableTheorem :
    MTTNormConstructionLevel → Bool
  | .modeCategoryInterface => false
  | .trivialModeTheory => false
  | .finiteFXModePathCategory => false
  | .gratzerReadinessRecord => false
  | .mttSyntaxTranslation => false
  | .gratzerNormalizationTheorem => false
  | .fxConversionDecidableTheorem => true

/-- Current Axis 13 status: the finite FX mode theory has the input record
needed by the future Gratzer formalization, but no MTT syntax or conversion
theorem is present. -/
def fxMTTNormConstructionLevel : MTTNormConstructionLevel :=
  .gratzerReadinessRecord

theorem fxMTTNormConstructionLevel_eq :
    fxMTTNormConstructionLevel =
      MTTNormConstructionLevel.gratzerReadinessRecord := rfl

theorem fxMTTNorm_hasModeCategoryInterface :
    fxMTTNormConstructionLevel.hasModeCategoryInterface = true := rfl

theorem fxMTTNorm_hasTrivialModeTheory :
    fxMTTNormConstructionLevel.hasTrivialModeTheory = true := rfl

theorem fxMTTNorm_hasFiniteFXModePathCategory :
    fxMTTNormConstructionLevel.hasFiniteFXModePathCategory = true := rfl

theorem fxMTTNorm_hasGratzerReadinessRecord :
    fxMTTNormConstructionLevel.hasGratzerReadinessRecord = true := rfl

/-- Current Axis 13 has no MTT syntax translation. -/
theorem fxMTTNorm_hasNoMTTSyntaxTranslation :
    fxMTTNormConstructionLevel.hasMTTSyntaxTranslation = false := rfl

/-- Current Axis 13 has no mechanized Gratzer normalization theorem. -/
theorem fxMTTNorm_hasNoGratzerNormalizationTheorem :
    fxMTTNormConstructionLevel.hasGratzerNormalizationTheorem = false := rfl

/-- Current Axis 13 has no FX conversion-decidability theorem. -/
theorem fxMTTNorm_hasNoFXConversionDecidableTheorem :
    fxMTTNormConstructionLevel.hasFXConversionDecidableTheorem = false := rfl

end FX1Poly.MTTNorm
