import LeanFX2.Foundation.PolyCell.Core.Check
/-!
# CertifiedViews — FX Names for Certified PolyCells

This file gives the FX profile honest view names over the certified cell
layer.  These are not raw subtype wrappers: every inhabitant carries an actual
`PolyCell` witness.  Thin views are structural only: identities and vertical
composites of thin cells.  Full conversion/reduction/coherence views remain
absent until their operational predicates are certified.
-/

namespace LeanFX2.Foundation.PolyCell.FXProfile

open Core

/-- A certified FX-profile cell with fixed sort, dimension, and scope. -/
structure CertifiedFXCell
    (cellSort : CellSort) (cellDimension : CellDim) (scope : Nat) where
  /-- Raw erasure of the certified cell. -/
  rawCell : PolyTerm fxProfile cellDimension
  /-- Boundary index carried by the certified cell. -/
  cellBoundary : CellBoundary fxProfile cellSort cellDimension scope
  /-- Certified witness over the raw erasure. -/
  certifiedCell :
    PolyCell fxProfile cellSort cellDimension scope cellBoundary rawCell

namespace CertifiedFXCell

/-- Build a certified FX view from a raw-indexed certified package. -/
def ofCertifiedRawCell {cellDimension scope : Nat}
    {rawCell : PolyTerm fxProfile cellDimension}
    (certifiedRawCell : Check.CertifiedRawCell fxProfile scope rawCell) :
    CertifiedFXCell certifiedRawCell.cellSort cellDimension scope where
  rawCell := rawCell
  cellBoundary := certifiedRawCell.cellBoundary
  certifiedCell := certifiedRawCell.certifiedCell

/-- Forget a certified FX view to its raw cell. -/
def toRaw {cellSort : CellSort} {cellDimension scope : Nat}
    (cell : CertifiedFXCell cellSort cellDimension scope) :
    PolyTerm fxProfile cellDimension :=
  cell.rawCell

/-- Project the certified witness carried by a certified FX view. -/
def toCertifiedCell {cellSort : CellSort} {cellDimension scope : Nat}
    (cell : CertifiedFXCell cellSort cellDimension scope) :
    PolyCell fxProfile cellSort cellDimension scope
      cell.cellBoundary cell.rawCell :=
  cell.certifiedCell

/-- Source endpoint of a certified positive-dimensional FX cell. -/
def sourceRaw {cellSort : CellSort} {cellDimension scope : Nat}
    (cell : CertifiedFXCell cellSort (cellDimension + 1) scope) :
    PolyTerm fxProfile cellDimension :=
  cell.cellBoundary.1

/-- Target endpoint of a certified positive-dimensional FX cell. -/
def targetRaw {cellSort : CellSort} {cellDimension scope : Nat}
    (cell : CertifiedFXCell cellSort (cellDimension + 1) scope) :
    PolyTerm fxProfile cellDimension :=
  cell.cellBoundary.2

end CertifiedFXCell

/-- A certified positive-dimensional FX cell with certified thinness evidence. -/
structure CertifiedFXThinCell
    (cellSort : CellSort) (cellDimension : CellDim) (scope : Nat) where
  /-- Underlying certified positive-dimensional cell. -/
  certifiedFXCell : CertifiedFXCell cellSort (cellDimension + 1) scope
  /-- Certified structural thinness evidence for the underlying cell. -/
  thinEvidence : PolyCell.ThinCell certifiedFXCell.certifiedCell

namespace CertifiedFXThinCell

/-- Forget thinness and keep the underlying certified FX cell. -/
def toCertifiedFXCell {cellSort : CellSort} {cellDimension scope : Nat}
    (cell : CertifiedFXThinCell cellSort cellDimension scope) :
    CertifiedFXCell cellSort (cellDimension + 1) scope :=
  cell.certifiedFXCell

/-- Raw erasure of a certified thin FX cell. -/
def toRaw {cellSort : CellSort} {cellDimension scope : Nat}
    (cell : CertifiedFXThinCell cellSort cellDimension scope) :
    PolyTerm fxProfile (cellDimension + 1) :=
  cell.certifiedFXCell.toRaw

/-- Source endpoint of a certified thin FX cell. -/
def sourceRaw {cellSort : CellSort} {cellDimension scope : Nat}
    (cell : CertifiedFXThinCell cellSort cellDimension scope) :
    PolyTerm fxProfile cellDimension :=
  cell.certifiedFXCell.sourceRaw

/-- Target endpoint of a certified thin FX cell. -/
def targetRaw {cellSort : CellSort} {cellDimension scope : Nat}
    (cell : CertifiedFXThinCell cellSort cellDimension scope) :
    PolyTerm fxProfile cellDimension :=
  cell.certifiedFXCell.targetRaw

end CertifiedFXThinCell

/-- Certified FX context cell at dimension 0. -/
abbrev CertifiedFXContext (scope : Nat) := CertifiedFXCell .context 0 scope

/-- Certified FX type cell at dimension 0. -/
abbrev CertifiedFXType (scope : Nat) := CertifiedFXCell .type 0 scope

/-- Certified FX term cell at dimension 0. -/
abbrev CertifiedFXTerm (scope : Nat) := CertifiedFXCell .term 0 scope

/-- Certified FX mode cell at dimension 0. -/
abbrev CertifiedFXMode (scope : Nat) := CertifiedFXCell .mode 0 scope

/-- Certified structural term cell at dimension 1.

This is not yet the final `FXStep` view: operational reduction semantics and
thinness/conversion classification remain separate later layers. -/
abbrev CertifiedFXDimOneTermCell (scope : Nat) :=
  CertifiedFXCell .term 1 scope

/-- Certified structural type cell at dimension 1. -/
abbrev CertifiedFXDimOneTypeCell (scope : Nat) :=
  CertifiedFXCell .type 1 scope

/-- Certified structural context cell at dimension 1. -/
abbrev CertifiedFXDimOneContextCell (scope : Nat) :=
  CertifiedFXCell .context 1 scope

/-- Certified structural mode cell at dimension 1. -/
abbrev CertifiedFXDimOneModeCell (scope : Nat) :=
  CertifiedFXCell .mode 1 scope

/-- Certified structural term cell at dimension 2. -/
abbrev CertifiedFXDimTwoTermCell (scope : Nat) :=
  CertifiedFXCell .term 2 scope

/-- Certified thin term cell at dimension 1.

This is a structural thin cell, not yet the final legacy `Conv` bridge. -/
abbrev CertifiedFXTermThinCell (scope : Nat) :=
  CertifiedFXThinCell .term 0 scope

/-- Seed certified term view from the current dim-0 ingress subset. -/
def certifiedSeedTerm :
    CertifiedFXTerm NegativeProbes.defaultInferScope :=
  CertifiedFXCell.ofCertifiedRawCell
    (Check.certifiedSeedTermPackage (profile := fxProfile))

/-- Seed certified type view from the current dim-0 ingress subset. -/
def certifiedSeedType :
    CertifiedFXType NegativeProbes.defaultInferScope :=
  CertifiedFXCell.ofCertifiedRawCell
    (Check.certifiedSeedTypePackage (profile := fxProfile))

/-- Seed certified context view from the current dim-0 ingress subset. -/
def certifiedSeedContext :
    CertifiedFXContext NegativeProbes.defaultInferScope :=
  CertifiedFXCell.ofCertifiedRawCell
    (Check.certifiedSeedContextPackage (profile := fxProfile))

/-- Seed certified mode view from the current dim-0 ingress subset. -/
def certifiedSeedMode :
    CertifiedFXMode NegativeProbes.defaultInferScope :=
  CertifiedFXCell.ofCertifiedRawCell
    (Check.certifiedSeedModePackage (profile := fxProfile))

/-- Certified term view for the first finite application payload. -/
def certifiedApplicationVarZeroVarOne :
    CertifiedFXTerm NegativeProbes.defaultInferScope :=
  CertifiedFXCell.ofCertifiedRawCell
    (Check.certifiedApplicationVarZeroVarOnePackage (profile := fxProfile)
      (Check.certifiedApplicationVarZeroVarOneChildren (profile := fxProfile)
        (scope := NegativeProbes.defaultInferScope)
        (Nat.zero_lt_succ 3)
        (Nat.succ_lt_succ (Nat.zero_lt_succ 2))))

/-- Certified structural dim-1 term-cell view for the first term-step fixture. -/
def certifiedSeedTermStep :
    CertifiedFXDimOneTermCell NegativeProbes.defaultInferScope :=
  CertifiedFXCell.ofCertifiedRawCell
    (Check.certifiedSeedTermStepPackage (profile := fxProfile))

/-- Certified identity over the seed term fixture. -/
def certifiedSeedTermIdentity :
    CertifiedFXDimOneTermCell NegativeProbes.defaultInferScope :=
  CertifiedFXCell.ofCertifiedRawCell
    (Check.certifiedSeedTermIdentityPackage (profile := fxProfile))

/-- Certified identity over the seed type fixture. -/
def certifiedSeedTypeIdentity :
    CertifiedFXDimOneTypeCell NegativeProbes.defaultInferScope :=
  CertifiedFXCell.ofCertifiedRawCell
    (Check.certifiedSeedTypeIdentityPackage (profile := fxProfile))

/-- Certified identity over the seed context fixture. -/
def certifiedSeedContextIdentity :
    CertifiedFXDimOneContextCell NegativeProbes.defaultInferScope :=
  CertifiedFXCell.ofCertifiedRawCell
    (Check.certifiedSeedContextIdentityPackage (profile := fxProfile))

/-- Certified identity over the seed mode fixture. -/
def certifiedSeedModeIdentity :
    CertifiedFXDimOneModeCell NegativeProbes.defaultInferScope :=
  CertifiedFXCell.ofCertifiedRawCell
    (Check.certifiedSeedModeIdentityPackage (profile := fxProfile))

/-- Certified identity over the seed dim-1 term-step fixture. -/
def certifiedSeedTermStepIdentity :
    CertifiedFXDimTwoTermCell NegativeProbes.defaultInferScope :=
  CertifiedFXCell.ofCertifiedRawCell
    (Check.certifiedSeedTermStepIdentityPackage (profile := fxProfile))

/-- Certified vertical composite of the seed term identity with itself. -/
def certifiedSeedTermIdentityTwice :
    CertifiedFXDimOneTermCell NegativeProbes.defaultInferScope :=
  CertifiedFXCell.ofCertifiedRawCell
    (Check.certifiedSeedTermIdentityTwicePackage (profile := fxProfile))

/-- Certified thinness view for the seed term identity. -/
def certifiedSeedTermIdentityThin :
    CertifiedFXTermThinCell NegativeProbes.defaultInferScope where
  certifiedFXCell := certifiedSeedTermIdentity
  thinEvidence :=
    PolyCell.identityThinCell
      (Check.certifiedSeedTermPackage (profile := fxProfile)).certifiedCell

/-- Certified thinness view for the seed type identity. -/
def certifiedSeedTypeIdentityThin :
    CertifiedFXThinCell .type 0 NegativeProbes.defaultInferScope where
  certifiedFXCell := certifiedSeedTypeIdentity
  thinEvidence :=
    PolyCell.identityThinCell
      (Check.certifiedSeedTypePackage (profile := fxProfile)).certifiedCell

/-- Certified thinness view for the seed context identity. -/
def certifiedSeedContextIdentityThin :
    CertifiedFXThinCell .context 0 NegativeProbes.defaultInferScope where
  certifiedFXCell := certifiedSeedContextIdentity
  thinEvidence :=
    PolyCell.identityThinCell
      (Check.certifiedSeedContextPackage (profile := fxProfile)).certifiedCell

/-- Certified thinness view for the seed mode identity. -/
def certifiedSeedModeIdentityThin :
    CertifiedFXThinCell .mode 0 NegativeProbes.defaultInferScope where
  certifiedFXCell := certifiedSeedModeIdentity
  thinEvidence :=
    PolyCell.identityThinCell
      (Check.certifiedSeedModePackage (profile := fxProfile)).certifiedCell

/-- Certified thinness view for the identity over the seed dim-1 term cell. -/
def certifiedSeedTermStepIdentityThin :
    CertifiedFXThinCell .term 1 NegativeProbes.defaultInferScope where
  certifiedFXCell := certifiedSeedTermStepIdentity
  thinEvidence :=
    PolyCell.identityThinCell
      (Check.certifiedSeedTermStepPackage (profile := fxProfile)).certifiedCell

/-- Certified thinness view for the seed term identity composed with itself. -/
def certifiedSeedTermIdentityTwiceThin :
    CertifiedFXTermThinCell NegativeProbes.defaultInferScope where
  certifiedFXCell := certifiedSeedTermIdentityTwice
  thinEvidence :=
    PolyCell.verticalCompositeThinCell
      certifiedSeedTermIdentityThin.thinEvidence
      certifiedSeedTermIdentityThin.thinEvidence

theorem certifiedSeedTerm_raw :
    certifiedSeedTerm.toRaw = NegativeProbes.seedTermAtom fxProfile := rfl

theorem certifiedSeedType_raw :
    certifiedSeedType.toRaw = NegativeProbes.seedTypeAtom fxProfile := rfl

theorem certifiedSeedContext_raw :
    certifiedSeedContext.toRaw = NegativeProbes.seedContextAtom fxProfile := rfl

theorem certifiedSeedMode_raw :
    certifiedSeedMode.toRaw = NegativeProbes.seedModeAtom fxProfile := rfl

theorem certifiedApplicationVarZeroVarOne_raw :
    certifiedApplicationVarZeroVarOne.toRaw =
      NegativeProbes.applicationVarZeroVarOneRawCell fxProfile := rfl

theorem certifiedSeedTermStep_raw :
    certifiedSeedTermStep.toRaw =
      NegativeProbes.termStepVarZeroVarOneRawCell fxProfile := rfl

theorem certifiedSeedTermStep_sourceRaw :
    certifiedSeedTermStep.sourceRaw =
      NegativeProbes.seedTermAtom fxProfile := rfl

theorem certifiedSeedTermStep_targetRaw :
    certifiedSeedTermStep.targetRaw =
      NegativeProbes.alternateTermAtom fxProfile := rfl

theorem certifiedSeedTermIdentity_raw :
    certifiedSeedTermIdentity.toRaw =
      PolyTerm.identity (NegativeProbes.seedTermAtom fxProfile) := rfl

theorem certifiedSeedTermIdentity_sourceRaw :
    certifiedSeedTermIdentity.sourceRaw =
      NegativeProbes.seedTermAtom fxProfile := rfl

theorem certifiedSeedTermIdentity_targetRaw :
    certifiedSeedTermIdentity.targetRaw =
      NegativeProbes.seedTermAtom fxProfile := rfl

theorem certifiedSeedTypeIdentity_raw :
    certifiedSeedTypeIdentity.toRaw =
      PolyTerm.identity (NegativeProbes.seedTypeAtom fxProfile) := rfl

theorem certifiedSeedTypeIdentity_sourceRaw :
    certifiedSeedTypeIdentity.sourceRaw =
      NegativeProbes.seedTypeAtom fxProfile := rfl

theorem certifiedSeedTypeIdentity_targetRaw :
    certifiedSeedTypeIdentity.targetRaw =
      NegativeProbes.seedTypeAtom fxProfile := rfl

theorem certifiedSeedContextIdentity_raw :
    certifiedSeedContextIdentity.toRaw =
      PolyTerm.identity (NegativeProbes.seedContextAtom fxProfile) := rfl

theorem certifiedSeedContextIdentity_sourceRaw :
    certifiedSeedContextIdentity.sourceRaw =
      NegativeProbes.seedContextAtom fxProfile := rfl

theorem certifiedSeedContextIdentity_targetRaw :
    certifiedSeedContextIdentity.targetRaw =
      NegativeProbes.seedContextAtom fxProfile := rfl

theorem certifiedSeedModeIdentity_raw :
    certifiedSeedModeIdentity.toRaw =
      PolyTerm.identity (NegativeProbes.seedModeAtom fxProfile) := rfl

theorem certifiedSeedModeIdentity_sourceRaw :
    certifiedSeedModeIdentity.sourceRaw =
      NegativeProbes.seedModeAtom fxProfile := rfl

theorem certifiedSeedModeIdentity_targetRaw :
    certifiedSeedModeIdentity.targetRaw =
      NegativeProbes.seedModeAtom fxProfile := rfl

theorem certifiedSeedTermStepIdentity_raw :
    certifiedSeedTermStepIdentity.toRaw =
      PolyTerm.identity
        (NegativeProbes.termStepVarZeroVarOneRawCell fxProfile) := rfl

theorem certifiedSeedTermStepIdentity_sourceRaw :
    certifiedSeedTermStepIdentity.sourceRaw =
      NegativeProbes.termStepVarZeroVarOneRawCell fxProfile := rfl

theorem certifiedSeedTermStepIdentity_targetRaw :
    certifiedSeedTermStepIdentity.targetRaw =
      NegativeProbes.termStepVarZeroVarOneRawCell fxProfile := rfl

theorem certifiedSeedTermIdentityTwice_raw :
    certifiedSeedTermIdentityTwice.toRaw =
      PolyTerm.compV
        (PolyTerm.identity (NegativeProbes.seedTermAtom fxProfile))
        (PolyTerm.identity (NegativeProbes.seedTermAtom fxProfile)) := rfl

theorem certifiedSeedTermIdentityTwice_sourceRaw :
    certifiedSeedTermIdentityTwice.sourceRaw =
      NegativeProbes.seedTermAtom fxProfile := rfl

theorem certifiedSeedTermIdentityTwice_targetRaw :
    certifiedSeedTermIdentityTwice.targetRaw =
      NegativeProbes.seedTermAtom fxProfile := rfl

theorem certifiedSeedTermIdentityThin_raw :
    certifiedSeedTermIdentityThin.toRaw =
      PolyTerm.identity (NegativeProbes.seedTermAtom fxProfile) := rfl

theorem certifiedSeedTermIdentityThin_sourceRaw :
    certifiedSeedTermIdentityThin.sourceRaw =
      NegativeProbes.seedTermAtom fxProfile := rfl

theorem certifiedSeedTermIdentityThin_targetRaw :
    certifiedSeedTermIdentityThin.targetRaw =
      NegativeProbes.seedTermAtom fxProfile := rfl

theorem certifiedSeedTermIdentityTwiceThin_raw :
    certifiedSeedTermIdentityTwiceThin.toRaw =
      PolyTerm.compV
        (PolyTerm.identity (NegativeProbes.seedTermAtom fxProfile))
        (PolyTerm.identity (NegativeProbes.seedTermAtom fxProfile)) := rfl

theorem certifiedSeedTermIdentityTwiceThin_sourceRaw :
    certifiedSeedTermIdentityTwiceThin.sourceRaw =
      NegativeProbes.seedTermAtom fxProfile := rfl

theorem certifiedSeedTermIdentityTwiceThin_targetRaw :
    certifiedSeedTermIdentityTwiceThin.targetRaw =
      NegativeProbes.seedTermAtom fxProfile := rfl

end LeanFX2.Foundation.PolyCell.FXProfile
