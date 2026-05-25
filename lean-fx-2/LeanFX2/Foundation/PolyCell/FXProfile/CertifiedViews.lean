import LeanFX2.Foundation.PolyCell.Core.Check
/-!
# CertifiedViews — FX Names for Certified PolyCells

This file gives the FX profile honest view names over the certified cell
layer.  These are not raw subtype wrappers: every inhabitant carries an actual
`PolyCell` witness.  Conversion/thinness views are intentionally absent until
thinness has a certified predicate over dim-1 cells.
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

end CertifiedFXCell

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

theorem certifiedSeedTermIdentity_raw :
    certifiedSeedTermIdentity.toRaw =
      PolyTerm.identity (NegativeProbes.seedTermAtom fxProfile) := rfl

theorem certifiedSeedTypeIdentity_raw :
    certifiedSeedTypeIdentity.toRaw =
      PolyTerm.identity (NegativeProbes.seedTypeAtom fxProfile) := rfl

theorem certifiedSeedContextIdentity_raw :
    certifiedSeedContextIdentity.toRaw =
      PolyTerm.identity (NegativeProbes.seedContextAtom fxProfile) := rfl

theorem certifiedSeedModeIdentity_raw :
    certifiedSeedModeIdentity.toRaw =
      PolyTerm.identity (NegativeProbes.seedModeAtom fxProfile) := rfl

theorem certifiedSeedTermStepIdentity_raw :
    certifiedSeedTermStepIdentity.toRaw =
      PolyTerm.identity
        (NegativeProbes.termStepVarZeroVarOneRawCell fxProfile) := rfl

end LeanFX2.Foundation.PolyCell.FXProfile
