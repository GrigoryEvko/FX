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

end LeanFX2.Foundation.PolyCell.FXProfile
