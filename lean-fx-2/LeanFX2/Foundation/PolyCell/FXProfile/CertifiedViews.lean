import LeanFX2.Foundation.PolyCell.Core.Check
import LeanFX2.Foundation.PolyCell.Core.CertifyExact
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

/-- Endpoint-indexed certified positive-dimensional FX cell.

Unlike `CertifiedFXCell`, this view makes the source and target part of the
type.  Vertical composition can therefore demand a shared middle endpoint
without equality casts. -/
structure CertifiedFXArrow
    (cellSort : CellSort) (cellDimension : CellDim) (scope : Nat)
    (sourceRaw targetRaw : PolyTerm fxProfile cellDimension) where
  /-- Raw erasure of the certified arrow. -/
  rawCell : PolyTerm fxProfile (cellDimension + 1)
  /-- Certified witness with the exact indexed boundary. -/
  certifiedCell :
    PolyCell fxProfile cellSort (cellDimension + 1) scope
      (sourceRaw, targetRaw) rawCell

namespace CertifiedFXArrow

/-- Build an endpoint-indexed arrow from an exact certified witness. -/
def ofCell {cellSort : CellSort} {cellDimension scope : Nat}
    {sourceRaw targetRaw : PolyTerm fxProfile cellDimension}
    {rawCell : PolyTerm fxProfile (cellDimension + 1)}
    (certifiedCell :
      PolyCell fxProfile cellSort (cellDimension + 1) scope
        (sourceRaw, targetRaw) rawCell) :
    CertifiedFXArrow cellSort cellDimension scope sourceRaw targetRaw where
  rawCell := rawCell
  certifiedCell := certifiedCell

/-- Forget endpoint-indexing to the coarser certified FX cell view. -/
def toCertifiedFXCell {cellSort : CellSort} {cellDimension scope : Nat}
    {sourceRaw targetRaw : PolyTerm fxProfile cellDimension}
    (arrow :
      CertifiedFXArrow cellSort cellDimension scope sourceRaw targetRaw) :
    CertifiedFXCell cellSort (cellDimension + 1) scope where
  rawCell := arrow.rawCell
  cellBoundary := (sourceRaw, targetRaw)
  certifiedCell := arrow.certifiedCell

/-- Raw erasure of an endpoint-indexed certified arrow. -/
def toRaw {cellSort : CellSort} {cellDimension scope : Nat}
    {sourceRaw targetRaw : PolyTerm fxProfile cellDimension}
    (arrow :
      CertifiedFXArrow cellSort cellDimension scope sourceRaw targetRaw) :
    PolyTerm fxProfile (cellDimension + 1) :=
  arrow.rawCell

/-- Source endpoint of an endpoint-indexed certified arrow. -/
def source {cellSort : CellSort} {cellDimension scope : Nat}
    {sourceRaw targetRaw : PolyTerm fxProfile cellDimension}
    (_arrow :
      CertifiedFXArrow cellSort cellDimension scope sourceRaw targetRaw) :
    PolyTerm fxProfile cellDimension :=
  sourceRaw

/-- Target endpoint of an endpoint-indexed certified arrow. -/
def target {cellSort : CellSort} {cellDimension scope : Nat}
    {sourceRaw targetRaw : PolyTerm fxProfile cellDimension}
    (_arrow :
      CertifiedFXArrow cellSort cellDimension scope sourceRaw targetRaw) :
    PolyTerm fxProfile cellDimension :=
  targetRaw

/-- Identity arrow over any certified FX cell. -/
def identity {cellSort : CellSort} {cellDimension scope : Nat}
    (baseCell : CertifiedFXCell cellSort cellDimension scope) :
    CertifiedFXArrow cellSort cellDimension scope
      baseCell.rawCell baseCell.rawCell :=
  ofCell (PolyCell.identityCell baseCell.certifiedCell)

/-- Vertical composition of endpoint-indexed certified arrows. -/
def compV {cellSort : CellSort} {cellDimension scope : Nat}
    {sourceRaw middleRaw targetRaw : PolyTerm fxProfile cellDimension}
    (firstArrow :
      CertifiedFXArrow cellSort cellDimension scope sourceRaw middleRaw)
    (secondArrow :
      CertifiedFXArrow cellSort cellDimension scope middleRaw targetRaw) :
    CertifiedFXArrow cellSort cellDimension scope sourceRaw targetRaw :=
  ofCell
    (PolyCell.verticalCompositeCell
      firstArrow.certifiedCell
      secondArrow.certifiedCell)

/-- Raw erasure of an identity arrow is definitional. -/
theorem identity_raw {cellSort : CellSort} {cellDimension scope : Nat}
    (baseCell : CertifiedFXCell cellSort cellDimension scope) :
    (identity baseCell).toRaw =
      PolyTerm.identity (profile := fxProfile) baseCell.rawCell := rfl

/-- Source endpoint of an identity arrow is definitional. -/
theorem identity_source {cellSort : CellSort} {cellDimension scope : Nat}
    (baseCell : CertifiedFXCell cellSort cellDimension scope) :
    (identity baseCell).source = baseCell.rawCell := rfl

/-- Target endpoint of an identity arrow is definitional. -/
theorem identity_target {cellSort : CellSort} {cellDimension scope : Nat}
    (baseCell : CertifiedFXCell cellSort cellDimension scope) :
    (identity baseCell).target = baseCell.rawCell := rfl

/-- Raw erasure of vertical composition is definitional. -/
theorem compV_raw {cellSort : CellSort} {cellDimension scope : Nat}
    {sourceRaw middleRaw targetRaw : PolyTerm fxProfile cellDimension}
    (firstArrow :
      CertifiedFXArrow cellSort cellDimension scope sourceRaw middleRaw)
    (secondArrow :
      CertifiedFXArrow cellSort cellDimension scope middleRaw targetRaw) :
    (compV firstArrow secondArrow).toRaw =
      PolyTerm.compV (profile := fxProfile)
        firstArrow.rawCell secondArrow.rawCell := rfl

/-- Source endpoint of arrow vertical composition is definitional. -/
theorem compV_source {cellSort : CellSort} {cellDimension scope : Nat}
    {sourceRaw middleRaw targetRaw : PolyTerm fxProfile cellDimension}
    (firstArrow :
      CertifiedFXArrow cellSort cellDimension scope sourceRaw middleRaw)
    (secondArrow :
      CertifiedFXArrow cellSort cellDimension scope middleRaw targetRaw) :
    (compV firstArrow secondArrow).source = sourceRaw := rfl

/-- Target endpoint of arrow vertical composition is definitional. -/
theorem compV_target {cellSort : CellSort} {cellDimension scope : Nat}
    {sourceRaw middleRaw targetRaw : PolyTerm fxProfile cellDimension}
    (firstArrow :
      CertifiedFXArrow cellSort cellDimension scope sourceRaw middleRaw)
    (secondArrow :
      CertifiedFXArrow cellSort cellDimension scope middleRaw targetRaw) :
    (compV firstArrow secondArrow).target = targetRaw := rfl

end CertifiedFXArrow

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

/-- Endpoint-indexed certified thin positive-dimensional FX cell. -/
structure CertifiedFXThinArrow
    (cellSort : CellSort) (cellDimension : CellDim) (scope : Nat)
    (sourceRaw targetRaw : PolyTerm fxProfile cellDimension) where
  /-- Underlying endpoint-indexed certified arrow. -/
  certifiedArrow :
    CertifiedFXArrow cellSort cellDimension scope sourceRaw targetRaw
  /-- Certified structural thinness evidence for the underlying arrow. -/
  thinEvidence : PolyCell.ThinCell certifiedArrow.certifiedCell

namespace CertifiedFXThinArrow

/-- Forget thinness and keep the endpoint-indexed certified arrow. -/
def toCertifiedFXArrow {cellSort : CellSort} {cellDimension scope : Nat}
    {sourceRaw targetRaw : PolyTerm fxProfile cellDimension}
    (arrow :
      CertifiedFXThinArrow cellSort cellDimension scope sourceRaw targetRaw) :
    CertifiedFXArrow cellSort cellDimension scope sourceRaw targetRaw :=
  arrow.certifiedArrow

/-- Forget endpoint indexing and keep the coarser certified thin-cell view. -/
def toCertifiedFXThinCell {cellSort : CellSort} {cellDimension scope : Nat}
    {sourceRaw targetRaw : PolyTerm fxProfile cellDimension}
    (arrow :
      CertifiedFXThinArrow cellSort cellDimension scope sourceRaw targetRaw) :
    CertifiedFXThinCell cellSort cellDimension scope where
  certifiedFXCell := arrow.certifiedArrow.toCertifiedFXCell
  thinEvidence := arrow.thinEvidence

/-- Raw erasure of an endpoint-indexed certified thin arrow. -/
def toRaw {cellSort : CellSort} {cellDimension scope : Nat}
    {sourceRaw targetRaw : PolyTerm fxProfile cellDimension}
    (arrow :
      CertifiedFXThinArrow cellSort cellDimension scope sourceRaw targetRaw) :
    PolyTerm fxProfile (cellDimension + 1) :=
  arrow.certifiedArrow.toRaw

/-- Source endpoint of an endpoint-indexed certified thin arrow. -/
def source {cellSort : CellSort} {cellDimension scope : Nat}
    {sourceRaw targetRaw : PolyTerm fxProfile cellDimension}
    (arrow :
      CertifiedFXThinArrow cellSort cellDimension scope sourceRaw targetRaw) :
    PolyTerm fxProfile cellDimension :=
  arrow.certifiedArrow.source

/-- Target endpoint of an endpoint-indexed certified thin arrow. -/
def target {cellSort : CellSort} {cellDimension scope : Nat}
    {sourceRaw targetRaw : PolyTerm fxProfile cellDimension}
    (arrow :
      CertifiedFXThinArrow cellSort cellDimension scope sourceRaw targetRaw) :
    PolyTerm fxProfile cellDimension :=
  arrow.certifiedArrow.target

/-- Identity thin arrow over any certified FX cell. -/
def identity {cellSort : CellSort} {cellDimension scope : Nat}
    (baseCell : CertifiedFXCell cellSort cellDimension scope) :
    CertifiedFXThinArrow cellSort cellDimension scope
      baseCell.rawCell baseCell.rawCell where
  certifiedArrow := CertifiedFXArrow.identity baseCell
  thinEvidence := PolyCell.identityThinCell baseCell.certifiedCell

/-- Vertical composition of endpoint-indexed certified thin arrows. -/
def compV {cellSort : CellSort} {cellDimension scope : Nat}
    {sourceRaw middleRaw targetRaw : PolyTerm fxProfile cellDimension}
    (firstArrow :
      CertifiedFXThinArrow cellSort cellDimension scope sourceRaw middleRaw)
    (secondArrow :
      CertifiedFXThinArrow cellSort cellDimension scope middleRaw targetRaw) :
    CertifiedFXThinArrow cellSort cellDimension scope sourceRaw targetRaw where
  certifiedArrow :=
    CertifiedFXArrow.compV
      firstArrow.certifiedArrow
      secondArrow.certifiedArrow
  thinEvidence :=
    PolyCell.verticalCompositeThinCell
      firstArrow.thinEvidence
      secondArrow.thinEvidence

/-- Raw erasure of an identity thin arrow is definitional. -/
theorem identity_raw {cellSort : CellSort} {cellDimension scope : Nat}
    (baseCell : CertifiedFXCell cellSort cellDimension scope) :
    (identity baseCell).toRaw =
      PolyTerm.identity (profile := fxProfile) baseCell.rawCell := rfl

/-- Source endpoint of a thin identity arrow is definitional. -/
theorem identity_source {cellSort : CellSort} {cellDimension scope : Nat}
    (baseCell : CertifiedFXCell cellSort cellDimension scope) :
    (identity baseCell).source = baseCell.rawCell := rfl

/-- Target endpoint of a thin identity arrow is definitional. -/
theorem identity_target {cellSort : CellSort} {cellDimension scope : Nat}
    (baseCell : CertifiedFXCell cellSort cellDimension scope) :
    (identity baseCell).target = baseCell.rawCell := rfl

/-- Raw erasure of thin vertical composition is definitional. -/
theorem compV_raw {cellSort : CellSort} {cellDimension scope : Nat}
    {sourceRaw middleRaw targetRaw : PolyTerm fxProfile cellDimension}
    (firstArrow :
      CertifiedFXThinArrow cellSort cellDimension scope sourceRaw middleRaw)
    (secondArrow :
      CertifiedFXThinArrow cellSort cellDimension scope middleRaw targetRaw) :
    (compV firstArrow secondArrow).toRaw =
      PolyTerm.compV (profile := fxProfile)
        firstArrow.certifiedArrow.rawCell
        secondArrow.certifiedArrow.rawCell := rfl

/-- Source endpoint of thin-arrow vertical composition is definitional. -/
theorem compV_source {cellSort : CellSort} {cellDimension scope : Nat}
    {sourceRaw middleRaw targetRaw : PolyTerm fxProfile cellDimension}
    (firstArrow :
      CertifiedFXThinArrow cellSort cellDimension scope sourceRaw middleRaw)
    (secondArrow :
      CertifiedFXThinArrow cellSort cellDimension scope middleRaw targetRaw) :
    (compV firstArrow secondArrow).source = sourceRaw := rfl

/-- Target endpoint of thin-arrow vertical composition is definitional. -/
theorem compV_target {cellSort : CellSort} {cellDimension scope : Nat}
    {sourceRaw middleRaw targetRaw : PolyTerm fxProfile cellDimension}
    (firstArrow :
      CertifiedFXThinArrow cellSort cellDimension scope sourceRaw middleRaw)
    (secondArrow :
      CertifiedFXThinArrow cellSort cellDimension scope middleRaw targetRaw) :
    (compV firstArrow secondArrow).target = targetRaw := rfl

end CertifiedFXThinArrow

/-- Certified generating term step.

This is the first operationally named step view over the certified substrate.
It is still deliberately narrower than the legacy raw `FXStep`: the view carries
an endpoint-indexed certified term arrow and a proof that the raw erasure is a
single generating dim-1 cell, not an identity or composite. -/
structure CertifiedFXGeneratingStep (scope : Nat)
    (sourceRaw targetRaw : PolyTerm fxProfile 0) where
  /-- Underlying endpoint-indexed certified term arrow. -/
  certifiedArrow :
    CertifiedFXArrow .term 0 scope sourceRaw targetRaw
  /-- The raw erasure is one generating dim-1 cell. -/
  hasGeneratingStepCell :
    certifiedArrow.rawCell.isGeneratingStepCell = true

namespace CertifiedFXGeneratingStep

/-- Forget generating-step evidence and keep the certified arrow. -/
def toCertifiedFXArrow {scope : Nat}
    {sourceRaw targetRaw : PolyTerm fxProfile 0}
    (step : CertifiedFXGeneratingStep scope sourceRaw targetRaw) :
    CertifiedFXArrow .term 0 scope sourceRaw targetRaw :=
  step.certifiedArrow

/-- Forget endpoint indexing and keep the underlying certified FX cell. -/
def toCertifiedFXCell {scope : Nat}
    {sourceRaw targetRaw : PolyTerm fxProfile 0}
    (step : CertifiedFXGeneratingStep scope sourceRaw targetRaw) :
    CertifiedFXCell .term 1 scope :=
  step.certifiedArrow.toCertifiedFXCell

/-- Raw erasure of a certified generating step. -/
def toRaw {scope : Nat} {sourceRaw targetRaw : PolyTerm fxProfile 0}
    (step : CertifiedFXGeneratingStep scope sourceRaw targetRaw) :
    PolyTerm fxProfile 1 :=
  step.certifiedArrow.toRaw

/-- Source endpoint of a certified generating step. -/
def source {scope : Nat} {sourceRaw targetRaw : PolyTerm fxProfile 0}
    (step : CertifiedFXGeneratingStep scope sourceRaw targetRaw) :
    PolyTerm fxProfile 0 :=
  step.certifiedArrow.source

/-- Target endpoint of a certified generating step. -/
def target {scope : Nat} {sourceRaw targetRaw : PolyTerm fxProfile 0}
    (step : CertifiedFXGeneratingStep scope sourceRaw targetRaw) :
    PolyTerm fxProfile 0 :=
  step.certifiedArrow.target

/-- Certified generating steps erase to raw generating step cells. -/
theorem toRaw_isGeneratingStepCell {scope : Nat}
    {sourceRaw targetRaw : PolyTerm fxProfile 0}
    (step : CertifiedFXGeneratingStep scope sourceRaw targetRaw) :
    step.toRaw.isGeneratingStepCell = true :=
  step.hasGeneratingStepCell

/-- Certified generating steps are accepted by the older raw step recognizer. -/
theorem toRaw_isStepCell {scope : Nat}
    {sourceRaw targetRaw : PolyTerm fxProfile 0}
    (step : CertifiedFXGeneratingStep scope sourceRaw targetRaw) :
    step.toRaw.isStepCell = true :=
  PolyTerm.isStepCell_of_isGeneratingStepCell
    step.toRaw step.hasGeneratingStepCell

end CertifiedFXGeneratingStep

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

/-- Endpoint-indexed certified term arrow at dimension 2. -/
abbrev CertifiedFXDimTwoTermArrow (scope : Nat)
    (sourceRaw targetRaw : PolyTerm fxProfile 1) :=
  CertifiedFXArrow .term 1 scope sourceRaw targetRaw

/-- Certified thin term cell at dimension 1.

This is a structural thin cell, not yet the final legacy `Conv` bridge. -/
abbrev CertifiedFXTermThinCell (scope : Nat) :=
  CertifiedFXThinCell .term 0 scope

/-- Certified thin type cell at dimension 1. -/
abbrev CertifiedFXTypeThinCell (scope : Nat) :=
  CertifiedFXThinCell .type 0 scope

/-- Certified thin context cell at dimension 1. -/
abbrev CertifiedFXContextThinCell (scope : Nat) :=
  CertifiedFXThinCell .context 0 scope

/-- Certified thin mode cell at dimension 1. -/
abbrev CertifiedFXModeThinCell (scope : Nat) :=
  CertifiedFXThinCell .mode 0 scope

/-- Endpoint-indexed certified term arrow at dimension 1. -/
abbrev CertifiedFXTermArrow (scope : Nat)
    (sourceRaw targetRaw : PolyTerm fxProfile 0) :=
  CertifiedFXArrow .term 0 scope sourceRaw targetRaw

/-- Endpoint-indexed certified type arrow at dimension 1. -/
abbrev CertifiedFXTypeArrow (scope : Nat)
    (sourceRaw targetRaw : PolyTerm fxProfile 0) :=
  CertifiedFXArrow .type 0 scope sourceRaw targetRaw

/-- Endpoint-indexed certified context arrow at dimension 1. -/
abbrev CertifiedFXContextArrow (scope : Nat)
    (sourceRaw targetRaw : PolyTerm fxProfile 0) :=
  CertifiedFXArrow .context 0 scope sourceRaw targetRaw

/-- Endpoint-indexed certified mode arrow at dimension 1. -/
abbrev CertifiedFXModeArrow (scope : Nat)
    (sourceRaw targetRaw : PolyTerm fxProfile 0) :=
  CertifiedFXArrow .mode 0 scope sourceRaw targetRaw

/-- Endpoint-indexed certified thin term arrow at dimension 1. -/
abbrev CertifiedFXTermThinArrow (scope : Nat)
    (sourceRaw targetRaw : PolyTerm fxProfile 0) :=
  CertifiedFXThinArrow .term 0 scope sourceRaw targetRaw

/-- Endpoint-indexed certified thin term arrow at dimension 2. -/
abbrev CertifiedFXDimTwoTermThinArrow (scope : Nat)
    (sourceRaw targetRaw : PolyTerm fxProfile 1) :=
  CertifiedFXThinArrow .term 1 scope sourceRaw targetRaw

/-- Certified structural term conversion at dimension 1.

This names the current certified-thin term-arrow layer.  It is not the final
legacy `Conv` bridge: only structural thin arrows built from certified
identities and vertical composition of thin arrows inhabit it. -/
abbrev CertifiedFXStructuralConv (scope : Nat)
    (sourceRaw targetRaw : PolyTerm fxProfile 0) :=
  CertifiedFXTermThinArrow scope sourceRaw targetRaw

/-- Endpoint-indexed certified thin type arrow at dimension 1. -/
abbrev CertifiedFXTypeThinArrow (scope : Nat)
    (sourceRaw targetRaw : PolyTerm fxProfile 0) :=
  CertifiedFXThinArrow .type 0 scope sourceRaw targetRaw

/-- Endpoint-indexed certified thin context arrow at dimension 1. -/
abbrev CertifiedFXContextThinArrow (scope : Nat)
    (sourceRaw targetRaw : PolyTerm fxProfile 0) :=
  CertifiedFXThinArrow .context 0 scope sourceRaw targetRaw

/-- Endpoint-indexed certified thin mode arrow at dimension 1. -/
abbrev CertifiedFXModeThinArrow (scope : Nat)
    (sourceRaw targetRaw : PolyTerm fxProfile 0) :=
  CertifiedFXThinArrow .mode 0 scope sourceRaw targetRaw

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

/-- Certified term view for the first finite lambda payload. -/
def certifiedLambdaUnitTypeBodyVarZero :
    CertifiedFXTerm NegativeProbes.defaultInferScope :=
  CertifiedFXCell.ofCertifiedRawCell
    (Check.certifiedLambdaUnitTypeBodyVarZeroPackage (profile := fxProfile)
      (Check.certifiedLambdaUnitTypeBodyVarZeroChildren (profile := fxProfile)
        (scope := NegativeProbes.defaultInferScope)))

/-- Certified type view for the first finite pi-type payload. -/
def certifiedPiTypeUnitCodomainUnit :
    CertifiedFXType NegativeProbes.defaultInferScope :=
  CertifiedFXCell.ofCertifiedRawCell
    (Check.certifiedPiTypeUnitCodomainUnitPackage (profile := fxProfile)
      (Check.certifiedPiTypeUnitCodomainUnitChildren (profile := fxProfile)
        (scope := NegativeProbes.defaultInferScope)))

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
    CertifiedFXTypeThinCell NegativeProbes.defaultInferScope where
  certifiedFXCell := certifiedSeedTypeIdentity
  thinEvidence :=
    PolyCell.identityThinCell
      (Check.certifiedSeedTypePackage (profile := fxProfile)).certifiedCell

/-- Certified thinness view for the seed context identity. -/
def certifiedSeedContextIdentityThin :
    CertifiedFXContextThinCell NegativeProbes.defaultInferScope where
  certifiedFXCell := certifiedSeedContextIdentity
  thinEvidence :=
    PolyCell.identityThinCell
      (Check.certifiedSeedContextPackage (profile := fxProfile)).certifiedCell

/-- Certified thinness view for the seed mode identity. -/
def certifiedSeedModeIdentityThin :
    CertifiedFXModeThinCell NegativeProbes.defaultInferScope where
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

/-- Endpoint-indexed arrow for the seed dim-1 term-step fixture. -/
def certifiedSeedTermStepArrow :
    CertifiedFXTermArrow NegativeProbes.defaultInferScope
      (NegativeProbes.seedTermAtom fxProfile)
      (NegativeProbes.alternateTermAtom fxProfile) :=
  CertifiedFXArrow.ofCell
    (Check.certifiedSeedTermStepPackage
      (profile := fxProfile)).certifiedCell

/-- Certified generating-step view for the first dim-1 term-step fixture. -/
def certifiedSeedTermGeneratingStep :
    CertifiedFXGeneratingStep NegativeProbes.defaultInferScope
      (NegativeProbes.seedTermAtom fxProfile)
      (NegativeProbes.alternateTermAtom fxProfile) where
  certifiedArrow := certifiedSeedTermStepArrow
  hasGeneratingStepCell := rfl

/-- Endpoint-indexed dim-2 arrow for the identity over the seed term step. -/
def certifiedSeedTermStepIdentityArrow :
    CertifiedFXDimTwoTermArrow NegativeProbes.defaultInferScope
      (NegativeProbes.termStepVarZeroVarOneRawCell fxProfile)
      (NegativeProbes.termStepVarZeroVarOneRawCell fxProfile) :=
  CertifiedFXArrow.identity certifiedSeedTermStep

/-- Endpoint-indexed dim-2 thin arrow for the identity over the seed term
step. -/
def certifiedSeedTermStepIdentityThinArrow :
    CertifiedFXDimTwoTermThinArrow NegativeProbes.defaultInferScope
      (NegativeProbes.termStepVarZeroVarOneRawCell fxProfile)
      (NegativeProbes.termStepVarZeroVarOneRawCell fxProfile) :=
  CertifiedFXThinArrow.identity certifiedSeedTermStep

/-- Endpoint-indexed thin arrow for the seed term identity. -/
def certifiedSeedTermIdentityThinArrow :
    CertifiedFXTermThinArrow NegativeProbes.defaultInferScope
      (NegativeProbes.seedTermAtom fxProfile)
      (NegativeProbes.seedTermAtom fxProfile) :=
  CertifiedFXThinArrow.identity certifiedSeedTerm

/-- Endpoint-indexed thin arrow for the seed type identity. -/
def certifiedSeedTypeIdentityThinArrow :
    CertifiedFXTypeThinArrow NegativeProbes.defaultInferScope
      (NegativeProbes.seedTypeAtom fxProfile)
      (NegativeProbes.seedTypeAtom fxProfile) :=
  CertifiedFXThinArrow.identity certifiedSeedType

/-- Endpoint-indexed thin arrow for the seed context identity. -/
def certifiedSeedContextIdentityThinArrow :
    CertifiedFXContextThinArrow NegativeProbes.defaultInferScope
      (NegativeProbes.seedContextAtom fxProfile)
      (NegativeProbes.seedContextAtom fxProfile) :=
  CertifiedFXThinArrow.identity certifiedSeedContext

/-- Endpoint-indexed thin arrow for the seed mode identity. -/
def certifiedSeedModeIdentityThinArrow :
    CertifiedFXModeThinArrow NegativeProbes.defaultInferScope
      (NegativeProbes.seedModeAtom fxProfile)
      (NegativeProbes.seedModeAtom fxProfile) :=
  CertifiedFXThinArrow.identity certifiedSeedMode

/-- Endpoint-indexed thin arrow for the seed term identity composed with
itself. -/
def certifiedSeedTermIdentityTwiceThinArrow :
    CertifiedFXTermThinArrow NegativeProbes.defaultInferScope
      (NegativeProbes.seedTermAtom fxProfile)
      (NegativeProbes.seedTermAtom fxProfile) :=
  CertifiedFXThinArrow.compV
    certifiedSeedTermIdentityThinArrow
    certifiedSeedTermIdentityThinArrow

/-- Certified structural conversion for the seed term reflexivity arrow. -/
def certifiedSeedTermStructuralReflConv :
    CertifiedFXStructuralConv NegativeProbes.defaultInferScope
      (NegativeProbes.seedTermAtom fxProfile)
      (NegativeProbes.seedTermAtom fxProfile) :=
  certifiedSeedTermIdentityThinArrow

/-- Certified structural conversion for reflexivity composed with itself. -/
def certifiedSeedTermStructuralReflConvTwice :
    CertifiedFXStructuralConv NegativeProbes.defaultInferScope
      (NegativeProbes.seedTermAtom fxProfile)
      (NegativeProbes.seedTermAtom fxProfile) :=
  certifiedSeedTermIdentityTwiceThinArrow

/-- Endpoint-indexed thin arrow for the seed type identity composed with
itself. -/
def certifiedSeedTypeIdentityTwiceThinArrow :
    CertifiedFXTypeThinArrow NegativeProbes.defaultInferScope
      (NegativeProbes.seedTypeAtom fxProfile)
      (NegativeProbes.seedTypeAtom fxProfile) :=
  CertifiedFXThinArrow.compV
    certifiedSeedTypeIdentityThinArrow
    certifiedSeedTypeIdentityThinArrow

/-- Endpoint-indexed thin arrow for the seed context identity composed with
itself. -/
def certifiedSeedContextIdentityTwiceThinArrow :
    CertifiedFXContextThinArrow NegativeProbes.defaultInferScope
      (NegativeProbes.seedContextAtom fxProfile)
      (NegativeProbes.seedContextAtom fxProfile) :=
  CertifiedFXThinArrow.compV
    certifiedSeedContextIdentityThinArrow
    certifiedSeedContextIdentityThinArrow

/-- Endpoint-indexed thin arrow for the seed mode identity composed with
itself. -/
def certifiedSeedModeIdentityTwiceThinArrow :
    CertifiedFXModeThinArrow NegativeProbes.defaultInferScope
      (NegativeProbes.seedModeAtom fxProfile)
      (NegativeProbes.seedModeAtom fxProfile) :=
  CertifiedFXThinArrow.compV
    certifiedSeedModeIdentityThinArrow
    certifiedSeedModeIdentityThinArrow

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

theorem certifiedLambdaUnitTypeBodyVarZero_raw :
    certifiedLambdaUnitTypeBodyVarZero.toRaw =
      NegativeProbes.lambdaUnitTypeBodyVarZeroRawCell fxProfile := rfl

theorem certifiedPiTypeUnitCodomainUnit_raw :
    certifiedPiTypeUnitCodomainUnit.toRaw =
      NegativeProbes.piTypeUnitCodomainUnitRawCell fxProfile := rfl

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

theorem certifiedSeedTermStepArrow_raw :
    certifiedSeedTermStepArrow.toRaw =
      NegativeProbes.termStepVarZeroVarOneRawCell fxProfile := rfl

theorem certifiedSeedTermStepArrow_source :
    certifiedSeedTermStepArrow.source =
      NegativeProbes.seedTermAtom fxProfile := rfl

theorem certifiedSeedTermStepArrow_target :
    certifiedSeedTermStepArrow.target =
      NegativeProbes.alternateTermAtom fxProfile := rfl

theorem certifiedSeedTermGeneratingStep_raw :
    certifiedSeedTermGeneratingStep.toRaw =
      NegativeProbes.termStepVarZeroVarOneRawCell fxProfile := rfl

theorem certifiedSeedTermGeneratingStep_source :
    certifiedSeedTermGeneratingStep.source =
      NegativeProbes.seedTermAtom fxProfile := rfl

theorem certifiedSeedTermGeneratingStep_target :
    certifiedSeedTermGeneratingStep.target =
      NegativeProbes.alternateTermAtom fxProfile := rfl

theorem certifiedSeedTermGeneratingStep_isGeneratingStepCell :
    certifiedSeedTermGeneratingStep.toRaw.isGeneratingStepCell = true := rfl

theorem certifiedSeedTermGeneratingStep_isStepCell :
    certifiedSeedTermGeneratingStep.toRaw.isStepCell = true := rfl

theorem certifiedSeedTermStepIdentityArrow_raw :
    certifiedSeedTermStepIdentityArrow.toRaw =
      PolyTerm.identity
        (NegativeProbes.termStepVarZeroVarOneRawCell fxProfile) := rfl

theorem certifiedSeedTermStepIdentityArrow_source :
    certifiedSeedTermStepIdentityArrow.source =
      NegativeProbes.termStepVarZeroVarOneRawCell fxProfile := rfl

theorem certifiedSeedTermStepIdentityArrow_target :
    certifiedSeedTermStepIdentityArrow.target =
      NegativeProbes.termStepVarZeroVarOneRawCell fxProfile := rfl

theorem certifiedSeedTermStepIdentityThinArrow_raw :
    certifiedSeedTermStepIdentityThinArrow.toRaw =
      PolyTerm.identity
        (NegativeProbes.termStepVarZeroVarOneRawCell fxProfile) := rfl

theorem certifiedSeedTermStepIdentityThinArrow_source :
    certifiedSeedTermStepIdentityThinArrow.source =
      NegativeProbes.termStepVarZeroVarOneRawCell fxProfile := rfl

theorem certifiedSeedTermStepIdentityThinArrow_target :
    certifiedSeedTermStepIdentityThinArrow.target =
      NegativeProbes.termStepVarZeroVarOneRawCell fxProfile := rfl

theorem certifiedSeedTermIdentityThinArrow_raw :
    certifiedSeedTermIdentityThinArrow.toRaw =
      PolyTerm.identity (NegativeProbes.seedTermAtom fxProfile) := rfl

theorem certifiedSeedTermIdentityThinArrow_source :
    certifiedSeedTermIdentityThinArrow.source =
      NegativeProbes.seedTermAtom fxProfile := rfl

theorem certifiedSeedTermIdentityThinArrow_target :
    certifiedSeedTermIdentityThinArrow.target =
      NegativeProbes.seedTermAtom fxProfile := rfl

theorem certifiedSeedTypeIdentityThinArrow_raw :
    certifiedSeedTypeIdentityThinArrow.toRaw =
      PolyTerm.identity (NegativeProbes.seedTypeAtom fxProfile) := rfl

theorem certifiedSeedTypeIdentityThinArrow_source :
    certifiedSeedTypeIdentityThinArrow.source =
      NegativeProbes.seedTypeAtom fxProfile := rfl

theorem certifiedSeedTypeIdentityThinArrow_target :
    certifiedSeedTypeIdentityThinArrow.target =
      NegativeProbes.seedTypeAtom fxProfile := rfl

theorem certifiedSeedContextIdentityThinArrow_raw :
    certifiedSeedContextIdentityThinArrow.toRaw =
      PolyTerm.identity (NegativeProbes.seedContextAtom fxProfile) := rfl

theorem certifiedSeedContextIdentityThinArrow_source :
    certifiedSeedContextIdentityThinArrow.source =
      NegativeProbes.seedContextAtom fxProfile := rfl

theorem certifiedSeedContextIdentityThinArrow_target :
    certifiedSeedContextIdentityThinArrow.target =
      NegativeProbes.seedContextAtom fxProfile := rfl

theorem certifiedSeedModeIdentityThinArrow_raw :
    certifiedSeedModeIdentityThinArrow.toRaw =
      PolyTerm.identity (NegativeProbes.seedModeAtom fxProfile) := rfl

theorem certifiedSeedModeIdentityThinArrow_source :
    certifiedSeedModeIdentityThinArrow.source =
      NegativeProbes.seedModeAtom fxProfile := rfl

theorem certifiedSeedModeIdentityThinArrow_target :
    certifiedSeedModeIdentityThinArrow.target =
      NegativeProbes.seedModeAtom fxProfile := rfl

theorem certifiedSeedTermIdentityTwiceThinArrow_raw :
    certifiedSeedTermIdentityTwiceThinArrow.toRaw =
      PolyTerm.compV
        (PolyTerm.identity (NegativeProbes.seedTermAtom fxProfile))
        (PolyTerm.identity (NegativeProbes.seedTermAtom fxProfile)) := rfl

theorem certifiedSeedTermIdentityTwiceThinArrow_source :
    certifiedSeedTermIdentityTwiceThinArrow.source =
      NegativeProbes.seedTermAtom fxProfile := rfl

theorem certifiedSeedTermIdentityTwiceThinArrow_target :
    certifiedSeedTermIdentityTwiceThinArrow.target =
      NegativeProbes.seedTermAtom fxProfile := rfl

theorem certifiedSeedTermStructuralReflConv_raw :
    certifiedSeedTermStructuralReflConv.toRaw =
      PolyTerm.identity (NegativeProbes.seedTermAtom fxProfile) := rfl

theorem certifiedSeedTermStructuralReflConv_source :
    certifiedSeedTermStructuralReflConv.source =
      NegativeProbes.seedTermAtom fxProfile := rfl

theorem certifiedSeedTermStructuralReflConv_target :
    certifiedSeedTermStructuralReflConv.target =
      NegativeProbes.seedTermAtom fxProfile := rfl

theorem certifiedSeedTermStructuralReflConvTwice_raw :
    certifiedSeedTermStructuralReflConvTwice.toRaw =
      PolyTerm.compV
        (PolyTerm.identity (NegativeProbes.seedTermAtom fxProfile))
        (PolyTerm.identity (NegativeProbes.seedTermAtom fxProfile)) := rfl

theorem certifiedSeedTermStructuralReflConvTwice_source :
    certifiedSeedTermStructuralReflConvTwice.source =
      NegativeProbes.seedTermAtom fxProfile := rfl

theorem certifiedSeedTermStructuralReflConvTwice_target :
    certifiedSeedTermStructuralReflConvTwice.target =
      NegativeProbes.seedTermAtom fxProfile := rfl

theorem certifiedSeedTypeIdentityTwiceThinArrow_raw :
    certifiedSeedTypeIdentityTwiceThinArrow.toRaw =
      PolyTerm.compV
        (PolyTerm.identity (NegativeProbes.seedTypeAtom fxProfile))
        (PolyTerm.identity (NegativeProbes.seedTypeAtom fxProfile)) := rfl

theorem certifiedSeedTypeIdentityTwiceThinArrow_source :
    certifiedSeedTypeIdentityTwiceThinArrow.source =
      NegativeProbes.seedTypeAtom fxProfile := rfl

theorem certifiedSeedTypeIdentityTwiceThinArrow_target :
    certifiedSeedTypeIdentityTwiceThinArrow.target =
      NegativeProbes.seedTypeAtom fxProfile := rfl

theorem certifiedSeedContextIdentityTwiceThinArrow_raw :
    certifiedSeedContextIdentityTwiceThinArrow.toRaw =
      PolyTerm.compV
        (PolyTerm.identity (NegativeProbes.seedContextAtom fxProfile))
        (PolyTerm.identity (NegativeProbes.seedContextAtom fxProfile)) := rfl

theorem certifiedSeedContextIdentityTwiceThinArrow_source :
    certifiedSeedContextIdentityTwiceThinArrow.source =
      NegativeProbes.seedContextAtom fxProfile := rfl

theorem certifiedSeedContextIdentityTwiceThinArrow_target :
    certifiedSeedContextIdentityTwiceThinArrow.target =
      NegativeProbes.seedContextAtom fxProfile := rfl

theorem certifiedSeedModeIdentityTwiceThinArrow_raw :
    certifiedSeedModeIdentityTwiceThinArrow.toRaw =
      PolyTerm.compV
        (PolyTerm.identity (NegativeProbes.seedModeAtom fxProfile))
        (PolyTerm.identity (NegativeProbes.seedModeAtom fxProfile)) := rfl

theorem certifiedSeedModeIdentityTwiceThinArrow_source :
    certifiedSeedModeIdentityTwiceThinArrow.source =
      NegativeProbes.seedModeAtom fxProfile := rfl

theorem certifiedSeedModeIdentityTwiceThinArrow_target :
    certifiedSeedModeIdentityTwiceThinArrow.target =
      NegativeProbes.seedModeAtom fxProfile := rfl

/-- General FX raw-indexed certifier: one entry point certifying any non-`compH`
FX raw cell at any dimension, with the certified result indexed by the EXACT
input so erasure back to the input is definitional.  This is the canonical
general ingress for the FX profile — atoms, identities, generating cells, and
vertical composites all route through it. -/
def certifyFXCellExact? (scope : Nat) {dim : CellDim}
    (rawCell : PolyTerm fxProfile dim) :
    Except CellCheckRejection (Check.CertifiedRawCell fxProfile scope rawCell) :=
  Check.certifyRawCellExact? scope rawCell

/-- General FX ingress returning the existential certified-result package
(carrying inferred sort, dimension, the certified cell, and a raw-code
preservation certificate). -/
def certifyFXCell? (scope : Nat) {dim : CellDim}
    (rawCell : PolyTerm fxProfile dim) :
    Except CellCheckRejection (Check.CertifiedRawCellResult fxProfile scope) :=
  Check.inferRawCellGeneral? scope rawCell

/-- The general FX certifier rejects horizontal composition pending Gray
semantics. -/
theorem certifyFXCellExact?_compH_rejects {scope : Nat} {dim : CellDim}
    (left right : PolyTerm fxProfile (dim + 1)) :
    certifyFXCellExact? scope (PolyTerm.compH left right) =
      Except.error .unsupportedCompH := rfl

/-- Every cell accepted by the general FX certifier erases exactly to its raw
input — the FX-level statement of no-false-positives. -/
theorem certifyFXCellExact?_sound {scope : Nat} {dim : CellDim}
    {rawCell : PolyTerm fxProfile dim}
    (certifiedCell : Check.CertifiedRawCell fxProfile scope rawCell)
    (accepted : certifyFXCellExact? scope rawCell = Except.ok certifiedCell) :
    certifiedCell.certifiedCell.raw = rawCell :=
  Check.certifyRawCellExact?_sound certifiedCell accepted

/-- The existential FX ingress recovers the input dimension on accept: the
dimension-erased result's `cellDimension` equals the input cell's dimension. -/
theorem certifyFXCell?_accepted_cellDimension_eq {scope : Nat} {dim : CellDim}
    {rawCell : PolyTerm fxProfile dim}
    {result : Check.CertifiedRawCellResult fxProfile scope}
    (accepted : certifyFXCell? scope rawCell = Except.ok result) :
    result.cellDimension = dim :=
  Check.inferRawCellGeneral?_accepted_cellDimension_eq accepted

/-- Every cell accepted by the existential FX ingress erases exactly to its raw
input (heterogeneously over the erased dimension) — the FX-level statement of
no-false-positives for the existential `certifyFXCell?` entry point. -/
theorem certifyFXCell?_sound {scope : Nat} {dim : CellDim}
    {rawCell : PolyTerm fxProfile dim}
    {result : Check.CertifiedRawCellResult fxProfile scope}
    (accepted : certifyFXCell? scope rawCell = Except.ok result) :
    HEq result.certifiedCell.raw rawCell :=
  Check.inferRawCellGeneral?_sound accepted

end LeanFX2.Foundation.PolyCell.FXProfile
