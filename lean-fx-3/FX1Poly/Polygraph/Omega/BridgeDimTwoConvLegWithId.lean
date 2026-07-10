import FX1Poly.Polygraph.Omega.BridgeDimTwoWithId

/-! # Polygraph/Omega/BridgeDimTwoConvLegWithId — the n=2 bridge conv leg over the idCongr sibling
(OMEGA bridge round, the leg (ii) closure)

★ **The residual the `SuspensionWithIdLedger` named as leg (ii): the full `TwoCellConv →
SaturatedConvOverWithId` induction carrying the free dim-2 convertibility into the sibling congruence over
`toCellDimTwo`.**  `BridgeDimTwoWithId` shipped the STATEMENT `bridgeDimTwoHoldsWithId` and discharged the
KEY step (`vcompIdLeft`) on the crown carrier (`crownJam_dischargedWithId`); this file discharges the WHOLE
conv leg over the sibling, inhabiting `bridgeDimTwoHoldsWithId` for every signature.

## The induction shape (recon A-census)

`TwoCellConv` has four constructors (`ofStep / refl / symm / trans`); `refl / symm / trans` map to the
sibling namesakes, `ofStep` inducts on `TwoCellStep` (twelve constructors).  The twelve step arms:

  * associativity / whisker-vcomp-functoriality / interchange-of-vcomps → `ofRelation` of the matching
    `StrictAxiomRel` row (defeq-shape or the derived Godement middle-four);
  * the four one-hole congruences → the sibling's namesake congruences on the inductive hypothesis;
  * the two `vcompId` units → `vcompIdLeft_bridgedWithId` / `vcompIdRight_bridgedWithId` (the boundary
    coherence lifted by `idCongr`, the unit row absorbing the trailing identity);
  * the two `whiskerId` units → `whiskerLeftUnit` / `whiskerRightUnit` then `idCongr` of the composePath
    coherence.

## The supporting coherences (all NEW, ported / mirrored)

  * `realizePathCellSig_boundarySource` — the source boundary of a realised 1-cell is its start mode (port
    of `realizePathCell_boundarySource`).
  * `realizePathCellSig_composePath_convWithId` — `realize (p . q) ~ (realize p) . (realize q)` over the
    sibling (port of `realizePath_composePath_conv`).
  * `toCellDimTwo_boundarySource_convWithId` / `toCellDimTwo_boundaryTarget_convWithId` — the translated
    2-cell's structural boundary is convertible to the realised source / target path (the composePath
    coherence threaded through the whisker cases).
  * `vcompIdRight_bridgedWithId` — the right-unit mirror of the shipped `vcompIdLeft_bridgedWithId`.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

open FX1Poly.Polygraph

/-! ## Firing a strict-axiom row into the sibling over any presentation -/

/-- Fire a strict omega-law row as a sibling convertibility over the union base relation (`Or.inl`), for any
presentation rows.  The uniform way every strict step below enters `SaturatedConvOverWithId`. -/
def strictRowWithId {computad : OmegaComputad} {presentationRows : CellRelOver computad} {dim : Nat}
    {cellAlpha cellBeta : CellExpr computad dim} (row : StrictAxiomRel computad cellAlpha cellBeta) :
    SaturatedConvOverWithId computad (unionCellRel computad (StrictAxiomRel computad) presentationRows)
      cellAlpha cellBeta :=
  SaturatedConvOverWithId.ofRelation (Or.inl row)

/-! ## The right-unit mirror of `vcompIdLeft_bridgedWithId` -/

/-- ★ **The `vcompIdRight` jam step, discharged over the sibling.**  The right-unit mirror of the shipped
`vcompIdLeft_bridgedWithId`: from a convertibility `targetCandidate ~ boundaryTarget cellA`, `idCongr` lifts
it to the identity 1-cells, `vcompCongrRight` places it under the vertical composite, and the unit row
absorbs the trailing identity — yielding `vcomp cellA (id targetCandidate) ~ cellA`. -/
theorem vcompIdRight_bridgedWithId {computad : OmegaComputad} {baseRel : CellRelOver computad}
    {dim : Nat} {targetCandidate : CellExpr computad dim} (cellA : CellExpr computad (dim + 1))
    (hconv : SaturatedConvOverWithId computad baseRel targetCandidate (boundaryTarget cellA))
    (unitRow : SaturatedConvOverWithId computad baseRel
      (CellExpr.vcomp cellA (CellExpr.id (boundaryTarget cellA))) cellA) :
    SaturatedConvOverWithId computad baseRel
      (CellExpr.vcomp cellA (CellExpr.id targetCandidate)) cellA :=
  SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.vcompCongrRight cellA (SaturatedConvOverWithId.idCongr hconv))
    unitRow

/-! ## Porting the dim-1 collapse coherences to the signature computad, over the sibling -/

/-- The source boundary of a realised 1-cell over the signature computad is its start mode — the
`computadOfSignature` / sibling port of `realizePathCell_boundarySource`. -/
theorem realizePathCellSig_boundarySource {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (path : ModalityPath signature.graph sourceMode targetMode) :
    boundarySource (realizePathCellSig path) = CellExpr.ofMode sourceMode := by
  cases path with
  | nil _ => rfl
  | cons _ _ => rfl

/-- ★ **`realizePathCellSig` is a homomorphism up to the strict laws, over the sibling.**  Path composition
maps to vertical composition modulo `SaturatedConvOverWithId (StrictAxiomRel union presentationRows)`: the
`nil` case fires `vcompUnitLeft` (its source boundary read off by `realizePathCellSig_boundarySource`), the
`cons` case threads the inductive hypothesis under `vcompCongrRight` and re-associates with `vcompAssoc`.
The sibling port of `realizePath_composePath_conv`. -/
theorem realizePathCellSig_composePath_convWithId {signature : ModeSignature}
    {presentationRows : CellRelOver (computadOfSignature signature)}
    {sourceMode middleMode : signature.graph.Mode}
    (first : ModalityPath signature.graph sourceMode middleMode) :
    ∀ {targetMode : signature.graph.Mode} (second : ModalityPath signature.graph middleMode targetMode),
      SaturatedConvOverWithId (computadOfSignature signature)
        (unionCellRel (computadOfSignature signature) (StrictAxiomRel (computadOfSignature signature))
          presentationRows)
        (realizePathCellSig (composePath first second))
        (CellExpr.vcomp (realizePathCellSig first) (realizePathCellSig second)) := by
  induction first with
  | nil _ =>
      intro _ second
      have unitStep := strictRowWithId (presentationRows := presentationRows)
        (StrictAxiomRel.vcompUnitLeft (realizePathCellSig second))
      rw [realizePathCellSig_boundarySource] at unitStep
      exact SaturatedConvOverWithId.symm unitStep
  | cons _ rest ih =>
      intro _ second
      exact SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.vcompCongrRight _ (ih second))
        (SaturatedConvOverWithId.symm
          (strictRowWithId (presentationRows := presentationRows)
            (StrictAxiomRel.vcompAssoc _ (realizePathCellSig rest) (realizePathCellSig second))))

/-- ★ **Boundary coherence (source).**  The translated 2-cell's structural source boundary is convertible to
the realised source path — by induction on the raw 2-cell: `gen` / `id` are `refl`, `vcomp` follows the left
inductive hypothesis, and the whisker cases thread the hypothesis under `vcompCongr{Right,Left}` then apply
the composePath homomorphism. -/
theorem toCellDimTwo_boundarySource_convWithId {signature : ModeSignature}
    {presentationRows : CellRelOver (computadOfSignature signature)}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    SaturatedConvOverWithId (computadOfSignature signature)
      (unionCellRel (computadOfSignature signature) (StrictAxiomRel (computadOfSignature signature))
        presentationRows)
      (boundarySource (toCellDimTwo cell)) (realizePathCellSig sourcePath) := by
  induction cell with
  | gen _ => exact SaturatedConvOverWithId.refl _
  | id _ => exact SaturatedConvOverWithId.refl _
  | vcomp _ _ ihAlpha _ => exact ihAlpha
  | whiskerLeft oneCell _ ihBeta =>
      exact SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.vcompCongrRight (realizePathCellSig oneCell) ihBeta)
        (SaturatedConvOverWithId.symm
          (realizePathCellSig_composePath_convWithId (presentationRows := presentationRows) oneCell _))
  | whiskerRight oneCell _ ihAlpha =>
      exact SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.vcompCongrLeft (realizePathCellSig oneCell) ihAlpha)
        (SaturatedConvOverWithId.symm
          (realizePathCellSig_composePath_convWithId (presentationRows := presentationRows) _ oneCell))

/-- ★ **Boundary coherence (target).**  The dual of `toCellDimTwo_boundarySource_convWithId`: the translated
2-cell's structural target boundary is convertible to the realised target path. -/
theorem toCellDimTwo_boundaryTarget_convWithId {signature : ModeSignature}
    {presentationRows : CellRelOver (computadOfSignature signature)}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    SaturatedConvOverWithId (computadOfSignature signature)
      (unionCellRel (computadOfSignature signature) (StrictAxiomRel (computadOfSignature signature))
        presentationRows)
      (boundaryTarget (toCellDimTwo cell)) (realizePathCellSig targetPath) := by
  induction cell with
  | gen _ => exact SaturatedConvOverWithId.refl _
  | id _ => exact SaturatedConvOverWithId.refl _
  | vcomp _ _ _ ihBeta => exact ihBeta
  | whiskerLeft oneCell _ ihBeta =>
      exact SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.vcompCongrRight (realizePathCellSig oneCell) ihBeta)
        (SaturatedConvOverWithId.symm
          (realizePathCellSig_composePath_convWithId (presentationRows := presentationRows) oneCell _))
  | whiskerRight oneCell _ ihAlpha =>
      exact SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.vcompCongrLeft (realizePathCellSig oneCell) ihAlpha)
        (SaturatedConvOverWithId.symm
          (realizePathCellSig_composePath_convWithId (presentationRows := presentationRows) _ oneCell))

/-! ## The interchange arm — the Godement middle-four exchange derived over the sibling -/

/-- ★ **The generic middle-four rebracket.**  From a middle exchange `(Q . R) ~ (R' . Q')`, associativity
alone rebrackets `(P . Q) . (R . S) ~ (P . R') . (Q' . S)`.  The pure-associativity skeleton of the Godement
interchange, generic in the six factors — five `vcompAssoc` re-associations threading the middle exchange
through the vertical composite. -/
theorem vcompMiddleFourRebracket {computad : OmegaComputad}
    {presentationRows : CellRelOver computad} {dim : Nat}
    (cellP cellQ cellR cellS cellRPrime cellQPrime : CellExpr computad (dim + 1))
    (middle : SaturatedConvOverWithId computad
      (unionCellRel computad (StrictAxiomRel computad) presentationRows)
      (CellExpr.vcomp cellQ cellR) (CellExpr.vcomp cellRPrime cellQPrime)) :
    SaturatedConvOverWithId computad
      (unionCellRel computad (StrictAxiomRel computad) presentationRows)
      (CellExpr.vcomp (CellExpr.vcomp cellP cellQ) (CellExpr.vcomp cellR cellS))
      (CellExpr.vcomp (CellExpr.vcomp cellP cellRPrime) (CellExpr.vcomp cellQPrime cellS)) :=
  SaturatedConvOverWithId.trans
    (strictRowWithId (StrictAxiomRel.vcompAssoc cellP cellQ (CellExpr.vcomp cellR cellS)))
    (SaturatedConvOverWithId.trans
      (SaturatedConvOverWithId.vcompCongrRight cellP
        (SaturatedConvOverWithId.symm (strictRowWithId (StrictAxiomRel.vcompAssoc cellQ cellR cellS))))
      (SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.vcompCongrRight cellP
          (SaturatedConvOverWithId.vcompCongrLeft cellS middle))
        (SaturatedConvOverWithId.trans
          (SaturatedConvOverWithId.vcompCongrRight cellP
            (strictRowWithId (StrictAxiomRel.vcompAssoc cellRPrime cellQPrime cellS)))
          (SaturatedConvOverWithId.symm
            (strictRowWithId
              (StrictAxiomRel.vcompAssoc cellP cellRPrime (CellExpr.vcomp cellQPrime cellS)))))))

/-- ★ **THE INTERCHANGE ARM (the sole hard step).**  `toCellDimTwo` carries the `TwoCellStep.interchange`
Godement-of-vcomps law into a sibling convertibility: the two whisker-functoriality rows split the outer
whiskers, the strict `interchange` row exchanges the middle two whiskerings (bridged onto the realised
whisker cells by the whisker-1-cell congruences and the boundary coherences), and `vcompMiddleFourRebracket`
re-associates.  This is the Godement-from-middle-four derivation the recon budgeted as the single risk. -/
theorem bridgeInterchangeArm {signature : ModeSignature}
    {presentationRows : CellRelOver (computadOfSignature signature)}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {oneCellFLow oneCellFMid oneCellFHigh : ModalityPath signature.graph sourceMode middleMode}
    {oneCellGLow oneCellGMid oneCellGHigh : ModalityPath signature.graph middleMode targetMode}
    (cellAlpha : RawTwoCellExpr signature oneCellFLow oneCellFMid)
    (cellAlphaUpper : RawTwoCellExpr signature oneCellFMid oneCellFHigh)
    (cellBeta : RawTwoCellExpr signature oneCellGLow oneCellGMid)
    (cellBetaUpper : RawTwoCellExpr signature oneCellGMid oneCellGHigh) :
    SaturatedConvOverWithId (computadOfSignature signature)
      (unionCellRel (computadOfSignature signature) (StrictAxiomRel (computadOfSignature signature))
        presentationRows)
      (toCellDimTwo (RawTwoCellExpr.hcomp (RawTwoCellExpr.vcomp cellAlpha cellAlphaUpper)
        (RawTwoCellExpr.vcomp cellBeta cellBetaUpper)))
      (toCellDimTwo (RawTwoCellExpr.vcomp (RawTwoCellExpr.hcomp cellAlpha cellBeta)
        (RawTwoCellExpr.hcomp cellAlphaUpper cellBetaUpper))) := by
  have h1 : SaturatedConvOverWithId (computadOfSignature signature)
      (unionCellRel (computadOfSignature signature) (StrictAxiomRel (computadOfSignature signature))
        presentationRows)
      (realizePathCellSig oneCellGLow) (boundarySource (toCellDimTwo cellBeta)) :=
    SaturatedConvOverWithId.symm
      (toCellDimTwo_boundarySource_convWithId (presentationRows := presentationRows) cellBeta)
  have h2 : SaturatedConvOverWithId (computadOfSignature signature)
      (unionCellRel (computadOfSignature signature) (StrictAxiomRel (computadOfSignature signature))
        presentationRows)
      (realizePathCellSig oneCellFHigh) (boundaryTarget (toCellDimTwo cellAlphaUpper)) :=
    SaturatedConvOverWithId.symm
      (toCellDimTwo_boundaryTarget_convWithId (presentationRows := presentationRows) cellAlphaUpper)
  have h3 : SaturatedConvOverWithId (computadOfSignature signature)
      (unionCellRel (computadOfSignature signature) (StrictAxiomRel (computadOfSignature signature))
        presentationRows)
      (boundarySource (toCellDimTwo cellAlphaUpper)) (realizePathCellSig oneCellFMid) :=
    toCellDimTwo_boundarySource_convWithId (presentationRows := presentationRows) cellAlphaUpper
  have h4 : SaturatedConvOverWithId (computadOfSignature signature)
      (unionCellRel (computadOfSignature signature) (StrictAxiomRel (computadOfSignature signature))
        presentationRows)
      (boundaryTarget (toCellDimTwo cellBeta)) (realizePathCellSig oneCellGMid) :=
    toCellDimTwo_boundaryTarget_convWithId (presentationRows := presentationRows) cellBeta
  -- the middle exchange `(Q . R) ~ (R' . Q')`, bridged onto the realised whisker cells
  have middle : SaturatedConvOverWithId (computadOfSignature signature)
      (unionCellRel (computadOfSignature signature) (StrictAxiomRel (computadOfSignature signature))
        presentationRows)
      (CellExpr.vcomp (CellExpr.whiskerRight (toCellDimTwo cellAlphaUpper) (realizePathCellSig oneCellGLow))
        (CellExpr.whiskerLeft (realizePathCellSig oneCellFHigh) (toCellDimTwo cellBeta)))
      (CellExpr.vcomp (CellExpr.whiskerLeft (realizePathCellSig oneCellFMid) (toCellDimTwo cellBeta))
        (CellExpr.whiskerRight (toCellDimTwo cellAlphaUpper) (realizePathCellSig oneCellGMid))) :=
    SaturatedConvOverWithId.trans
      (SaturatedConvOverWithId.vcompCongrLeft
        (CellExpr.whiskerLeft (realizePathCellSig oneCellFHigh) (toCellDimTwo cellBeta))
        (SaturatedConvOverWithId.whiskerRightWhiskerCongr (toCellDimTwo cellAlphaUpper) h1))
      (SaturatedConvOverWithId.trans
        (SaturatedConvOverWithId.vcompCongrRight
          (CellExpr.whiskerRight (toCellDimTwo cellAlphaUpper) (boundarySource (toCellDimTwo cellBeta)))
          (SaturatedConvOverWithId.whiskerLeftWhiskerCongr (toCellDimTwo cellBeta) h2))
        (SaturatedConvOverWithId.trans
          (strictRowWithId
            (StrictAxiomRel.interchange (toCellDimTwo cellAlphaUpper) (toCellDimTwo cellBeta)))
          (SaturatedConvOverWithId.trans
            (SaturatedConvOverWithId.vcompCongrLeft
              (CellExpr.whiskerRight (toCellDimTwo cellAlphaUpper) (boundaryTarget (toCellDimTwo cellBeta)))
              (SaturatedConvOverWithId.whiskerLeftWhiskerCongr (toCellDimTwo cellBeta) h3))
            (SaturatedConvOverWithId.vcompCongrRight
              (CellExpr.whiskerLeft (realizePathCellSig oneCellFMid) (toCellDimTwo cellBeta))
              (SaturatedConvOverWithId.whiskerRightWhiskerCongr (toCellDimTwo cellAlphaUpper) h4)))))
  -- split the outer whiskers by whisker-functoriality, then rebracket
  have init : SaturatedConvOverWithId (computadOfSignature signature)
      (unionCellRel (computadOfSignature signature) (StrictAxiomRel (computadOfSignature signature))
        presentationRows)
      (CellExpr.vcomp
        (CellExpr.whiskerRight (CellExpr.vcomp (toCellDimTwo cellAlpha) (toCellDimTwo cellAlphaUpper))
          (realizePathCellSig oneCellGLow))
        (CellExpr.whiskerLeft (realizePathCellSig oneCellFHigh)
          (CellExpr.vcomp (toCellDimTwo cellBeta) (toCellDimTwo cellBetaUpper))))
      (CellExpr.vcomp
        (CellExpr.vcomp (CellExpr.whiskerRight (toCellDimTwo cellAlpha) (realizePathCellSig oneCellGLow))
          (CellExpr.whiskerRight (toCellDimTwo cellAlphaUpper) (realizePathCellSig oneCellGLow)))
        (CellExpr.vcomp (CellExpr.whiskerLeft (realizePathCellSig oneCellFHigh) (toCellDimTwo cellBeta))
          (CellExpr.whiskerLeft (realizePathCellSig oneCellFHigh) (toCellDimTwo cellBetaUpper)))) :=
    SaturatedConvOverWithId.trans
      (SaturatedConvOverWithId.vcompCongrLeft
        (CellExpr.whiskerLeft (realizePathCellSig oneCellFHigh)
          (CellExpr.vcomp (toCellDimTwo cellBeta) (toCellDimTwo cellBetaUpper)))
        (strictRowWithId (StrictAxiomRel.whiskerRightFunctorial (toCellDimTwo cellAlpha)
          (toCellDimTwo cellAlphaUpper) (realizePathCellSig oneCellGLow))))
      (SaturatedConvOverWithId.vcompCongrRight
        (CellExpr.vcomp (CellExpr.whiskerRight (toCellDimTwo cellAlpha) (realizePathCellSig oneCellGLow))
          (CellExpr.whiskerRight (toCellDimTwo cellAlphaUpper) (realizePathCellSig oneCellGLow)))
        (strictRowWithId (StrictAxiomRel.whiskerLeftFunctorial (realizePathCellSig oneCellFHigh)
          (toCellDimTwo cellBeta) (toCellDimTwo cellBetaUpper))))
  exact SaturatedConvOverWithId.trans init
    (vcompMiddleFourRebracket
      (CellExpr.whiskerRight (toCellDimTwo cellAlpha) (realizePathCellSig oneCellGLow))
      (CellExpr.whiskerRight (toCellDimTwo cellAlphaUpper) (realizePathCellSig oneCellGLow))
      (CellExpr.whiskerLeft (realizePathCellSig oneCellFHigh) (toCellDimTwo cellBeta))
      (CellExpr.whiskerLeft (realizePathCellSig oneCellFHigh) (toCellDimTwo cellBetaUpper))
      (CellExpr.whiskerLeft (realizePathCellSig oneCellFMid) (toCellDimTwo cellBeta))
      (CellExpr.whiskerRight (toCellDimTwo cellAlphaUpper) (realizePathCellSig oneCellGMid))
      middle)

/-! ## The twelve-arm step induction and the four-arm conv induction -/

/-- ★ **The step arm bundle — every `TwoCellStep` 3-cell carried into the sibling over `toCellDimTwo`.**  By
induction on the step: associativity / whisker-functoriality / interchange-of-vcomps fire the matching
`StrictAxiomRel` row (`bridgeInterchangeArm` for the last), the four one-hole congruences recurse through the
sibling's namesakes, the two `vcompId` units use `vcompId{Left,Right}_bridgedWithId` (boundary coherence
lifted by `idCongr`), and the two `whiskerId` units fire `whisker{Left,Right}Unit` then `idCongr` of the
composePath coherence. -/
theorem toCellDimTwo_step_convWithId {signature : ModeSignature}
    {presentationRows : CellRelOver (computadOfSignature signature)}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath}
    (step : TwoCellStep signature cellAlpha cellBeta) :
    SaturatedConvOverWithId (computadOfSignature signature)
      (unionCellRel (computadOfSignature signature) (StrictAxiomRel (computadOfSignature signature))
        presentationRows)
      (toCellDimTwo cellAlpha) (toCellDimTwo cellBeta) := by
  induction step with
  | vcompIdLeft cellA =>
      exact vcompIdLeft_bridgedWithId (toCellDimTwo cellA)
        (SaturatedConvOverWithId.symm
          (toCellDimTwo_boundarySource_convWithId (presentationRows := presentationRows) cellA))
        (strictRowWithId (StrictAxiomRel.vcompUnitLeft (toCellDimTwo cellA)))
  | vcompIdRight cellA =>
      exact vcompIdRight_bridgedWithId (toCellDimTwo cellA)
        (SaturatedConvOverWithId.symm
          (toCellDimTwo_boundaryTarget_convWithId (presentationRows := presentationRows) cellA))
        (strictRowWithId (StrictAxiomRel.vcompUnitRight (toCellDimTwo cellA)))
  | vcompAssoc cellA cellB cellC =>
      exact strictRowWithId
        (StrictAxiomRel.vcompAssoc (toCellDimTwo cellA) (toCellDimTwo cellB) (toCellDimTwo cellC))
  | whiskerLeftId oneCell path =>
      exact SaturatedConvOverWithId.trans
        (strictRowWithId
          (StrictAxiomRel.whiskerLeftUnit (realizePathCellSig oneCell) (realizePathCellSig path)))
        (SaturatedConvOverWithId.idCongr
          (SaturatedConvOverWithId.symm
            (realizePathCellSig_composePath_convWithId (presentationRows := presentationRows) oneCell path)))
  | whiskerRightId path oneCell =>
      exact SaturatedConvOverWithId.trans
        (strictRowWithId
          (StrictAxiomRel.whiskerRightUnit (realizePathCellSig path) (realizePathCellSig oneCell)))
        (SaturatedConvOverWithId.idCongr
          (SaturatedConvOverWithId.symm
            (realizePathCellSig_composePath_convWithId (presentationRows := presentationRows) path oneCell)))
  | whiskerLeftVcomp oneCell cellB cellC =>
      exact strictRowWithId (StrictAxiomRel.whiskerLeftFunctorial (realizePathCellSig oneCell)
        (toCellDimTwo cellB) (toCellDimTwo cellC))
  | whiskerRightVcomp oneCell cellA cellB =>
      exact strictRowWithId (StrictAxiomRel.whiskerRightFunctorial (toCellDimTwo cellA)
        (toCellDimTwo cellB) (realizePathCellSig oneCell))
  | vcompCongrLeft cellB _ ih =>
      exact SaturatedConvOverWithId.vcompCongrLeft (toCellDimTwo cellB) ih
  | vcompCongrRight cellA _ ih =>
      exact SaturatedConvOverWithId.vcompCongrRight (toCellDimTwo cellA) ih
  | whiskerLeftCongr oneCell _ ih =>
      exact SaturatedConvOverWithId.whiskerLeftCongr (realizePathCellSig oneCell) ih
  | whiskerRightCongr oneCell _ ih =>
      exact SaturatedConvOverWithId.whiskerRightCongr (realizePathCellSig oneCell) ih
  | interchange cellA cellAUpper cellB cellBUpper =>
      exact bridgeInterchangeArm cellA cellAUpper cellB cellBUpper

/-- ★ **The conv leg — `TwoCellConv` carried into the sibling over `toCellDimTwo`.**  By induction on the
convertibility: `ofStep` is the twelve-arm step bundle, and `refl` / `symm` / `trans` map to the sibling's
namesakes.  This is the full `TwoCellConv → SaturatedConvOverWithId` induction the ledger named as the open
leg (ii). -/
theorem toCellDimTwo_conv_convWithId {signature : ModeSignature}
    {presentationRows : CellRelOver (computadOfSignature signature)}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath}
    (conv : TwoCellConv signature cellAlpha cellBeta) :
    SaturatedConvOverWithId (computadOfSignature signature)
      (unionCellRel (computadOfSignature signature) (StrictAxiomRel (computadOfSignature signature))
        presentationRows)
      (toCellDimTwo cellAlpha) (toCellDimTwo cellBeta) := by
  induction conv with
  | ofStep step => exact toCellDimTwo_step_convWithId (presentationRows := presentationRows) step
  | refl _ => exact SaturatedConvOverWithId.refl _
  | symm _ ih => exact SaturatedConvOverWithId.symm ih
  | trans _ _ ihLeft ihRight => exact SaturatedConvOverWithId.trans ihLeft ihRight

/-! ## The inhabitant — `bridgeDimTwoHoldsWithId` proven for every signature -/

/-- ★★ **THE BRIDGE CONV LEG, CLOSED.**  `bridgeDimTwoHoldsWithId` holds for every mode signature: the
translation `toCellDimTwo` preserves size (`toCellDimTwo_size`) AND carries `TwoCellConv` into the idCongr
sibling congruence `freeStrictCongruenceWithId` over the empty presentation
(`toCellDimTwo_conv_convWithId`).  This inhabits the OMEGA-3 r2 statement — leg (ii) of the
`SuspensionWithIdLedger` map-IN family, closed. -/
theorem bridgeDimTwoHoldsWithId_proof (signature : ModeSignature) :
    bridgeDimTwoHoldsWithId signature := by
  refine ⟨@toCellDimTwo signature, fun cell => toCellDimTwo_size cell, ?_⟩
  intro _ _ _ _ _ _ conv
  exact toCellDimTwo_conv_convWithId
    (presentationRows := emptyPresentation (computadOfSignature signature)) conv

/-! ## The round marker -/

/-- ★ **CLOSED — the full bridge conv leg over the sibling.**  `= true` records that
`bridgeDimTwoHoldsWithId` is now INHABITED for every signature (`bridgeDimTwoHoldsWithId_proof`): the whole
`TwoCellConv → SaturatedConvOverWithId` induction is discharged, the interchange arm and all.  The r2 marker
`fxOmega_bridgeDimTwoHoldsWithIdConvLegOpenR2` (round-stamped) is UNTOUCHED as the historical record of the
wall at r2; this is its resolution one round on.  The shipped `bridgeDimTwoHolds` / its
`fxOmega_bridgeDimTwoConvLegOpen` (the OLD 8-constructor relation's wall) stay untouched — this closure is
over the idCongr sibling only. -/
def fxOmega_bridgeDimTwoHoldsWithIdConvLegClosedR4 : Bool := true

end FX1Poly.Polygraph.Omega
