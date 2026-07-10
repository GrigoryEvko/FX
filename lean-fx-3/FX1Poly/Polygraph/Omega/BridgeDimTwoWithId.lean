import FX1Poly.Polygraph.Omega.BridgeDimTwo
import FX1Poly.Polygraph.Omega.Steiner.WallHarvestWithId

/-! # Polygraph/Omega/BridgeDimTwoWithId — the n=2 bridge conv leg over the idCongr sibling (OMEGA-3 r2, B3)

★ **The bridge conv-leg statement re-targeted at the sibling.**  The shipped `bridgeDimTwoHolds`
(`BridgeDimTwo.lean`) is the n=2 bridge whose SIZE leg is proven (`bridgeDimTwoForwardSize`) and whose CONV
leg is the named wall (`fxOmega_bridgeDimTwoConvLegOpen`): the `vcompIdLeft` reduction needs an
`id`-congruence the 8-constructor `freeStrictCongruence` lacks.  With the idCongr sibling shipped, that exact
wall step is now dischargeable — `crownJam_dischargedWithId` machine-checks it on the crown carrier via
`vcompIdLeft_bridgedWithId`.

This file ships the ADDITIVE re-targeted statement `bridgeDimTwoHoldsWithId` (the conv leg over
`freeStrictCongruenceWithId`) as a forward-declared proposition, exactly mirroring the shipped
`bridgeDimTwoHolds` but with the sibling as the codomain congruence.  The shipped `bridgeDimTwoHolds` and its
marker `fxOmega_bridgeDimTwoConvLegOpen` are UNTOUCHED (they remain the honest open statement for the OLD
8-constructor relation).

## Honest status (recon §3, executed)

  * The **jam STEP is discharged** over the sibling (`vcompIdLeft_bridgedWithId` +
    `crownJam_dischargedWithId`): from a convertibility `p ~ boundarySource cellA`, `idCongr` supplies
    `id p ~ id (boundarySource cellA)`, `vcompCongrLeft` places it, the unit row absorbs the trailing
    identity.  This is the `TwoCellStep.vcompIdLeft` reduction that walled the old bridge.
  * The **full conv leg `bridgeDimTwoHoldsWithId` stays OPEN**: it needs the whole `TwoCellConv →
    SaturatedConvOverWithId` induction (composite 1-cells in whisker position use the whisker-1-cell
    congruences, and `realizePathCellSig (composePath ..)` is only convertible — not defeq — to the
    `vcomp`), a genuine sizable deliverable deferred to OMEGA-4.  The marker records it honestly.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

open FX1Poly.Polygraph

/-! ## The bridge conv-leg statement over the sibling -/

/-- ★ **STATEMENT: the n=2 bridge over the idCongr sibling.**  There exists a dim-2 translation preserving
size and carrying the free dim-2 convertibility `TwoCellConv` into the idCongr sibling
`freeStrictCongruenceWithId emptyPresentation`.  The re-targeted analog of `bridgeDimTwoHolds`; a
forward-declared proposition (no axiom).  **Status:** the SIZE leg is `toCellDimTwo` (proven,
`bridgeDimTwoForwardSize`); the CONV leg's key wall step is discharged over the sibling
(`crownJam_dischargedWithId`), but the FULL `TwoCellConv → SaturatedConvOverWithId` induction is the open
OMEGA-4 deliverable.  The shipped `bridgeDimTwoHolds` (over the old relation) keeps its name and meaning. -/
def bridgeDimTwoHoldsWithId (signature : ModeSignature) : Prop :=
  ∃ toCell : DimTwoTranslation signature,
    (∀ {sourceMode targetMode : signature.graph.Mode}
        {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
        (cell : RawTwoCellExpr signature sourcePath targetPath),
        cellSize (toCell cell) = cell.size) ∧
    (∀ {sourceMode targetMode : signature.graph.Mode}
        {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
        {cellAlpha cellBeta : RawTwoCellExpr signature sourcePath targetPath},
        TwoCellConv signature cellAlpha cellBeta →
        freeStrictCongruenceWithId (computadOfSignature signature)
          (emptyPresentation (computadOfSignature signature)) (toCell cellAlpha) (toCell cellBeta))

/-! ## OMEGA-3 r2 bridge markers (B3 — strictly factual) -/

/-- ★ **B3 — the vcompIdLeft jam STEP is DISCHARGED over the sibling.**  The exact `TwoCellStep.vcompIdLeft`
reduction that walled the OMEGA-1 bridge conv leg is machine-checked over the sibling on the crown carrier
(`crownJam_dischargedWithId`, via `vcompIdLeft_bridgedWithId`) — `idCongr` lifts the (conv, not defeq)
boundary equality, which the 8-constructor relation could not.  `= true`. -/
def fxOmega_bridgeConvLegJamStepDischargedWithIdR2 : Bool := true

/-- ★ **B3 — the FULL bridge conv leg over the sibling stays OPEN.**  `= true` records the wall is present:
`bridgeDimTwoHoldsWithId`'s conv leg needs the whole `TwoCellConv → SaturatedConvOverWithId` induction
(whisker-1-cell congruences for composite 1-cells in whisker position; `realizePathCellSig (composePath ..)`
only convertible to the `vcomp`), a sizable deliverable deferred to OMEGA-4.  The shipped
`fxOmega_bridgeDimTwoConvLegOpen` (the OLD relation's wall) is UNTOUCHED. -/
def fxOmega_bridgeDimTwoHoldsWithIdConvLegOpenR2 : Bool := true

end FX1Poly.Polygraph.Omega
