import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingRightPadCongruence
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingSpineActionCongruence
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedMatchingBoundaryDiscipline

/-! # MatchingWhiskerRightCongruence — the right-whisker compositionality of the matching

The MODE3-C assembly: the matching of a RIGHT whisker depends on the whiskered cell only
through its matching.  The pieces, all shipped:

* the right whisker is matching-action-invisible (`processSpine_spine_whiskerRight`) — the
  whiskered run is the CELL'S OWN spine from the padded canonical seed;
* the canonical seed pair is right-pad-simulated (`matchingRightPadSim_initial`) and the
  boundary-disciplined fold carries the simulation through the spine
  (`matchingRightPadSim_processSpine_ofBoundaryDiscipline`, fed by the chain/arity producers
  `spineBoundaryChained_spine` / `spineHasCupCapAtoms_spine`);
* equal base extracts give equal padded extracts (`extractDiagram_ofRightPadSimPair`).

`matchingOf_whiskerRight_congr` is the signature-generic statement (cup/cap generator
premises); `matchingOf_whiskerRight_congruence` is the UNCONDITIONAL field inhabitant at the
walking adjunction — exactly the `whiskerRight` field of `MatchingSaturatedCongruence`. -/

namespace FX1Poly.Polygraph

/-- ★ **The matching of a right whisker depends on the cell only through its matching** —
signature-generic, under the cup/cap generator discipline.  The whiskered runs are the bare
spines from the padded canonical seed (action invisibility), both runs are pad-simulated by
the seed instance folded through the boundary discipline, and the padded extract congruence
closes from the base matching equality. -/
theorem matchingOf_whiskerRight_congr {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {oneCellF oneCellG : ModalityPath signature.graph sourceMode middleMode}
    (oneCell : ModalityPath signature.graph middleMode targetMode)
    {cellAlpha cellAlphaPrime : RawTwoCellExpr signature oneCellF oneCellG}
    (alphaCupCap : CellHasCupCapGenerators cellAlpha)
    (alphaPrimeCupCap : CellHasCupCapGenerators cellAlphaPrime)
    (matchingsEqual : matchingOf cellAlpha = matchingOf cellAlphaPrime) :
    matchingOf (RawTwoCellExpr.whiskerRight oneCell cellAlpha)
      = matchingOf (RawTwoCellExpr.whiskerRight oneCell cellAlphaPrime) := by
  have foldedSimAlpha := matchingRightPadSim_processSpine_ofBoundaryDiscipline
    oneCellF.length oneCell.length (padIdentifiers oneCellF.length oneCell.length)
    cellAlpha.spine (canonicalMatchingSeed oneCellF.length)
    (canonicalMatchingSeed (oneCellF.length + oneCell.length)) oneCellF.length
    cellAlpha.spineBoundaryChained_spine
    (cellAlpha.spineHasCupCapAtoms_spine alphaCupCap)
    (canonicalMatchingSeed_wireCount oneCellF.length)
    (matchingRightPadSim_initial oneCellF.length oneCell.length)
  have foldedSimAlphaPrime := matchingRightPadSim_processSpine_ofBoundaryDiscipline
    oneCellF.length oneCell.length (padIdentifiers oneCellF.length oneCell.length)
    cellAlphaPrime.spine (canonicalMatchingSeed oneCellF.length)
    (canonicalMatchingSeed (oneCellF.length + oneCell.length)) oneCellF.length
    cellAlphaPrime.spineBoundaryChained_spine
    (cellAlphaPrime.spineHasCupCapAtoms_spine alphaPrimeCupCap)
    (canonicalMatchingSeed_wireCount oneCellF.length)
    (matchingRightPadSim_initial oneCellF.length oneCell.length)
  show extractDiagram (composePath oneCellF oneCell).length
      (processSpine (canonicalMatchingSeed (composePath oneCellF oneCell).length)
        (RawTwoCellExpr.whiskerRight oneCell cellAlpha).spine)
    = extractDiagram (composePath oneCellF oneCell).length
      (processSpine (canonicalMatchingSeed (composePath oneCellF oneCell).length)
        (RawTwoCellExpr.whiskerRight oneCell cellAlphaPrime).spine)
  rw [processSpine_spine_whiskerRight oneCell cellAlpha,
    processSpine_spine_whiskerRight oneCell cellAlphaPrime,
    composePath_length oneCellF oneCell]
  exact extractDiagram_ofRightPadSimPair oneCellF.length oneCell.length
    (processSpine (canonicalMatchingSeed oneCellF.length) cellAlpha.spine)
    (processSpine (canonicalMatchingSeed (oneCellF.length + oneCell.length)) cellAlpha.spine)
    (processSpine (canonicalMatchingSeed oneCellF.length) cellAlphaPrime.spine)
    (processSpine (canonicalMatchingSeed (oneCellF.length + oneCell.length))
      cellAlphaPrime.spine)
    foldedSimAlpha foldedSimAlphaPrime matchingsEqual

/-- ★ **The `whiskerRight` field inhabitant at the walking adjunction — UNCONDITIONAL.**
Every cell over the adjunction signature has cup/cap generators
(`cellHasCupCapGenerators_ofAdjunctionSignature`), so the generic congruence applies with no
side conditions — exactly the `whiskerRight` field of `MatchingSaturatedCongruence`. -/
theorem matchingOf_whiskerRight_congruence
    {sourceMode middleMode targetMode : AdjunctionMode}
    {oneCellF oneCellG : ModalityPath adjunctionGraph sourceMode middleMode}
    (oneCell : ModalityPath adjunctionGraph middleMode targetMode)
    {cellAlpha cellAlphaPrime : RawTwoCellExpr adjunctionModeSignature oneCellF oneCellG}
    (matchingsEqual : matchingOf cellAlpha = matchingOf cellAlphaPrime) :
    matchingOf (RawTwoCellExpr.whiskerRight oneCell cellAlpha)
      = matchingOf (RawTwoCellExpr.whiskerRight oneCell cellAlphaPrime) :=
  matchingOf_whiskerRight_congr oneCell
    (cellHasCupCapGenerators_ofAdjunctionSignature cellAlpha)
    (cellHasCupCapGenerators_ofAdjunctionSignature cellAlphaPrime) matchingsEqual

/-! ## Honesty marker -/

/-- **Honesty marker — the right-whisker matching congruence is SHIPPED.**  Both the
signature-generic form (`matchingOf_whiskerRight_congr`, under cup/cap generator premises)
and the UNCONDITIONAL walking-adjunction field inhabitant
(`matchingOf_whiskerRight_congruence`) matching the `whiskerRight` field of
`MatchingSaturatedCongruence` verbatim.  Remaining MODE3-C fields: `whiskerLeft` (positions
shift by the pad — needs a position-shifted pad-sim variant) and `vcompRight` (the MODE3-D
Joyal–Street leg).  `= true`. -/
def fxMode_hasMatchingWhiskerRightCongruence : Bool := true

end FX1Poly.Polygraph
