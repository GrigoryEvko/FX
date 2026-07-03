import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingLeftPadCongruence
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingLeftPadFold
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SaturatedMatchingBoundaryDiscipline

/-! # MatchingWhiskerLeftCongruence — the left-whisker compositionality of the matching

The MODE3-C assembly for the LEFT whisker: the matching of a left whisker depends on the
whiskered cell only through its matching.  Unlike the right whisker there is NO action
invisibility — a left whisker shifts every atom's firing window by the whiskering 1-cell's
length — so the padded run is the whiskered cell's OWN spine, related to the base spine by
the position-shift correspondence.  The pieces, all shipped:

* the left whisker's spine is the `oneCell.length`-position-shifted copy of the bare spine
  (`spine_whiskerLeft_spinePositionShifted`);
* the canonical seed pair is left-pad-simulated (`matchingLeftPadSim_initial`) and the
  two-list fold carries the simulation through the corresponded spine pair
  (`matchingLeftPadSim_processSpine_ofCorrespondence`, fed by the chain/arity producers
  `spineBoundaryChained_spine` / `spineHasCupCapAtoms_spine` on the BASE side);
* equal base extracts give equal padded extracts (`extractDiagram_ofLeftPadSimPair`).

`matchingOf_whiskerLeft_congr` is the signature-generic statement (cup/cap generator
premises); `matchingOf_whiskerLeft_congruence` is the UNCONDITIONAL field inhabitant at the
walking adjunction — exactly the `whiskerLeft` field of `MatchingSaturatedCongruence`. -/

namespace FX1Poly.Polygraph

/-- ★ **The matching of a left whisker depends on the cell only through its matching** —
signature-generic, under the cup/cap generator discipline.  The whiskered runs are the
position-shifted spines from the padded canonical seed, both runs are pad-simulated by the
seed instance folded through the position-shift correspondence under the base side's
boundary discipline, and the padded extract congruence closes from the base matching
equality. -/
theorem matchingOf_whiskerLeft_congr {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    (oneCell : ModalityPath signature.graph sourceMode middleMode)
    {oneCellG oneCellH : ModalityPath signature.graph middleMode targetMode}
    {cellBeta cellBetaPrime : RawTwoCellExpr signature oneCellG oneCellH}
    (betaCupCap : CellHasCupCapGenerators cellBeta)
    (betaPrimeCupCap : CellHasCupCapGenerators cellBetaPrime)
    (matchingsEqual : matchingOf cellBeta = matchingOf cellBetaPrime) :
    matchingOf (RawTwoCellExpr.whiskerLeft oneCell cellBeta)
      = matchingOf (RawTwoCellExpr.whiskerLeft oneCell cellBetaPrime) := by
  have foldedSimBeta := matchingLeftPadSim_processSpine_ofCorrespondence
    oneCell.length (padIdentifiers 0 oneCell.length)
    cellBeta.spine (RawTwoCellExpr.whiskerLeft oneCell cellBeta).spine
    (canonicalMatchingSeed oneCellG.length)
    (canonicalMatchingSeed (oneCell.length + oneCellG.length)) oneCellG.length
    (spine_whiskerLeft_spinePositionShifted oneCell cellBeta)
    cellBeta.spineBoundaryChained_spine
    (cellBeta.spineHasCupCapAtoms_spine betaCupCap)
    (canonicalMatchingSeed_wireCount oneCellG.length)
    (matchingLeftPadSim_initial oneCell.length oneCellG.length)
  have foldedSimBetaPrime := matchingLeftPadSim_processSpine_ofCorrespondence
    oneCell.length (padIdentifiers 0 oneCell.length)
    cellBetaPrime.spine (RawTwoCellExpr.whiskerLeft oneCell cellBetaPrime).spine
    (canonicalMatchingSeed oneCellG.length)
    (canonicalMatchingSeed (oneCell.length + oneCellG.length)) oneCellG.length
    (spine_whiskerLeft_spinePositionShifted oneCell cellBetaPrime)
    cellBetaPrime.spineBoundaryChained_spine
    (cellBetaPrime.spineHasCupCapAtoms_spine betaPrimeCupCap)
    (canonicalMatchingSeed_wireCount oneCellG.length)
    (matchingLeftPadSim_initial oneCell.length oneCellG.length)
  show extractDiagram (composePath oneCell oneCellG).length
      (processSpine (canonicalMatchingSeed (composePath oneCell oneCellG).length)
        (RawTwoCellExpr.whiskerLeft oneCell cellBeta).spine)
    = extractDiagram (composePath oneCell oneCellG).length
      (processSpine (canonicalMatchingSeed (composePath oneCell oneCellG).length)
        (RawTwoCellExpr.whiskerLeft oneCell cellBetaPrime).spine)
  rw [composePath_length oneCell oneCellG]
  exact extractDiagram_ofLeftPadSimPair oneCell.length oneCellG.length
    (processSpine (canonicalMatchingSeed oneCellG.length) cellBeta.spine)
    (processSpine (canonicalMatchingSeed (oneCell.length + oneCellG.length))
      (RawTwoCellExpr.whiskerLeft oneCell cellBeta).spine)
    (processSpine (canonicalMatchingSeed oneCellG.length) cellBetaPrime.spine)
    (processSpine (canonicalMatchingSeed (oneCell.length + oneCellG.length))
      (RawTwoCellExpr.whiskerLeft oneCell cellBetaPrime).spine)
    foldedSimBeta foldedSimBetaPrime matchingsEqual

/-- ★ **The `whiskerLeft` field inhabitant at the walking adjunction — UNCONDITIONAL.**
Every cell over the adjunction signature has cup/cap generators
(`cellHasCupCapGenerators_ofAdjunctionSignature`), so the generic congruence applies with no
side conditions — exactly the `whiskerLeft` field of `MatchingSaturatedCongruence`. -/
theorem matchingOf_whiskerLeft_congruence
    {sourceMode middleMode targetMode : AdjunctionMode}
    (oneCell : ModalityPath adjunctionGraph sourceMode middleMode)
    {oneCellG oneCellH : ModalityPath adjunctionGraph middleMode targetMode}
    {cellBeta cellBetaPrime : RawTwoCellExpr adjunctionModeSignature oneCellG oneCellH}
    (matchingsEqual : matchingOf cellBeta = matchingOf cellBetaPrime) :
    matchingOf (RawTwoCellExpr.whiskerLeft oneCell cellBeta)
      = matchingOf (RawTwoCellExpr.whiskerLeft oneCell cellBetaPrime) :=
  matchingOf_whiskerLeft_congr oneCell
    (cellHasCupCapGenerators_ofAdjunctionSignature cellBeta)
    (cellHasCupCapGenerators_ofAdjunctionSignature cellBetaPrime) matchingsEqual

/-! ## Honesty marker -/

/-- **Honesty marker — the left-whisker matching congruence is SHIPPED.**  Both the
signature-generic form (`matchingOf_whiskerLeft_congr`, under cup/cap generator premises)
and the UNCONDITIONAL walking-adjunction field inhabitant
(`matchingOf_whiskerLeft_congruence`) matching the `whiskerLeft` field of
`MatchingSaturatedCongruence` verbatim.  Three of the four MODE3-C fields are now inhabited
(`vcompLeft`, `whiskerRight`, `whiskerLeft`); the remaining `vcompRight` is the MODE3-D
Joyal–Street leg.  `= true`. -/
def fxMode_hasMatchingWhiskerLeftCongruence : Bool := true

end FX1Poly.Polygraph
