import FX1Poly.Polygraph.TwoCategory.WalkingString.StringStraightenBandCollapseProducer
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringOrientationExcludedRefutation
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringValleyCommuteProducer
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringValleyCommuteProducerLeft

/-! # WalkingString — the STRAIGHTEN descent-oracle WIRE-UP (FC-3 r7, B4): Piece I reduced to the RIGHT mirror

Every arm of the descent oracle's per-step dispatch is now `StringCellDescentResult`-valued EXCEPT the RIGHT-handed
straighten:

  * `disjointWindows` → `stringCommuteCellDescentStepRight` / `stringCommuteCellDescentStepLeft` (shipped);
  * `zigZagSharedLeg`, LEFT (`|lcCup| + 1 = |lcCap|`) → `stringStraightenCellDescentStep_left` (FC-3 r7, B2);
  * `zigZagSharedLeg`, RIGHT (`|lcCap| + 1 = |lcCup|`) → the MIRROR, un-built (the shipped
    `stringCupCapDeletionReconnects` carries only the LEFT width relation);
  * `orientationExcludedBothLegs` → `stringOrientationExcluded_vacuous` (FC-3 r7, B3, vacuous).

★ **`stringDescentDispatch_ofLocatedPair`** wires ALL of them GIVEN the located pair, taking the RIGHT-handed
straighten as its remaining input: the three-way verdict dispatch (`classifyAdjacentAtoms`, its exhaustive
`deriving DecidableEq` match), the two width `le_total` / `stringZigZagSharedLeg_widthDichotomy` splits, with the
`coh` for the orientation arm read off `cell`'s own realized chain (`framedChain_pairPathCoherence`).  The whole
verdict dispatch is `StringCellDescentResult`-valued, reduced to EXACTLY the RIGHT mirror.

## What this does NOT close (gates stay `false`) — TWO remaining inputs to the full oracle

  (1) The RIGHT-handed mirror straighten producer is un-built (a RIGHT reconnect + the `triangleGlo`/`triangleH`
      RIGHT-snakes; the shipped `stringCupCapDeletionReconnects` carries only the LEFT width relation).
  (2) A DATA-valued locate: a non-valley cell only exposes its adjacent cup·cap pair through the Prop-`∃`
      `hasAdjacentCupThenCap_split`, which `Exists.casesOn` cannot eliminate into the data result
      `StringCellDescentResult`; a structural-recursion locate returning the split as a `Σ'` is needed to feed this
      dispatch and inhabit `StringCellDescentStepOracle` hypothesis-free.

So `StringCellDescentStepOracle` is NOT inhabited hypothesis-free — Piece I is NOT done, and
`fxString_hasAdjointTripleCompleteness` stays `false` (Piece II, the valley trace-equivalence, is also separate and
untouched).  This file assembles the verdict DISPATCH only, honestly.

Raw Lean 4 + Init; the dispatch is a structural `match` on the classifier verdict + `Or` on the width relations.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.  Per-declaration `#assert_no_axioms` gated
in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- The RIGHT-handed straighten producer TYPE — the mirror of `stringStraightenCellDescentStep_left` at the RIGHT
width relation `|lcCap| + 1 = |lcCup|`.  The SINGLE remaining input to the whole per-step oracle. -/
def StringRightStraightenProducer : Type :=
  ∀ {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath)
    (prefixCells rest : List (SpineAtom adjointTripleModeSignature sourceMode targetMode))
    {cupAtom capAtom : SpineAtom adjointTripleModeSignature sourceMode targetMode},
    cupAtom.isCupAtom = true → capAtom.isCupAtom = false →
    cell.spine = prefixCells ++ cupAtom :: capAtom :: rest →
    capAtom.leftContext.length + 1 = cupAtom.leftContext.length →
    StringCellDescentResult cell

/-- ★★★ **THE PER-STEP VERDICT DISPATCH — given a LOCATED pair, modulo the RIGHT mirror.**  Given the located
cup·cap split (as DATA — `prefixCells`, `cupAtom`, `capAtom`, `rest`, `sourceSplit`), classify it and dispatch to the
shipped producer: COMMUTE (either offset), LEFT STRAIGHTEN, the supplied RIGHT-handed straighten, or the
orientation-excluded vacuity.  This is the WHOLE verdict dispatch, `StringCellDescentResult`-valued, reduced to
EXACTLY the RIGHT mirror.  (It takes the located pair as arguments because a non-valley cell only yields the pair
through the Prop-`∃` `hasAdjacentCupThenCap_split`, which cannot be eliminated into this data result — a
data-valued locate is the second remaining input to the full oracle.) -/
def stringDescentDispatch_ofLocatedPair (rightStraighten : StringRightStraightenProducer)
    {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath)
    (prefixCells rest : List (SpineAtom adjointTripleModeSignature sourceMode targetMode))
    {cupAtom capAtom : SpineAtom adjointTripleModeSignature sourceMode targetMode}
    (isCupCup : cupAtom.isCupAtom = true) (isCapCap : capAtom.isCupAtom = false)
    (sourceSplit : cell.spine = prefixCells ++ cupAtom :: capAtom :: rest) :
    StringCellDescentResult cell :=
  match hVerdict : classifyAdjacentAtoms cupAtom capAtom with
  | AdjacentCupCapKind.disjointWindows =>
      if offsetLe : cupAtom.leftContext.length ≤ capAtom.leftContext.length then
        stringCommuteCellDescentStepRight cell prefixCells rest isCupCup isCapCap sourceSplit
          offsetLe hVerdict
      else
        stringCommuteCellDescentStepLeft cell prefixCells rest isCupCup isCapCap sourceSplit
          ((Nat.le_total cupAtom.leftContext.length capAtom.leftContext.length).resolve_left offsetLe)
          hVerdict
  | AdjacentCupCapKind.zigZagSharedLeg =>
      if widthRelLeft : cupAtom.leftContext.length + 1 = capAtom.leftContext.length then
        stringStraightenCellDescentStep_left cell prefixCells rest isCupCup isCapCap sourceSplit
          widthRelLeft
      else
        rightStraighten cell prefixCells rest isCupCup isCapCap sourceSplit
          ((stringZigZagSharedLeg_widthDichotomy cupAtom capAtom hVerdict).resolve_left widthRelLeft)
  | AdjacentCupCapKind.orientationExcludedBothLegs =>
      (stringOrientationExcluded_vacuous cupAtom capAtom isCupCup isCapCap hVerdict
        (framedChain_pairPathCoherence rest prefixCells
          (FramedSpineChain.castAtoms sourceSplit cell.cellChain))).elim

/-! ## Honesty marker -/

/-- **★ ESTABLISHED (partial) — the WHOLE per-step verdict DISPATCH is WIRED, reduced to the RIGHT mirror + a
data-locate (FC-3 r7, B4).**  `stringDescentDispatch_ofLocatedPair` produces `StringCellDescentResult cell` from a
LOCATED cup·cap split: the exhaustive three-verdict dispatch, the COMMUTE both-offset split, the LEFT straighten
(`stringStraightenCellDescentStep_left`, now UNCONDITIONAL), the orientation vacuity
(`stringOrientationExcluded_vacuous`), all assembled — only the RIGHT zigzag arm remains a hypothesis.

  What this marker does NOT close (gates stay `false`): TWO inputs to the full oracle remain — (1) the RIGHT-handed
  mirror straighten (a RIGHT reconnect + the `triangleGlo`/`triangleH` RIGHT-snakes), un-built; (2) a DATA-valued
  locate (the Prop-`∃` `hasAdjacentCupThenCap_split` cannot be eliminated into `StringCellDescentResult`).  So
  `StringCellDescentStepOracle` is NOT inhabited hypothesis-free — Piece I is NOT done.  Piece II
  (`StringCellValleyTraceEquiv`) is separate and untouched.  `fxString_hasAdjointTripleCompleteness` stays `false`.
  `= true`. -/
def fxString_hasStringDescentDispatchModuloRightMirror : Bool := true

end FX1Poly.Polygraph
