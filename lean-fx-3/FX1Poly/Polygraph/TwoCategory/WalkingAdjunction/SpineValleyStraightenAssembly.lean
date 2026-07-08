import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyStraightenSeed
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyStraightenSeedB
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyRedexStep

/-! # mode-3 keystone — Piece I STRAIGHTEN producer: THE ASSEMBLY (both handednesses dispatched)

Every ingredient of the STRAIGHTEN per-step is now shipped:

  * the boundary coherence `coh` — read off `cell`'s OWN realized chain by `framedChain_pairPathCoherence`
    (handedness-agnostic; the same read-off the COMMUTE producer uses);
  * the reconnection `reconnect` — the endpoint identification `cupCapDeletionReconnects`;
  * the concrete band collapse — dispatched by the width dichotomy `zigZagSharedLeg_widthDichotomy` (`A ∨ B`) into
    `zigZagBandCollapseA` (LEFT snake) or `zigZagBandCollapseB` (RIGHT snake);
  * the readback realization `stepConv` — `straightenStepConv`, fed that collapse;
  * the deleted `next` cell and its spine — `straightenNextCell` / `straightenNextCell_spine`;
  * the `CellDescentResult` package — `cellDescentResult_ofStraightenStep`, whose `disorderDrops` is the deletion
    strict-decrease.

★ **This file assembles them into `straightenCellDescentStep`** — a TOTAL closed function producing a
`CellDescentResult cell` for any located `zigZagSharedLeg` redex, with NO `CellStraightenStepInput` input and NO
`matchingOf` / `partnerIndexOf` / arc read.  The width dichotomy chooses the handedness; both arms are shipped, so
the STRAIGHTEN move is now discharged unconditionally.

## What this closes / does NOT close

This DISCHARGES the STRAIGHTEN residual: `straightenCellDescentStep` is exactly the body the oracle's
`.zigZagSharedLeg` arm needs, with no open input.  It does NOT by itself close `MatchingReductsShareSpineTrace` —
after the swap (`SpineValleyOracleDispatch`), that reduces to `CellValleyTraceEquiv` (Piece II) ALONE.  No gate flag
flips here; `convOfMapEq` and the fib-3 gate flags stay `false` until Piece II lands too.

Raw Lean 4 + Init; pure plumbing over shipped lemmas.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/
`omega`-free; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★★ **THE STRAIGHTEN ASSEMBLY.**  A total closed per-step move for a located `zigZagSharedLeg` redex: read the
boundary coherence off `cell`'s own realized chain, reconnect the chain, dispatch the band collapse by the width
dichotomy (LEFT snake `zigZagBandCollapseA` or RIGHT snake `zigZagBandCollapseB`), realize the readback `stepConv`,
build the deleted `next`, and package the `CellDescentResult`.  No `CellStraightenStepInput` input, no `matchingOf`
read — partner-hood is READ OFF the local seed-rigidity geometry. -/
def straightenCellDescentStep {sourceMode targetMode : AdjunctionMode}
    {sourcePath targetPath : ModalityPath adjunctionGraph sourceMode targetMode}
    (cell : RawTwoCellExpr adjunctionModeSignature sourcePath targetPath)
    (prefixCells rest : List (SpineAtom adjunctionModeSignature sourceMode targetMode))
    {cupAtom capAtom : SpineAtom adjunctionModeSignature sourceMode targetMode}
    (isCupCup : cupAtom.isCupAtom = true) (isCapCap : capAtom.isCupAtom = false)
    (sourceSplit : cell.spine = prefixCells ++ cupAtom :: capAtom :: rest)
    (verdict : classifyAdjacentAtoms cupAtom capAtom = AdjacentCupCapKind.zigZagSharedLeg) :
    CellDescentResult cell :=
  let coh : atomFrameTarget cupAtom = atomFrameSource capAtom :=
    framedChain_pairPathCoherence rest prefixCells
      (FramedSpineChain.castAtoms sourceSplit cell.cellChain)
  let reconnect : atomFrameSource cupAtom = atomFrameTarget capAtom :=
    cupCapDeletionReconnects cupAtom capAtom isCupCup isCapCap coh
  let collapse :
      SaturatedTwoCellConv
        (RawTwoCellExpr.vcomp (readbackBand cupAtom)
          (RawTwoCellExpr.castBoundary coh.symm reconnect.symm (readbackBand capAtom)))
        (RawTwoCellExpr.id (signature := adjunctionModeSignature) (atomFrameSource cupAtom)) :=
    match zigZagSharedLeg_widthDichotomy cupAtom capAtom verdict with
    | Or.inl widthA => zigZagBandCollapseA cupAtom capAtom isCupCup isCapCap coh reconnect widthA
    | Or.inr widthB => zigZagBandCollapseB cupAtom capAtom isCupCup isCapCap coh reconnect widthB
  let stepConv := straightenStepConv cell prefixCells rest reconnect coh collapse sourceSplit
  let targetSplit := straightenNextCell_spine cell prefixCells rest reconnect sourceSplit
  cellDescentResult_ofStraightenStep stepConv prefixCells rest isCupCup isCapCap sourceSplit targetSplit

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the STRAIGHTEN per-step move is DISCHARGED unconditionally.**  `straightenCellDescentStep` is
a total closed function producing a `CellDescentResult cell` for any located `zigZagSharedLeg` redex, dispatching the
band collapse by the width dichotomy across the shipped `zigZagBandCollapseA` (LEFT) / `zigZagBandCollapseB` (RIGHT)
arms — no `CellStraightenStepInput` input, no `matchingOf` / arc read.  It is exactly the body the oracle's
`.zigZagSharedLeg` arm consumes; the swap in `SpineValleyOracleDispatch` retires `CellStraightenStepInput`.

  What this marker does NOT close (gate stays `false`): `MatchingReductsShareSpineTrace` still owes
  `CellValleyTraceEquiv` (Piece II).  `convOfMapEq` and the fib-3 gate flags stay `false`.  `= true`. -/
def fxMode_hasSpineValleyStraightenAssembly : Bool := true

end FX1Poly.Polygraph
