import FX1Poly.Polygraph.TwoCategory.WalkingString.StringRightStraightenProducer
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringAdjacentPairLocate
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMatchingValleyDescent

/-! # WalkingString — PIECE I DONE: the per-step descent oracle is inhabited HYPOTHESIS-FREE (FC-3 r8, B3)

Everything the per-step move oracle needed is now shipped:

  * the DATA-valued locate `locateAdjacentCupCapSplit` (B1) exposes a non-valley cell's adjacent cup·cap pair as
    `Type` data (feeding the dispatch), with the completeness bridge
    `locateAdjacentCupCapSplit_eq_none_isValley`;
  * the per-step verdict DISPATCH `stringDescentDispatch_ofLocatedPair` routes a located pair to COMMUTE / LEFT
    straighten / the RIGHT straighten / the orientation vacuity;
  * the RIGHT-handed straighten producer `stringStraightenCellDescentStep_right` (B2) — the sole input the dispatch
    still took — is now an unconditional term.

So `StringCellDescentStepOracle` is inhabited with NO hypotheses: run the data locate; on `some split` dispatch
(feeding the concrete RIGHT producer); on `none` derive `False` from the completeness bridge (the spine is a valley,
contradicting the oracle's `notValley` hypothesis) via `Bool.noConfusion`.

  * ★★★ **`stringDescentStepOracle : StringCellDescentStepOracle`** — the hypothesis-free inhabitant.  **PIECE I DONE.**
  * ★ **`stringMatchingReductsShareSpineTrace_of_valleyTraceEquiv`** — the monolithic completeness residual
    `StringMatchingReductsShareSpineTrace` now follows from Piece II (`StringCellValleyTraceEquiv`) ALONE: the per-step
    oracle input to `stringMatchingReductsShareSpineTrace_of_oracle_of_valleyTraceEquiv` is discharged by
    `stringDescentStepOracle`.  So the whole adjoint-triple DECISION rests on EXACTLY one named Prop.

## What this does NOT close (the flag stays `false`)

Piece II (`StringCellValleyTraceEquiv` — two valley cells with equal boundary matching have trace-equivalent spines)
is a SEPARATE, colour-aware reconstruction (a valley's generators are boundary-determined, NOT length-determined; the
walking adjoint-triple is not length-rigid, `string_left_ne_coLeft`), still open.  Its completion is the last input to
`fxString_hasAdjointTripleCompleteness`, which therefore STAYS `false`.  Piece I inhabiting the oracle does NOT flip
the completeness gate — it isolates the residual to Piece II alone, honestly.

Raw Lean 4 + Init; the oracle is a total `Option.casesOn` on the data locate, the `none` branch a `Bool.noConfusion`
against the completeness bridge.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The hypothesis-free per-step descent oracle -/

/-- ★★★ **THE PER-STEP DESCENT ORACLE — INHABITED HYPOTHESIS-FREE.  PIECE I DONE.**  For any NON-valley string cell,
produce a `StringCellDescentResult`: run the DATA-valued locate on the cell's spine; on a located split, dispatch to
the shipped per-step verdict machine (feeding the unconditional RIGHT straighten producer
`stringStraightenCellDescentStep_right`); on `none`, the completeness bridge
`locateAdjacentCupCapSplit_eq_none_isValley` says the spine is a valley, contradicting the `notValley` hypothesis via
`Bool.noConfusion`.  No hypothesis remains — the descent-oracle input every downstream driver
(`stringValleyDescentDriverCell`, `stringValleyNFCell`, `stringCellDescentConv`) took is now a concrete term. -/
def stringDescentStepOracle : StringCellDescentStepOracle :=
  fun cell notValley =>
    match hLocate : locateAdjacentCupCapSplit cell.spine with
    | some split =>
        stringDescentDispatch_ofLocatedPair stringStraightenCellDescentStep_right cell
          split.prefixCells split.rest split.isCupCup split.isCapCap split.splitEq
    | none =>
        Bool.noConfusion
          ((locateAdjacentCupCapSplit_eq_none_isValley cell.spine hLocate).symm.trans notValley)

/-! ## The monolithic residual now rests on Piece II ALONE -/

/-- ★ **The monolithic completeness residual reduced to Piece II ALONE.**  With the per-step oracle inhabited
(`stringDescentStepOracle`), `StringMatchingReductsShareSpineTrace` follows from the cell-level Piece-II input
`StringCellValleyTraceEquiv` by itself — the oracle argument of
`stringMatchingReductsShareSpineTrace_of_oracle_of_valleyTraceEquiv` is discharged.  Every other input to
`fxString_hasAdjointTripleCompleteness` was already reduced to this residual, so the whole adjoint-triple DECISION now
rests on EXACTLY one named Prop, `StringCellValleyTraceEquiv`. -/
theorem stringMatchingReductsShareSpineTrace_of_valleyTraceEquiv
    (valleyTraceEquiv : StringCellValleyTraceEquiv) : StringMatchingReductsShareSpineTrace :=
  stringMatchingReductsShareSpineTrace_of_oracle_of_valleyTraceEquiv stringDescentStepOracle valleyTraceEquiv

/-! ## Honesty markers -/

/-- **★★★ ESTABLISHED — PIECE I DONE: the per-step descent oracle is inhabited HYPOTHESIS-FREE (FC-3 r8, B3).**
`stringDescentStepOracle : StringCellDescentStepOracle` produces a `StringCellDescentResult` for every non-valley
string cell with NO remaining hypothesis: the DATA-valued locate (B1) + the verdict dispatch + the unconditional RIGHT
straighten producer (B2) + the completeness bridge assemble the total per-step move.  This closes the descent half of
the adjoint-triple decision: `stringValleyDescentDriverCell` / `stringValleyNFCell` / `stringCellDescentConv` /
`stringValleyNFCell_isValley` all become unconditional at `stringDescentStepOracle`, and
`stringMatchingReductsShareSpineTrace_of_valleyTraceEquiv` reduces the monolithic residual
`StringMatchingReductsShareSpineTrace` to Piece II ALONE.

  What this marker does NOT close (gates stay `false`): Piece II (`StringCellValleyTraceEquiv`, the colour-aware valley
  trace reconstruction) is the SOLE remaining input to the whole decision; it is separate and untouched.  So
  `fxString_hasAdjointTripleCompleteness` STAYS `false` — inhabiting the per-step oracle isolates the residual to Piece
  II, it does NOT flip the completeness gate.  `= true`. -/
def fxString_hasStringCellDescentStepOracle : Bool := true

end FX1Poly.Polygraph
