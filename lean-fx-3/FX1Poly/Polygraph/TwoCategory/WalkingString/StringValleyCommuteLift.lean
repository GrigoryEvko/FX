import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMatchingValleyDescent
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyCommuteLift
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyRedexStep

/-! # WalkingString — Piece I COMMUTE lift: the flat located swap IS the whole string step (FC-3 r6, B2)

The walking-adjunction COMMUTE apparatus (`SpineValleyCommuteLift`, `SpineValleyRedexStep`) reduced the oracle's
COMMUTE branch to the cheapest possible residual: because the descent is valued in the SATURATED relation and
`ofSpineTraceEquiv` lifts ANY spine trace equivalence unconditionally, the FLAT boundary-length `SpineAtomSwap`
suffices for the whole `stepConv` — no boundary-PATH Godement band-refactor.  This file ports that lift to
`StringSaturatedTwoCellConv`, and the two disorder-drop `CellDescentResult` builders, over the three-generator
seed's `StringCellDescentResult` carrier:

  * ★ **`stringCommutePrefixSwapCellLift`** — two string cells sharing an atom prefix whose remaining spines are
    related by a flat `SpineAtomSwap` are `StringSaturatedTwoCellConv`: the swap is a Godement spine step
    (`SpineAtomSwap.toGodementStep`), hence one trace equivalence (`SpineTraceEquiv.ofStep`), prefixed by the
    shared atoms (the `{signature}`-GENERIC `spineTraceEquiv_prependAtoms`), and lifted into the saturated
    string relation (`StringSaturatedTwoCellConv.ofSpineTraceEquiv`).  The three-generator analog of
    `commutePrefixSwapCellLift`.
  * ★ **`stringCellDescentResult_ofCommuteStep`** — package a `StringCellDescentResult cell` from a `next` cell
    saturated-convertible to `cell` whose spine transposes the located cup·cap pair to a slot-preserving cap·cup;
    `disorderDrops` is discharged by the `{signature}`-GENERIC `spineDisorder_swap_lt`.
  * ★ **`stringCellDescentResult_ofCommutePrefixSwap`** — the RIGHT-of COMMUTE builder from the FLAT swap: lift the
    swap by `stringCommutePrefixSwapCellLift`, then package via `stringCellDescentResult_ofCommuteStep`.
  * ★ **`stringCellDescentResult_ofCommutePrefixSwapLeft`** — the LEFT-of builder from the REVERSED flat swap
    (moved pair as source): lift `next ≈ cell`, take `.symm`, then package.

## What this does NOT close (gates stay `false`)

This is the CHEAP COMMUTE `stepConv` layer — it consumes a `next` and a flat `SpineAtomSwap`.  The producers that
DERIVE those (the disjoint-window word factorization + the transposed `next`) are the two commute producers over
this file; the STRAIGHTEN arm and the whole oracle wire-up are separate.  So `StringCellDescentStepOracle` stays
UN-inhabited and `fxString_hasAdjointTripleCompleteness` stays `false`.

Raw Lean 4 + Init; the lift is `ofSpineTraceEquiv ∘ prepend ∘ ofStep ∘ toGodementStep`, the builders thread the
generic spine drop through the split equations.  `propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/
`omega`-free; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The flat located swap is the whole COMMUTE conversion -/

/-- ★ **The prefixed spine swap lifts to a string cell conversion.**  Two string cells sharing an atom prefix whose
remaining spines are related by a flat `SpineAtomSwap` are `StringSaturatedTwoCellConv`: the swap is a Godement
spine step (`SpineAtomSwap.toGodementStep`), a single trace equivalence (`SpineTraceEquiv.ofStep`), prefixed by the
shared atoms (`spineTraceEquiv_prependAtoms`) and lifted into the saturated string relation
(`StringSaturatedTwoCellConv.ofSpineTraceEquiv`).  Built from the FLAT boundary-length swap ALONE — no
boundary-path Godement conversion.  The three-generator twin of `commutePrefixSwapCellLift`. -/
theorem stringCommutePrefixSwapCellLift {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    (cellFirst cellSecond : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath)
    (prefixCells : List (SpineAtom adjointTripleModeSignature sourceMode targetMode))
    {pairFirst pairSecond : List (SpineAtom adjointTripleModeSignature sourceMode targetMode)}
    (firstSpine : cellFirst.spine = prefixCells ++ pairFirst)
    (secondSpine : cellSecond.spine = prefixCells ++ pairSecond)
    (swapStep : SpineAtomSwap adjointTripleModeSignature pairFirst pairSecond) :
    StringSaturatedTwoCellConv cellFirst cellSecond :=
  StringSaturatedTwoCellConv.ofSpineTraceEquiv cellFirst cellSecond
    (by
      rw [firstSpine, secondSpine]
      exact spineTraceEquiv_prependAtoms
        (SpineTraceEquiv.ofStep swapStep.toGodementStep) prefixCells)

/-! ## The disorder-drop `StringCellDescentResult` builders -/

/-- ★ **The COMMUTE `StringCellDescentResult` builder.**  Given a `next` cell saturated-convertible to `cell` whose
spine is `cell`'s with the located cup·cap pair transposed to a slot-preserving cap·cup (the two moved atoms keep
their tags), package a `StringCellDescentResult cell`: `disorderDrops` is discharged by the `{signature}`-GENERIC
`spineDisorder_swap_lt`.  The three-generator twin of `cellDescentResult_ofCommuteStep`. -/
def stringCellDescentResult_ofCommuteStep {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    {cell next : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath}
    (stepConv : StringSaturatedTwoCellConv cell next)
    (prefixCells rest : List (SpineAtom adjointTripleModeSignature sourceMode targetMode))
    {cupAtom capAtom capMoved cupMoved : SpineAtom adjointTripleModeSignature sourceMode targetMode}
    (isCupCup : cupAtom.isCupAtom = true) (isCapCap : capAtom.isCupAtom = false)
    (isCapMoved : capMoved.isCupAtom = false) (isCupMoved : cupMoved.isCupAtom = true)
    (sourceSplit : cell.spine = prefixCells ++ cupAtom :: capAtom :: rest)
    (targetSplit : next.spine = prefixCells ++ capMoved :: cupMoved :: rest) :
    StringCellDescentResult cell :=
  ⟨next, stepConv, by
    rw [sourceSplit, targetSplit]
    exact spineDisorder_swap_lt prefixCells isCupCup isCapCap isCapMoved isCupMoved rest⟩

/-- ★ **The RIGHT-of COMMUTE `StringCellDescentResult` builder from the FLAT located swap.**  Given a `next` cell
whose spine transposes the located pair and the flat located `SpineAtomSwap (cupAtom :: capAtom :: rest)
(capMoved :: cupMoved :: rest)`, package a `StringCellDescentResult cell`: `stepConv` by
`stringCommutePrefixSwapCellLift`, `disorderDrops` by `stringCellDescentResult_ofCommuteStep`. -/
def stringCellDescentResult_ofCommutePrefixSwap {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    {cell next : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath}
    (prefixCells rest : List (SpineAtom adjointTripleModeSignature sourceMode targetMode))
    {cupAtom capAtom capMoved cupMoved : SpineAtom adjointTripleModeSignature sourceMode targetMode}
    (isCupCup : cupAtom.isCupAtom = true) (isCapCap : capAtom.isCupAtom = false)
    (isCapMoved : capMoved.isCupAtom = false) (isCupMoved : cupMoved.isCupAtom = true)
    (sourceSplit : cell.spine = prefixCells ++ cupAtom :: capAtom :: rest)
    (targetSplit : next.spine = prefixCells ++ capMoved :: cupMoved :: rest)
    (swapStep : SpineAtomSwap adjointTripleModeSignature
      (cupAtom :: capAtom :: rest) (capMoved :: cupMoved :: rest)) :
    StringCellDescentResult cell :=
  stringCellDescentResult_ofCommuteStep
    (stringCommutePrefixSwapCellLift cell next prefixCells sourceSplit targetSplit swapStep)
    prefixCells rest isCupCup isCapCap isCapMoved isCupMoved sourceSplit targetSplit

/-- ★ **The LEFT-of COMMUTE `StringCellDescentResult` builder from the REVERSED flat swap.**  The left-of analogue:
given the REVERSED flat located `SpineAtomSwap (capMoved :: cupMoved :: rest) (cupAtom :: capAtom :: rest)` (moved
pair as source), lift it to `StringSaturatedTwoCellConv next cell` (`stringCommutePrefixSwapCellLift` on the
moved→original swap), flip by `.symm`, then package via `stringCellDescentResult_ofCommuteStep`. -/
def stringCellDescentResult_ofCommutePrefixSwapLeft {sourceMode targetMode : AdjointTripleMode}
    {sourcePath targetPath : ModalityPath adjointTripleGraph sourceMode targetMode}
    {cell next : RawTwoCellExpr adjointTripleModeSignature sourcePath targetPath}
    (prefixCells rest : List (SpineAtom adjointTripleModeSignature sourceMode targetMode))
    {cupAtom capAtom capMoved cupMoved : SpineAtom adjointTripleModeSignature sourceMode targetMode}
    (isCupCup : cupAtom.isCupAtom = true) (isCapCap : capAtom.isCupAtom = false)
    (isCapMoved : capMoved.isCupAtom = false) (isCupMoved : cupMoved.isCupAtom = true)
    (sourceSplit : cell.spine = prefixCells ++ cupAtom :: capAtom :: rest)
    (targetSplit : next.spine = prefixCells ++ capMoved :: cupMoved :: rest)
    (swapStep : SpineAtomSwap adjointTripleModeSignature
      (capMoved :: cupMoved :: rest) (cupAtom :: capAtom :: rest)) :
    StringCellDescentResult cell :=
  stringCellDescentResult_ofCommuteStep
    (StringSaturatedTwoCellConv.symm
      (stringCommutePrefixSwapCellLift next cell prefixCells targetSplit sourceSplit swapStep))
    prefixCells rest isCupCup isCapCap isCapMoved isCupMoved sourceSplit targetSplit

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the COMMUTE `stepConv` is CHEAP at the three-generator seed: the flat located swap is the
whole string conversion.**  Because the string descent is valued in `StringSaturatedTwoCellConv` and
`ofSpineTraceEquiv` lifts any spine trace equivalence unconditionally, the flat boundary-length `SpineAtomSwap`
suffices for the whole `stepConv` (`stringCommutePrefixSwapCellLift`, via the generic
`spineTraceEquiv_prependAtoms`).  The two `StringCellDescentResult` builders
(`stringCellDescentResult_ofCommutePrefixSwap` right, `stringCellDescentResult_ofCommutePrefixSwapLeft` left)
package the COMMUTE step from `next` plus the flat swap, discharging `disorderDrops` by the generic
`spineDisorder_swap_lt`.

  What this marker does NOT close: the producers that DERIVE `next` + the flat swap from the classifier's
  `disjointWindows` verdict (the word factorization), the STRAIGHTEN arm, and the whole oracle wire-up.  So
  `StringCellDescentStepOracle` stays UN-inhabited and `fxString_hasAdjointTripleCompleteness` stays `false`.
  `= true`. -/
def fxString_hasStringValleyCommuteLift : Bool := true

end FX1Poly.Polygraph
