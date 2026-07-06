import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicSwap
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicSwapGeneration
import FX1Poly.Polygraph.Computad.AdjunctionSeed

/-! # WalkingAdjunction/ArcCupDropAndAppend — back-append congruence for trace equivalence (#2184)

Structural prerequisites for the pure-cup completeness proof.  This file ships the
back-append congruence of the trace equivalence: appending a FIXED trailing atom to both
sides of a `SpineTraceEquiv` keeps the two spines trace-equivalent.  The swap generator is
LOCAL (an adjacent transposition with an explicit inert middle zone), so a trailing atom is
untouched by every step — it just extends the `rest` tail of each swap — and the closure
operators (`refl` / `symm` / `trans` / `consCongr`) propagate the appended tail arm for arm.

The proof routes through the ATOM granularity (`spineTraceEquiv_iff_atomicTraceEquiv`): the
block-level Godement swap is harder to back-append directly, but the atomic swap's `rest`
tail absorbs the trailing atom definitionally (`(a :: b :: rest) ++ [tailAtom]` reduces to
`a :: b :: (rest ++ [tailAtom])`), so the `ofSwap` case is a single re-application of the
`swap` constructor at the extended tail.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **Back-append congruence for the ATOMIC trace equivalence.**  Appending a fixed trailing
atom to both sides of an `AtomicTraceEquiv` preserves it.  Each adjacent swap's trailing tail
`rest` absorbs the appended atom (the cons-append reduces definitionally), so the `ofSwap` case
re-applies the `swap` constructor at `rest ++ [tailAtom]`; `refl` / `symm` / `trans` /
`consCongr` thread the appended tail congruence arm for arm. -/
theorem atomicTraceEquiv_backAppendCongr {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode}
    {firstList secondList : List (SpineAtom signature overallSource overallTarget)}
    (atomicEquiv : AtomicTraceEquiv signature firstList secondList)
    (tailAtom : SpineAtom signature overallSource overallTarget) :
    AtomicTraceEquiv signature (firstList ++ [tailAtom]) (secondList ++ [tailAtom]) := by
  induction atomicEquiv with
  | ofSwap swapStep =>
      cases swapStep with
      | @swap swapSourceMode swapMiddleLeft swapMiddleRight swapTargetMode oneCellFMid
          oneCellFHigh oneCellGLow oneCellGMid generatorLeft generatorRight leftAcc inertPath
          rightAcc rest =>
          exact AtomicTraceEquiv.ofSwap
            (SpineAtomSwap.swap generatorLeft generatorRight leftAcc inertPath rightAcc
              (rest ++ [tailAtom]))
  | refl spineList => exact AtomicTraceEquiv.refl (spineList ++ [tailAtom])
  | symm _ innerHypothesis => exact AtomicTraceEquiv.symm innerHypothesis
  | trans _ _ leftHypothesis rightHypothesis => exact leftHypothesis.trans rightHypothesis
  | consCongr atom _ innerHypothesis => exact AtomicTraceEquiv.consCongr atom innerHypothesis

/-- ★ **Back-append congruence for the block-level trace equivalence.**  Appending a fixed
trailing atom to both sides of a `SpineTraceEquiv` preserves it.  Routed through the atom
granularity: the block equivalence maps into the atomic closure
(`spineTraceEquiv_iff_atomicTraceEquiv`), the atomic back-append absorbs the trailing atom
(`atomicTraceEquiv_backAppendCongr`), and the result maps back to the block level. -/
theorem spineTraceEquiv_backAppendCongr
    {overallSource overallTarget : adjunctionGraph.Mode}
    {firstList secondList :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget)}
    (equiv : SpineTraceEquiv adjunctionModeSignature firstList secondList)
    (tailAtom : SpineAtom adjunctionModeSignature overallSource overallTarget) :
    SpineTraceEquiv adjunctionModeSignature (firstList ++ [tailAtom]) (secondList ++ [tailAtom]) :=
  spineTraceEquiv_iff_atomicTraceEquiv.mpr
    (atomicTraceEquiv_backAppendCongr
      (spineTraceEquiv_iff_atomicTraceEquiv.mp equiv) tailAtom)

/-! ## Honesty marker -/

/-- **Honesty marker — the back-append congruence of the trace equivalence is SHIPPED.**
`atomicTraceEquiv_backAppendCongr` / `spineTraceEquiv_backAppendCongr`: a fixed trailing atom
appended to both sides of a trace equivalence preserves it — the swap generator is local, so
the trailing atom only extends each swap's `rest` tail, and the closure operators propagate.
What this marker does NOT claim: the back-drop arc cancellation `dropLastCup_arc` (the
extract-injectivity linchpin), which is a separate structural obligation. -/
def fxMode_hasArcCupBackAppendCongr : Bool := true

end FX1Poly.Polygraph
