import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicSwapGeneration
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineTraceReconstruction
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.TraceCanonicalForm

/-! # TwoCellWordProblemDecision — the FREE 2-cell word problem decided (FREE-7 brick 1)

The chain closes: `TwoCellConvFull` of parallel free 2-cells IS `SpineTraceEquiv` of
their spines (`twoCellConvFull_iff_spineTraceEquiv`, FREE-2/4), which IS
`AtomicTraceEquiv` (`spineTraceEquiv_iff_atomicTraceEquiv`, FREE-5), which the
saturation search decides (`decideAtomicTraceEquiv?`, FREE-6c).  This file transports
the decision up the chain:

  * `twoCellConvFull_iff_atomicTraceEquiv` — the composed characterization;
  * `decideTwoCellConvFullViaSaturation` / `decideTwoCellConvFull?` ★ — the FREE
    2-category word problem decided over ANY mode signature, gated on the computable
    frontier-exhaustion check;
  * `cellCanonicalTrace_isConvInvariant` — convertible cells have THE SAME canonical
    trace (the cell-level normal form).

HONESTY: this is the FREE case — `TwoCellConvFull` is the congruence closure of the
Godement/whisker laws with NO presentation relations, and the decision is fuel-gated.
The general `fxMode_hasDecidableTwoCellEquality` marker (the mode theory WITH its
adjunction relations, ungated) stays `false`; that needs the saturated walking-
adjunction decision plus the class-size fuel bound.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- The composed characterization: free 2-cell conversion IS atomic trace equivalence
of the spines. -/
theorem twoCellConvFull_iff_atomicTraceEquiv {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (cellFirst cellSecond : RawTwoCellExpr signature sourcePath targetPath) :
    TwoCellConvFull signature cellFirst cellSecond
      ↔ AtomicTraceEquiv signature cellFirst.spine cellSecond.spine :=
  (twoCellConvFull_iff_spineTraceEquiv cellFirst cellSecond).trans
    spineTraceEquiv_iff_atomicTraceEquiv

/-- ★ **The gated free-cell decider**: with the spine saturation's frontier exhausted,
`TwoCellConvFull` is decided by the saturation membership test transported through the
characterization. -/
def decideTwoCellConvFullViaSaturation {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    (twoCellDecEq : {sourceMode targetMode : signature.graph.Mode} →
      (sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode) →
      DecidableEq (signature.twoCell sourcePath targetPath))
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (fuel : Nat) (cellFirst cellSecond : RawTwoCellExpr signature sourcePath targetPath)
    (didExhaust : didExhaustFrontier modeDecEq modalityDecEq twoCellDecEq fuel
      [cellFirst.spine] [cellFirst.spine] = true) :
    Decidable (TwoCellConvFull signature cellFirst cellSecond) :=
  match decideAtomicTraceEquivViaSaturation modeDecEq modalityDecEq twoCellDecEq fuel
      cellFirst.spine cellSecond.spine didExhaust with
  | Decidable.isTrue atomicEquiv =>
      Decidable.isTrue
        ((twoCellConvFull_iff_atomicTraceEquiv cellFirst cellSecond).mpr atomicEquiv)
  | Decidable.isFalse atomicRefuted =>
      Decidable.isFalse (fun cellsConv =>
        atomicRefuted
          ((twoCellConvFull_iff_atomicTraceEquiv cellFirst cellSecond).mp cellsConv))

/-- ★ **The honest front door for the FREE word problem**: run the computable
exhaustion gate on the first cell's spine; decide when it passes, stay silent when the
fuel runs short. -/
def decideTwoCellConvFull? {signature : ModeSignature}
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceMode targetMode : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceMode targetMode))
    (twoCellDecEq : {sourceMode targetMode : signature.graph.Mode} →
      (sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode) →
      DecidableEq (signature.twoCell sourcePath targetPath))
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    (fuel : Nat)
    (cellFirst cellSecond : RawTwoCellExpr signature sourcePath targetPath) :
    Option (Decidable (TwoCellConvFull signature cellFirst cellSecond)) :=
  match didExhaustCheck : didExhaustFrontier modeDecEq modalityDecEq twoCellDecEq fuel
      [cellFirst.spine] [cellFirst.spine] with
  | true =>
      some (decideTwoCellConvFullViaSaturation modeDecEq modalityDecEq twoCellDecEq
        fuel cellFirst cellSecond didExhaustCheck)
  | false => none

/-- Convertible cells have THE SAME canonical trace — the cell-level normal form:
conversion transports to trace equivalence, and the canonical representative is
equivalence-invariant by construction. -/
theorem cellCanonicalTrace_isConvInvariant {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    (keying : AtomKeying signature sourceMode targetMode)
    (modeDecEq : DecidableEq signature.graph.Mode)
    (modalityDecEq : (sourceModeInner targetModeInner : signature.graph.Mode) →
      DecidableEq (signature.graph.Modality sourceModeInner targetModeInner))
    (twoCellDecEq : {sourceModeInner targetModeInner : signature.graph.Mode} →
      (sourcePathInner targetPathInner :
        ModalityPath signature.graph sourceModeInner targetModeInner) →
      DecidableEq (signature.twoCell sourcePathInner targetPathInner))
    {sourcePath targetPath : ModalityPath signature.graph sourceMode targetMode}
    {fuelOne fuelTwo : Nat}
    {cellFirst cellSecond : RawTwoCellExpr signature sourcePath targetPath}
    (didExhaustFirst : didExhaustFrontier modeDecEq modalityDecEq twoCellDecEq fuelOne
      [cellFirst.spine] [cellFirst.spine] = true)
    (didExhaustSecond : didExhaustFrontier modeDecEq modalityDecEq twoCellDecEq fuelTwo
      [cellSecond.spine] [cellSecond.spine] = true)
    (cellsConv : TwoCellConvFull signature cellFirst cellSecond) :
    canonicalTraceRepresentative keying modeDecEq modalityDecEq twoCellDecEq fuelOne
        cellFirst.spine
      = canonicalTraceRepresentative keying modeDecEq modalityDecEq twoCellDecEq
        fuelTwo cellSecond.spine :=
  canonicalTraceRepresentative_isEquivInvariant keying modeDecEq modalityDecEq
    twoCellDecEq didExhaustFirst didExhaustSecond
    ((twoCellConvFull_iff_atomicTraceEquiv cellFirst cellSecond).mp cellsConv)

end FX1Poly.Polygraph
