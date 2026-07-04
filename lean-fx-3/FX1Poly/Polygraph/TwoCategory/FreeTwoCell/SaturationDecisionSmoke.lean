import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.TraceNormalFormNonInvariance
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ClassSaturation

/-! # SaturationDecisionSmoke — the saturation decider COMPUTES (FREE-7 smoke)

The Eckmann–Hilton bubble signature that falsified the extraction normal form now
witnesses the corrected decision procedure END TO END, by kernel computation alone:

  * `bubbleTwoCellDecEq` — the missing choice datum (fiberwise generator equality;
    each fiber holds at most one constructor, so the full-enumeration match closes);
  * `bubbleSaturationExhausts` — the BFS on the source trace's ~-class reaches its
    fixpoint within fuel 16, BY `rfl`;
  * `bubbleTraceDecision_acceptsSwappedTraces` — the decider ACCEPTS the one-swap
    pair that broke `normalizeSpine`, BY `rfl`;
  * `bubbleTraceDecision_rejectsShorterTrace` — the decider REJECTS a trace of
    different length, BY `rfl`.

Every step — the swap recognizers, the successor enumeration, the visited-list
membership, the exhaustion gate, the final membership test — reduces inside the
kernel with zero axioms.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- Decidable generator equality for the bubble signature: within any fixed fiber at
most one constructor lives (creation at `nil ⇒ strand`, bubble at `nil ⇒ nil`), so the
full enumeration of type-correct pairs is two reflexive cases. -/
def bubbleTwoCellDecEq {sourceMode targetMode : BubbleMode}
    (sourcePath targetPath : ModalityPath bubbleGraph sourceMode targetMode) :
    DecidableEq (BubbleTwoCell sourcePath targetPath) := fun firstCell secondCell =>
  match firstCell, secondCell with
  | BubbleTwoCell.creation, BubbleTwoCell.creation => Decidable.isTrue rfl
  | BubbleTwoCell.bubble, BubbleTwoCell.bubble => Decidable.isTrue rfl

/-- The saturation of the bubble source trace exhausts its frontier within fuel 16 —
the whole BFS runs inside the kernel. -/
theorem bubbleSaturationExhausts :
    didExhaustFrontier bubbleModeDecEq bubbleModalityDecEq bubbleTwoCellDecEq 16
      [bubbleSourceTrace] [bubbleSourceTrace] = true := rfl

/-- ★ The decider ACCEPTS the Eckmann–Hilton one-swap pair — the very traces whose
normal forms `normalizeSpine` got wrong are decided equivalent by computation. -/
theorem bubbleTraceDecision_acceptsSwappedTraces :
    @Decidable.decide
      (AtomicTraceEquiv bubbleSignature bubbleSourceTrace bubbleTargetTrace)
      (decideAtomicTraceEquivViaSaturation bubbleModeDecEq bubbleModalityDecEq
        bubbleTwoCellDecEq 16 bubbleSourceTrace bubbleTargetTrace
        bubbleSaturationExhausts) = true := rfl

/-- ★ The decider REJECTS a non-equivalent target (trace equivalence preserves
length, and the singleton is shorter). -/
theorem bubbleTraceDecision_rejectsShorterTrace :
    @Decidable.decide
      (AtomicTraceEquiv bubbleSignature bubbleSourceTrace [bubbleCreationAtom])
      (decideAtomicTraceEquivViaSaturation bubbleModeDecEq bubbleModalityDecEq
        bubbleTwoCellDecEq 16 bubbleSourceTrace [bubbleCreationAtom]
        bubbleSaturationExhausts) = false := rfl

end FX1Poly.Polygraph
