import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineTraceDecision
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicSwap

/-! # ArcThroughHeadArcEqual — the through-head arc equality the cup orbit re-selects against

The cup-head discharge (`cupHeadExtractionConclusion_ofLocatedBubbleAndCancel`) chooses a
`matchedRemainder` — the second spine re-threaded so the located head cup sits in front — and
must exhibit it as arc-equal to `tailList`.  The datum the orbit's re-selection starts from is
the WHOLE-spine (through-the-head) arc equality: `headAtom :: tailList` and `headAtom :: remainder`
share an arc structure at the seed boundary.  This brick assembles exactly that, from two shipped
facts: the caller's whole-spine arc equality against the raw second spine, and trace-invariance of
`arcStructureOf` applied to the located bubble's `AtomicTraceEquiv` (the second spine `~` the head
cup fronting the remainder).

  * ★ `arcStructureThroughHead_ofArcEqualAndAtomicEquiv` — chains the caller's arc equality with the
    trace-invariance of the bubble, landing the through-head arc equality.

What this brick does NOT do — and cannot: CANCEL the head cup from the arc structure.  Prepending a
cup to a spine is NON-injective on the full arc structure (`ArcCupDiagramAgreement` /
`not_arcCupHeadCancellationUnconditional`: two tails with equal composite extracts can carry
different internal counts), so `arcStructureOf (headAtom :: tailList) = arcStructureOf (headAtom ::
remainder)` does NOT give `arcStructureOf tailList = arcStructureOf remainder`.  The through-head
equality is the CONSTRAINT the orbit's tail re-selection must satisfy, not the tails-cancel itself.

Signature-generic over any `ModeSignature`.  Trace-invariance is threaded through the standard
`godementInvariant` hypothesis (the shipped soundness residual), exactly as the gated decision
`decidableSpineTraceEquiv_of` consumes it.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The through-head arc equality.**  Given the caller's whole-spine arc equality
(`headAtom :: tailList` shares an arc structure with the raw second spine at the seed `bottomCount`)
and the located bubble's trace equivalence (the second spine is `AtomicTraceEquiv` to the head cup
fronting the remainder), the head-fronted tail and the head-fronted remainder share an arc structure
at the seed.  The second conjunct routes through `arcStructureOfSpineList_traceInvariant` (soundness,
gated on the standard `godementInvariant`); the whole is one `Eq.trans`. -/
theorem arcStructureThroughHead_ofArcEqualAndAtomicEquiv {signature : ModeSignature}
    {overallSource overallTarget : signature.graph.Mode} (bottomCount : Nat)
    (godementInvariant : ∀ (state : ArcWireState)
        {firstList secondList : List (SpineAtom signature overallSource overallTarget)},
        SpineGodementStep signature firstList secondList →
        extractArcAfterProcessing bottomCount state firstList
          = extractArcAfterProcessing bottomCount state secondList)
    (headAtom : SpineAtom signature overallSource overallTarget)
    (tailList secondList remainder :
      List (SpineAtom signature overallSource overallTarget))
    (arcEqual : arcStructureOfSpineList bottomCount (headAtom :: tailList)
        = arcStructureOfSpineList bottomCount secondList)
    (atomicEquiv : AtomicTraceEquiv signature secondList (headAtom :: remainder)) :
    arcStructureOfSpineList bottomCount (headAtom :: tailList)
      = arcStructureOfSpineList bottomCount (headAtom :: remainder) :=
  arcEqual.trans
    (arcStructureOfSpineList_traceInvariant bottomCount godementInvariant
      atomicEquiv.toSpineTraceEquiv)

/-! ## Honesty marker -/

/-- **Honesty marker — the through-head arc equality the cup orbit re-selects against.**
`arcStructureThroughHead_ofArcEqualAndAtomicEquiv`: the caller's whole-spine arc equality plus the
located bubble's trace equivalence yield that `headAtom :: tailList` and `headAtom :: remainder`
share an arc structure at the seed boundary.  What this marker does NOT claim: the tails-cancel
(`arcStructureOf tailList = arcStructureOf remainder`) — prepending a cup is non-injective on the
arc structure, so the through-head equality is only the CONSTRAINT the orbit's re-selection must
satisfy, not the cancel.  `= true`. -/
def fxMode_hasArcThroughHeadArcEqual : Bool := true

end FX1Poly.Polygraph
