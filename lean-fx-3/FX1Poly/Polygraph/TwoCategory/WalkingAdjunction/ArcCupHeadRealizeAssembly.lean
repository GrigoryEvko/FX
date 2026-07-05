import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcBubbleToFront
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPeelFoundations
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineTraceDecision

/-! # ArcCupHeadRealizeAssembly — the cup-head discharge assembled MODULO the orbit (peel campaign H)

The cup-head extraction obligation's full conclusion assembles from the arity-GENERIC peel
chain — the same identify/realize the cap discharge uses — the moment two cup-specific inputs
are supplied.  Both inputs are exactly the pieces the REFUTED unconditional cancel cannot
provide, so this brick draws the honest boundary: everything downstream of the located bubble
is generic and shipped; the sole residual is the orbit that produces the bubble witness and the
matched cancel.

  * IDENTIFY — `adjunctionSpineAtom_eq_of_readOffs_at_equalBoundaryLengths` reads the moved
    target off the seed rigidity (equal boundary/window lengths and equal cup arities), so the
    bubbled atom IS the head; arity-parameterized, so cup arity `(0, 2)` drops in where the cap
    used `(2, 0)`;
  * REALIZE — `atomicTraceEquiv_of_bubblesToFront` realizes the witnessed bubble as a trace
    equivalence and `spineBoundaryChained_of_bubblesToFront` keeps the remainder chained; both
    are arity-generic over any `BubblesToFront` witness.

The two cup-specific HYPOTHESES this brick consumes — a `BubblesToFront` witness locating the
head cup at the front of the second spine, and the tails-arc-equal cancel — are the orbit's job
(`not_arcCupHeadCancellationUnconditional` refutes deriving the cancel unconditionally; the
head cup's empty generator domain swaps THROUGH the head, so the matched remainder is CHOSEN in
the second spine's trace orbit).  With them, the discharge is one identify + two realizes.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The cup-head extraction discharges, given the located bubble and the cancel.**  For a
cup-arity head firing at the running boundary `bottomCount`, a `BubblesToFront` witness carrying
the located cup to the front of the second spine (with its window and boundary pinned to the
head's, and its arity cup-shaped), plus the tails-arc-equal cancel at the head's target
boundary, assemble the full `SpineArcHeadExtractionChained` conclusion: the head extracts by a
realized trace equivalence, the remainder is chained at the target boundary, and the tails agree
there.  The identify/realize legs are the arity-generic peel chain; the two hypotheses are the
orbit residual the refuted unconditional cancel leaves open. -/
theorem cupHeadExtractionConclusion_ofLocatedBubbleAndCancel
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount : Nat)
    (headAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (hasCupDomArity : headAtom.generatorDom.length = 0)
    (hasCupCodArity : headAtom.generatorCod.length = 2)
    (headFires : headAtom.domBoundaryLength = bottomCount)
    (tailList secondList : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (secondChained : SpineBoundaryChained bottomCount secondList)
    (prefixAtoms suffixAtoms movedPrefixAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (toucherAtom movedTarget :
      SpineAtom adjunctionModeSignature overallSource overallTarget)
    (doesSplitSpine : secondList = prefixAtoms ++ toucherAtom :: suffixAtoms)
    (witness : BubblesToFront toucherAtom prefixAtoms movedTarget movedPrefixAtoms)
    (movedDomPin : movedTarget.generatorDom.length = 0)
    (movedCodPin : movedTarget.generatorCod.length = 2)
    (windowPin : movedTarget.leftContext.length = headAtom.leftContext.length)
    (boundaryPin : movedTarget.domBoundaryLength = bottomCount)
    (tailsCancel : arcStructureOfSpineList headAtom.codBoundaryLength tailList
        = arcStructureOfSpineList headAtom.codBoundaryLength (movedPrefixAtoms ++ suffixAtoms)) :
    ∃ matchedRemainder,
      SpineTraceEquiv adjunctionModeSignature secondList (headAtom :: matchedRemainder)
        ∧ SpineBoundaryChained headAtom.codBoundaryLength matchedRemainder
        ∧ arcStructureOfSpineList headAtom.codBoundaryLength tailList
            = arcStructureOfSpineList headAtom.codBoundaryLength matchedRemainder := by
  have movedIsHead : movedTarget = headAtom :=
    adjunctionSpineAtom_eq_of_readOffs_at_equalBoundaryLengths movedTarget headAtom
      (boundaryPin.trans headFires.symm) windowPin
      (movedDomPin.trans hasCupDomArity.symm) (movedCodPin.trans hasCupCodArity.symm)
  have atomicEquiv : AtomicTraceEquiv adjunctionModeSignature secondList
      (headAtom :: (movedPrefixAtoms ++ suffixAtoms)) := by
    rw [doesSplitSpine, ← movedIsHead]
    exact atomicTraceEquiv_of_bubblesToFront witness suffixAtoms
  have bubbledChained : SpineBoundaryChained bottomCount
      (movedTarget :: (movedPrefixAtoms ++ suffixAtoms)) := by
    refine spineBoundaryChained_of_bubblesToFront witness suffixAtoms ?_
    rw [← doesSplitSpine]
    exact secondChained
  have remainderChained : SpineBoundaryChained headAtom.codBoundaryLength
      (movedPrefixAtoms ++ suffixAtoms) := by
    have rawRemainderChained := (spineBoundaryChained_tail bubbledChained).2
    rw [movedIsHead] at rawRemainderChained
    exact rawRemainderChained
  exact ⟨movedPrefixAtoms ++ suffixAtoms, atomicEquiv.toSpineTraceEquiv, remainderChained,
    tailsCancel⟩

/-! ## Honesty marker -/

/-- **Honesty marker — the cup-head discharge is assembled MODULO the orbit (peel campaign H).**
`cupHeadExtractionConclusion_ofLocatedBubbleAndCancel`: given a `BubblesToFront` witness locating
the head cup at the front of the second spine (window/boundary/arity pinned) and the
tails-arc-equal cancel, the full `SpineArcHeadExtractionChained` conclusion follows by the
arity-generic identify (seed rigidity) + realize (bubble as trace equivalence, remainder chained)
— the exact cap-discharge chain re-typed for cup arity `(0, 2)`.  What this marker does NOT claim:
the two hypotheses themselves — the orbit that produces the bubble witness and the matched cancel
(`not_arcCupHeadCancellationUnconditional` refutes an unconditional cancel).  `= true`. -/
def fxMode_hasArcCupHeadRealizeAssembly : Bool := true

end FX1Poly.Polygraph
