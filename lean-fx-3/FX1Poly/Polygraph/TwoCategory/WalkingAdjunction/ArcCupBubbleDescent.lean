import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupBubbleConsStep

/-! # ArcCupBubbleDescent — the cup bubble producer's front-first recursion

Bricks 1–3 gave the cup descent's per-step machinery: the window dichotomy
(`adjunctionCupPastAtomWindowDichotomy`) and the inductive cons-step
(`adjunctionCupBubbleConsStep`).  This file assembles them into the FULL descent: a cup at the
end of a boundary-chained prefix bubbles all the way to the front.

The recursion is front-first structural induction on the prefix, mirroring the cap descent
(`arcPairSeated_bubblesThroughPrefix`) but WINDOW-ONLY — there is no seated pair to carry, since
the cup's invariant is just "still a cup" (`movedCup.generatorDom.length = 0`), and its base
parity is automatic (`adjunctionCupAtom_windowPositionMode`).  The one threading crux is the
cons-step's `boundariesChain` premise (`movedCup.domBoundaryLength = passedAtom.codBoundaryLength`):
it is recovered from the ORIGINAL boundary chain by transporting the inner bubble through
`spineBoundaryChained_of_bubblesToFront` and reading off the head boundary with
`spineBoundaryChained_tail`.

This discharges the whole cup bubble PRODUCER.  The only residual of the cup-head extraction is
now the CANCEL (the orbit: the peeled remainder matching the tail's arc structure).

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The cup bubble producer.**  A cup (`cupIsCup`) at the end of any boundary-chained prefix
`prefixAtoms ++ cup :: suffixAtoms` bubbles to the front: there is a `BubblesToFront` witness
carrying it past every prefix atom, and its moved image is still a cup.  Front-first structural
induction on the prefix: the nil case is `BubblesToFront.nil`; the cons case peels the head with
`spineBoundaryChained_tail`, recurses on the tail at the head's codomain boundary, then extends by
one atom with `adjunctionCupBubbleConsStep` — the cons-step's boundary premise recovered by
transporting the inner bubble through `spineBoundaryChained_of_bubblesToFront`. -/
theorem adjunctionCup_bubblesThroughPrefix
    {overallSource overallTarget : adjunctionGraph.Mode}
    (cup : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (cupIsCup : cup.generatorDom.length = 0)
    (prefixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) :
    ∀ (suffixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
      (runningBoundary : Nat),
      SpineBoundaryChained runningBoundary (prefixAtoms ++ cup :: suffixAtoms) →
      ∃ (movedCup : SpineAtom adjunctionModeSignature overallSource overallTarget)
        (movedRest : List (SpineAtom adjunctionModeSignature overallSource overallTarget)),
        BubblesToFront cup prefixAtoms movedCup movedRest
          ∧ movedCup.generatorDom.length = 0 := by
  induction prefixAtoms with
  | nil =>
      intro suffixAtoms runningBoundary _chained
      exact ⟨cup, [], BubblesToFront.nil, cupIsCup⟩
  | cons passedAtom restPrefix inductionHypothesis =>
      intro suffixAtoms runningBoundary chained
      obtain ⟨_headFires, tailChained⟩ := spineBoundaryChained_tail chained
      obtain ⟨movedCup, movedRest, restWitness, movedIsCup⟩ :=
        inductionHypothesis suffixAtoms passedAtom.codBoundaryLength tailChained
      have bubbledChained :=
        spineBoundaryChained_of_bubblesToFront restWitness suffixAtoms tailChained
      exact adjunctionCupBubbleConsStep cup passedAtom restWitness movedIsCup
        (spineBoundaryChained_tail bubbledChained).1

/-! ## Honesty marker -/

/-- **Honesty marker — the cup bubble producer is SHIPPED.**  `adjunctionCup_bubblesThroughPrefix`
carries a cup at the end of a boundary-chained prefix all the way to the front, moved image still
a cup — the full front-first descent, assembled from the window dichotomy (bricks 1–2) and the
cons-step (brick 3), threading the boundary chain through `spineBoundaryChained_of_bubblesToFront`.
What this marker does NOT claim: the CANCEL (the residual orbit — the peeled remainder matching the
tail's arc structure, where the refuted unconditional cancel lives) nor the cup-head extraction it
feeds (`cupHeadExtractionConclusion_ofLocatedBubbleAndCancel`).  `= true`. -/
def fxMode_hasArcCupBubbleDescent : Bool := true

end FX1Poly.Polygraph
