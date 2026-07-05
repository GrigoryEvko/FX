import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupHeadRealizeAssembly
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcBoundaryTracking

/-! # ArcCupHeadWindowAssembly — the cup-head discharge with the two free pins DERIVED

`cupHeadExtractionConclusion_ofLocatedBubbleAndCancel` (the shipped assembly) demanded FOUR pins on
the moved target — `movedDomPin` (dom = 0), `movedCodPin` (cod = 2), `windowPin` (window = head's),
`boundaryPin` (dom-boundary = the running boundary).  Two of those four are not orbit content at
all:

  * `movedCodPin` is FREE from `movedDomPin`: every adjunction spine atom is a cup `(0, 2)` or a
    cap `(2, 0)` (`adjunctionSpineAtom_hasCupOrCapArity`), and `dom = 0` rules out the cap, so
    `cod = 2` follows (the cap branch is closed by `Nat.noConfusion` on `2 = 0`);
  * `boundaryPin` is FREE from the bubble witness + the second spine's chain: transporting the
    witness through `spineBoundaryChained_of_bubblesToFront` keeps the moved list chained at the
    running boundary, and the head of a chained list has its dom-boundary at that boundary
    (`spineBoundaryChained_tail`).

So this brick re-fronts the assembly taking only `movedDomPin` (which the cup bubble producer
`adjunctionCup_bubblesThroughPrefix` already hands back) and `windowPin`.  The residual for the cup
case is now EXACTLY: the located split, the brick-4 bubble witness, `windowPin` (the moved cup lands
at the head's window), and `tailsCancel` — and of those, `windowPin` + `tailsCancel` are the sole
orbit content the refuted unconditional cancel leaves open.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The cup-head discharge, thinned to the orbit's two pins.**  Same conclusion as
`cupHeadExtractionConclusion_ofLocatedBubbleAndCancel`, but the codomain-arity pin and the
dom-boundary pin are DERIVED here (from the arity dichotomy and the bubble-transported chain), so a
caller supplies only `movedDomPin` — free from the cup bubble producer — and `windowPin`, the single
orbit-dependent pin, alongside the located split, the bubble witness, and the cancel. -/
theorem cupHeadExtractionConclusion_ofLocatedBubbleWindowAndCancel
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
    (windowPin : movedTarget.leftContext.length = headAtom.leftContext.length)
    (tailsCancel : arcStructureOfSpineList headAtom.codBoundaryLength tailList
        = arcStructureOfSpineList headAtom.codBoundaryLength (movedPrefixAtoms ++ suffixAtoms)) :
    ∃ matchedRemainder,
      SpineTraceEquiv adjunctionModeSignature secondList (headAtom :: matchedRemainder)
        ∧ SpineBoundaryChained headAtom.codBoundaryLength matchedRemainder
        ∧ arcStructureOfSpineList headAtom.codBoundaryLength tailList
            = arcStructureOfSpineList headAtom.codBoundaryLength matchedRemainder := by
  have movedCodPin : movedTarget.generatorCod.length = 2 := by
    cases adjunctionSpineAtom_hasCupOrCapArity movedTarget with
    | inl cupArity => exact cupArity.2
    | inr capArity => exact Nat.noConfusion (capArity.1.symm.trans movedDomPin)
  have boundaryPin : movedTarget.domBoundaryLength = bottomCount := by
    have bubbledChained : SpineBoundaryChained bottomCount
        (movedTarget :: (movedPrefixAtoms ++ suffixAtoms)) := by
      refine spineBoundaryChained_of_bubblesToFront witness suffixAtoms ?_
      rw [← doesSplitSpine]
      exact secondChained
    exact (spineBoundaryChained_tail bubbledChained).1
  exact cupHeadExtractionConclusion_ofLocatedBubbleAndCancel bottomCount headAtom
    hasCupDomArity hasCupCodArity headFires tailList secondList secondChained
    prefixAtoms suffixAtoms movedPrefixAtoms toucherAtom movedTarget doesSplitSpine witness
    movedDomPin movedCodPin windowPin boundaryPin tailsCancel

/-! ## Honesty marker -/

/-- **Honesty marker — the cup-head discharge is thinned to the orbit's two pins (peel campaign H).**
`cupHeadExtractionConclusion_ofLocatedBubbleWindowAndCancel` derives the codomain-arity pin (arity
dichotomy — `dom = 0` forces cup, closing the cap branch by `Nat.noConfusion`) and the dom-boundary
pin (the bubble-transported chain's head) that the four-pin assembly demanded, so the cup case's
residual is precisely: the located split, the cup bubble producer's witness + `movedDomPin`,
`windowPin`, and `tailsCancel`.  What this marker does NOT claim: `windowPin` (the moved cup lands at
the head's window) nor `tailsCancel` (the tails agree at the target boundary) — the two genuinely
orbit-dependent inputs the refuted unconditional cancel
(`not_arcCupHeadCancellationUnconditional`) leaves open.  `= true`. -/
def fxMode_hasArcCupHeadWindowAssembly : Bool := true

end FX1Poly.Polygraph
