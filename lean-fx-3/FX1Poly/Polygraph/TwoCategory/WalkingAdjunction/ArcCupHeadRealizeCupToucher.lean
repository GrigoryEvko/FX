import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupHeadRealizeAssembly
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupBubbleArity

/-! # ArcCupHeadRealizeCupToucher — the cup-head discharge with the arity/boundary pins DISCHARGED (peel campaign H, cup seat-tracking rung 1)

`cupHeadExtractionConclusion_ofLocatedBubbleAndCancel` (the arity-generic assembly) takes SIX
cup-specific pins: the two moved arities (`movedDomPin`/`movedCodPin`), the moved window pin, the
moved boundary pin, and the tails cancel.  Three of those six are NOT part of the orbit search —
they follow mechanically from the located toucher being a cup and from the bubble preserving the
running boundary:

  * `movedDomPin` / `movedCodPin` — the bubble carries the toucher's generator arities unchanged
    (`bubblesToFront_movedDomArity` / `bubblesToFront_movedCodArity`), so a cup toucher
    (`generatorDom.length = 0`, `generatorCod.length = 2`) bubbles to a moved atom that is still a
    cup;
  * `boundaryPin` — the bubbled list is boundary-chained at the running boundary
    (`spineBoundaryChained_of_bubblesToFront`), and a chained list's head fires at that boundary
    (`spineBoundaryChained_tail`), so `movedTarget.domBoundaryLength = bottomCount` is derived, not
    assumed.

  * ★ `cupHeadExtractionConclusion_ofLocatedCupBubble` — re-presents the discharge consuming only
    the located CUP toucher (its two arities), the bubble witness, the window pin, and the tails
    cancel; it derives the three mechanical pins internally and forwards to the arity-generic
    assembly.

This draws the residual sharp: after this brick the orbit owes exactly the WINDOW pin
(`movedTarget.leftContext.length = headAtom.leftContext.length`, the history-dependent seat the
search must land) and the TAILS cancel (the leg-de-merge) — the arity and boundary pins are off the
table.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The cup-head extraction discharges from a located CUP toucher, the window pin, and the
cancel.**  Same conclusion as `cupHeadExtractionConclusion_ofLocatedBubbleAndCancel`, but the two
moved-arity pins and the moved-boundary pin are DERIVED here rather than assumed: the moved arities
come from the bubble preserving the cup toucher's generator source/target lengths, and the moved
boundary comes from the bubbled list being chained at the running boundary.  What remains genuinely
the orbit's to supply is the window pin and the tails cancel. -/
theorem cupHeadExtractionConclusion_ofLocatedCupBubble
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
    (toucherHasCupDomArity : toucherAtom.generatorDom.length = 0)
    (toucherHasCupCodArity : toucherAtom.generatorCod.length = 2)
    (windowPin : movedTarget.leftContext.length = headAtom.leftContext.length)
    (tailsCancel : arcStructureOfSpineList headAtom.codBoundaryLength tailList
        = arcStructureOfSpineList headAtom.codBoundaryLength (movedPrefixAtoms ++ suffixAtoms)) :
    ∃ matchedRemainder,
      SpineTraceEquiv adjunctionModeSignature secondList (headAtom :: matchedRemainder)
        ∧ SpineBoundaryChained headAtom.codBoundaryLength matchedRemainder
        ∧ arcStructureOfSpineList headAtom.codBoundaryLength tailList
            = arcStructureOfSpineList headAtom.codBoundaryLength matchedRemainder := by
  have bubbledChained : SpineBoundaryChained bottomCount
      (movedTarget :: (movedPrefixAtoms ++ suffixAtoms)) := by
    refine spineBoundaryChained_of_bubblesToFront witness suffixAtoms ?_
    rw [← doesSplitSpine]
    exact secondChained
  exact cupHeadExtractionConclusion_ofLocatedBubbleAndCancel bottomCount headAtom
    hasCupDomArity hasCupCodArity headFires tailList secondList secondChained
    prefixAtoms suffixAtoms movedPrefixAtoms toucherAtom movedTarget doesSplitSpine witness
    (bubblesToFront_movedDomArity witness toucherHasCupDomArity)
    (bubblesToFront_movedCodArity witness toucherHasCupCodArity)
    windowPin
    (spineBoundaryChained_tail bubbledChained).1
    tailsCancel

/-! ## Honesty marker -/

/-- **Honesty marker — the cup-head discharge with the arity/boundary pins DISCHARGED (peel
campaign H, cup seat-tracking rung 1).**  `cupHeadExtractionConclusion_ofLocatedCupBubble`: the
arity-generic assembly's six cup pins are cut to the two genuine orbit residuals (window pin + tails
cancel) plus the located toucher being a cup — the two moved-arity pins fall out of the bubble
preserving the cup toucher's generator arities, and the moved-boundary pin falls out of the bubbled
list being chained at the running boundary.  What this marker does NOT claim: the window pin
(history-dependent seat, the orbit search) or the tails cancel (the leg-de-merge) — those remain the
orbit's to supply.  `= true`. -/
def fxMode_hasArcCupHeadRealizeCupToucher : Bool := true

end FX1Poly.Polygraph
