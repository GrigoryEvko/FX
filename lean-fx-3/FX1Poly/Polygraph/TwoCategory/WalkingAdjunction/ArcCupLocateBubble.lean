import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupExists
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupBubbleDescent

/-! # ArcCupLocateBubble — a positive cup total produces a located, bubbled cup at the front

The cup-head discharge (`#2152`) opens by producing three of the five inputs the window
assembly (`cupHeadExtractionConclusion_ofLocatedBubbleWindowAndCancel`) demands: the split at a
cup, a `BubblesToFront` witness carrying that cup to the front, and the moved cup's dom-arity
pin.  Both halves are already shipped:

  * `arcSpine_hasCup_of_cupCount_pos` (ArcCupExists) — a positive cup total locates a cup atom,
    splitting the spine as `prefixAtoms ++ cupAtom :: suffixAtoms`;
  * `adjunctionCup_bubblesThroughPrefix` (ArcCupBubbleDescent) — a cup at the end of a
    boundary-chained prefix bubbles to the front, moved image still a cup.

This brick chains them: a boundary-chained spine with a positive cup total splits at a cup that
bubbles to the front with its dom-arity preserved — the window-FREE half of the cup locator,
mirroring how `arcSpine_hasCup_of_cupCount_pos` was the existence half.  The two residual inputs
the window assembly still needs — `windowPin` (the bubbled cup lands at the head's window) and
`tailsCancel` — are the genuinely orbit-dependent pins the refuted unconditional cancel
(`not_arcCupHeadCancellationUnconditional`) leaves open; neither is produced here.

Raw Lean 4 + Init; structural chaining of two shipped producers; per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **A positive cup total produces a located, bubbled cup at the front.**  If a
boundary-chained walking-adjunction spine has a positive cup total, it splits at a cup atom
(`arcSpine_hasCup_of_cupCount_pos`) that bubbles all the way to the front
(`adjunctionCup_bubblesThroughPrefix`), the moved image still a cup — the split, the
`BubblesToFront` witness, and `movedDomPin`, exactly the three non-orbit inputs the window
assembly consumes. -/
theorem arcCupLocateAndBubble_ofCupCountPos (bottomCount : Nat)
    {overallSource overallTarget : adjunctionGraph.Mode}
    (secondList : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (secondChained : SpineBoundaryChained bottomCount secondList)
    (cupCountPos : 0 < (arcStructureOfSpineList bottomCount secondList).cupCount) :
    ∃ (prefixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
      (toucherAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
      (suffixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
      (movedTarget : SpineAtom adjunctionModeSignature overallSource overallTarget)
      (movedPrefixAtoms :
        List (SpineAtom adjunctionModeSignature overallSource overallTarget)),
      secondList = prefixAtoms ++ toucherAtom :: suffixAtoms
        ∧ BubblesToFront toucherAtom prefixAtoms movedTarget movedPrefixAtoms
        ∧ movedTarget.generatorDom.length = 0 := by
  obtain ⟨prefixAtoms, cupAtom, suffixAtoms, doesSplitSpine, cupDom, _cupCod⟩ :=
    arcSpine_hasCup_of_cupCount_pos bottomCount secondList cupCountPos
  rw [doesSplitSpine] at secondChained
  obtain ⟨movedTarget, movedPrefixAtoms, witness, movedIsCup⟩ :=
    adjunctionCup_bubblesThroughPrefix cupAtom cupDom prefixAtoms suffixAtoms bottomCount
      secondChained
  exact ⟨prefixAtoms, cupAtom, suffixAtoms, movedTarget, movedPrefixAtoms,
    doesSplitSpine, witness, movedIsCup⟩

/-! ## Honesty marker -/

/-- **Honesty marker — the window-free cup locate-and-bubble is SHIPPED (peel campaign H).**
`arcCupLocateAndBubble_ofCupCountPos` chains the existence half (`arcSpine_hasCup_of_cupCount_pos`)
with the bubble producer (`adjunctionCup_bubblesThroughPrefix`): a positive cup total on a
boundary-chained spine yields the split at a cup, a `BubblesToFront` witness carrying it to the
front, and `movedDomPin` — the three non-orbit inputs of
`cupHeadExtractionConclusion_ofLocatedBubbleWindowAndCancel`.  What this marker does NOT claim:
`windowPin` (the bubbled cup lands at the head's window — the located cup here is any cup, not the
window-matched one) nor `tailsCancel` — the two orbit-dependent inputs the refuted unconditional
cancel leaves open.  `= true`. -/
def fxMode_hasArcCupLocateBubble : Bool := true

end FX1Poly.Polygraph
