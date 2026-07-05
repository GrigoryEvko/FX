import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupLocateBubble
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupHeadCountPositive

/-! # ArcCupCaseLocate — the cup case's three non-orbit inputs, from the dispatch hypotheses

The chained head extraction's cup case (`spineArcHeadExtractionChained_ofArityDispatch`) hands a
cup-arity head, a boundary-chained second spine, and arc-structure equality.  From exactly those,
this brick produces the three non-orbit inputs the window assembly
(`cupHeadExtractionConclusion_ofLocatedBubbleWindowAndCancel`) demands — the located split, the
`BubblesToFront` witness, and `movedDomPin` — by chaining the two shipped halves:

  1. `arcCupHead_cupCount_pos` — the cup head forces `0 < cupCount (headAtom :: tailList)`, and
     arc-structure equality transports it to `0 < cupCount secondList`;
  2. `arcCupLocateAndBubble_ofCupCountPos` — a positive cup total on the boundary-chained second
     spine splits at a cup that bubbles to the front, dom-arity preserved.

After this brick, the cup case's residual is EXACTLY the two orbit pins the refuted unconditional
cancel leaves open: `windowPin` (the bubbled cup lands at the head's window) and `tailsCancel`.

Raw Lean 4 + Init; structural chaining of the two shipped halves; per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The cup case's three non-orbit inputs, from the dispatch hypotheses.**  For a cup-arity
head, a boundary-chained second spine, and arc-structure equality, the second spine splits at a
cup that bubbles to the front with its dom-arity preserved.  The cup total is positive on the
first spine (the head cup, `arcCupHead_cupCount_pos`), transported to the second by arc-structure
equality, then the shipped locator (`arcCupLocateAndBubble_ofCupCountPos`) does the rest. -/
theorem arcCupCase_locateAndBubble {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount : Nat)
    (headAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (hasCupDomArity : headAtom.generatorDom.length = 0)
    (hasCupCodArity : headAtom.generatorCod.length = 2)
    (tailList secondList :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (secondChained : SpineBoundaryChained bottomCount secondList)
    (arcEqual : arcStructureOfSpineList bottomCount (headAtom :: tailList)
        = arcStructureOfSpineList bottomCount secondList) :
    ∃ (prefixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
      (toucherAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
      (suffixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
      (movedTarget : SpineAtom adjunctionModeSignature overallSource overallTarget)
      (movedPrefixAtoms :
        List (SpineAtom adjunctionModeSignature overallSource overallTarget)),
      secondList = prefixAtoms ++ toucherAtom :: suffixAtoms
        ∧ BubblesToFront toucherAtom prefixAtoms movedTarget movedPrefixAtoms
        ∧ movedTarget.generatorDom.length = 0 := by
  have headPos : 0 < (arcStructureOfSpineList bottomCount (headAtom :: tailList)).cupCount :=
    arcCupHead_cupCount_pos bottomCount headAtom hasCupDomArity hasCupCodArity tailList
  have cupCountEq : (arcStructureOfSpineList bottomCount (headAtom :: tailList)).cupCount
      = (arcStructureOfSpineList bottomCount secondList).cupCount :=
    congrArg FullArcStructure.cupCount arcEqual
  have secondPos : 0 < (arcStructureOfSpineList bottomCount secondList).cupCount :=
    cupCountEq ▸ headPos
  exact arcCupLocateAndBubble_ofCupCountPos bottomCount secondList secondChained secondPos

/-! ## Honesty marker -/

/-- **Honesty marker — the cup case's non-orbit inputs are SHIPPED (peel campaign H).**
`arcCupCase_locateAndBubble` produces the located split, the `BubblesToFront` witness, and
`movedDomPin` from the cup case's actual dispatch hypotheses (cup head + boundary-chained second
spine + arc-structure equality), chaining `arcCupHead_cupCount_pos` (positivity, transported by
arc-equality) with `arcCupLocateAndBubble_ofCupCountPos` (locate + bubble).  What this marker does
NOT claim: `windowPin` (the bubbled cup lands at the head's window) nor `tailsCancel` — the two
orbit-dependent pins the refuted unconditional cancel leaves open.  `= true`. -/
def fxMode_hasArcCupCaseLocate : Bool := true

end FX1Poly.Polygraph
