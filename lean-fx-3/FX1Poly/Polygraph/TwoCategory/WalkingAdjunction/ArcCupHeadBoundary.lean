import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcDisciplineFold
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineBoundaryChain
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineTraceDecision

/-! # ArcCupHeadBoundary — the cup-head discharge's structural opening (peel campaign H)

The cup-side counterpart of the CAP discharge's opening plumbing
(`spineArcHeadExtractionChained_ofCapArity`, lines 75-102): before any locate/bubble/orbit
work, a cup-arity head fixes its boundary geometry from the chain alone.  A cap CONSUMES two
ports, so its cod boundary SHRINKS by two; a cup CREATES two legs, so its cod boundary GROWS
by two — the mirror sign the peel moves the running boundary in.

  * `arcCupHeadWindowFits` — the window sits within the running boundary
    (`leftContext.length ≤ bottomCount`); the cup's empty generator domain leaves the whole
    boundary available below the splice;
  * `arcCupHeadCodBoundaryGrows` — the head's cod boundary is `bottomCount + 2` (the two
    fresh legs), the tail's running boundary after the peel;
  * `arcCupHeadCompositeAsCupStep` — the composite arc structure of the cup-headed list IS
    the tail folded from the spliced seed (`stepCupArc` at the window), the cup analog of the
    cap discharge's `stepArcAtom_eq_stepCapArc` extract bridge.

These are the pure-arithmetic prerequisites every cup discharge route consumes; the genuine
cup residual (the orbit-form remainder re-selection replacing the REFUTED unconditional
cancel — see `not_arcCupHeadCancellationUnconditional`) is untouched here.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- **The cup head's window fits the running boundary.**  A cup-arity head chained at
`bottomCount` fires at a window `leftContext.length ≤ bottomCount`: its empty generator
domain (`generatorDom.length = 0`) consumes nothing, so the full running boundary is
available at or above the splice. -/
theorem arcCupHeadWindowFits {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount : Nat)
    (headAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (hasCupDomArity : headAtom.generatorDom.length = 0)
    (tailList : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (firstChained : SpineBoundaryChained bottomCount (headAtom :: tailList)) :
    headAtom.leftContext.length ≤ bottomCount := by
  have headFires : headAtom.domBoundaryLength = bottomCount :=
    (spineBoundaryChained_tail firstChained).1
  rw [← headFires]
  show headAtom.leftContext.length
      ≤ headAtom.leftContext.length + headAtom.generatorDom.length
        + headAtom.rightContext.length
  rw [hasCupDomArity]
  exact Nat.le_add_right headAtom.leftContext.length headAtom.rightContext.length

/-- **The cup head's cod boundary grows by two.**  A cup-arity head chained at `bottomCount`
(`generatorDom.length = 0`, `generatorCod.length = 2`) has cod boundary `bottomCount + 2` —
the two fresh legs the splice creates.  This is the tail's running boundary after the peel:
the boundary MOVES UP by two, the mirror of the cap's shrink-by-two. -/
theorem arcCupHeadCodBoundaryGrows {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount : Nat)
    (headAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (hasCupDomArity : headAtom.generatorDom.length = 0)
    (hasCupCodArity : headAtom.generatorCod.length = 2)
    (tailList : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (firstChained : SpineBoundaryChained bottomCount (headAtom :: tailList)) :
    headAtom.codBoundaryLength = bottomCount + 2 := by
  have headFires : headAtom.domBoundaryLength = bottomCount :=
    (spineBoundaryChained_tail firstChained).1
  rw [← headFires]
  show headAtom.leftContext.length + headAtom.generatorCod.length
      + headAtom.rightContext.length
    = headAtom.leftContext.length + headAtom.generatorDom.length
      + headAtom.rightContext.length + 2
  rw [hasCupDomArity, hasCupCodArity]
  show headAtom.leftContext.length + 2 + headAtom.rightContext.length
    = headAtom.leftContext.length + headAtom.rightContext.length + 2
  exact Nat.add_right_comm headAtom.leftContext.length 2 headAtom.rightContext.length

/-- **The cup-headed composite folds from the spliced seed.**  For a cup-arity head, the
composite arc structure of `headAtom :: tailList` equals the tail's arc structure folded from
the seed with the cup already spliced at the window (`stepCupArc` at `leftContext.length`) —
the cup analog of the cap discharge's `stepArcAtom_eq_stepCapArc` extract bridge, opening the
composite side in `stepCupArc` form so the shipped `arcCupHeadFolded_extractArc` transport can
land. -/
theorem arcCupHeadCompositeAsCupStep {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount : Nat)
    (headAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (hasCupDomArity : headAtom.generatorDom.length = 0)
    (hasCupCodArity : headAtom.generatorCod.length = 2)
    (tailList : List (SpineAtom adjunctionModeSignature overallSource overallTarget)) :
    arcStructureOfSpineList bottomCount (headAtom :: tailList)
      = extractArc bottomCount
          (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              headAtom.leftContext.length) tailList) := by
  show extractArc bottomCount
      (processArcSpine
        (stepArcAtom (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          headAtom) tailList)
    = extractArc bottomCount
        (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            headAtom.leftContext.length) tailList)
  rw [stepArcAtom_eq_stepCupArc
    (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) headAtom
    hasCupDomArity hasCupCodArity]

/-! ## Honesty marker -/

/-- **Honesty marker — the cup-head discharge's structural opening (peel campaign H).**
`arcCupHeadWindowFits` (window within the boundary), `arcCupHeadCodBoundaryGrows` (cod
boundary `bottomCount + 2`, the peel moves up by two), and `arcCupHeadCompositeAsCupStep`
(the cup-headed composite folds from the spliced seed) fix the cup head's boundary geometry
from the chain — the pure-arithmetic prerequisites of any cup discharge route, the cup mirror
of the cap discharge's opening.  What this marker does NOT claim: the cup LOCATE, the cup
BUBBLE, or the orbit-form remainder re-selection that replaces the REFUTED unconditional
cancel (`not_arcCupHeadCancellationUnconditional`) — the genuine cup residual.  `= true`. -/
def fxMode_hasArcCupHeadBoundary : Bool := true

end FX1Poly.Polygraph
