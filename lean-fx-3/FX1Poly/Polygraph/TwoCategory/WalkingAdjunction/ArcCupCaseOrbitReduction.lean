import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupHeadWindowAssembly
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcChainedExtraction

/-! # ArcCupCaseOrbitReduction — the cup case is EXACTLY the orbit witness

This brick isolates the sole residual of the walking-adjunction cup-head discharge.  Everything
below `windowPin` + `tailsCancel` is shipped: the located split, the bubble witness, and
`movedDomPin` come from `arcCupCase_locateAndBubble`; the two derived pins (`movedCodPin`,
`boundaryPin`) are recovered inside `cupHeadExtractionConclusion_ofLocatedBubbleWindowAndCancel`.
So the entire cup case reduces to producing ONE existential — a located cup carrying all five
pins, `ArcCupOrbitWitness` — which the orbit (the through-the-head trace re-selection the refuted
unconditional cancel leaves open) must supply.

  * `ArcCupOrbitWitness` — the located-cup certificate: a split at a cup that bubbles to the front
    with dom-arity `0`, lands at the head's window, and cancels the tail's arc structure at the
    head's target boundary;
  * ★ `spineArcHeadExtractionChained_cupCase_ofOrbitWitness` — the orbit witness discharges the
    whole cup case (the `cupCase` hypothesis of `spineArcHeadExtractionChained_ofArityDispatch`).

After this brick, `ArcCupOrbitWitness` is the ONLY thing standing between the shipped assembly and
`fxMode_hasArcCellReconstruction` — the Joyal-Street cup orbit, and nothing else.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- **The located-cup orbit certificate.**  A split of `secondList` at a cup that bubbles to the
front carrying: dom-arity `0` (`movedDomPin`), landing at the head's window (`windowPin`), and
cancelling the tail's arc structure at the head's target boundary (`tailsCancel`).  These are
exactly the orbit-dependent inputs `cupHeadExtractionConclusion_ofLocatedBubbleWindowAndCancel`
consumes beyond the derived pins.  Single-`∃` proposition; the orbit produces it, the reduction
below consumes it. -/
def ArcCupOrbitWitness {overallSource overallTarget : adjunctionGraph.Mode}
    (headAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (tailList secondList :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget)) : Prop :=
  ∃ (prefixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (toucherAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (suffixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (movedTarget : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (movedPrefixAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget)),
    secondList = prefixAtoms ++ toucherAtom :: suffixAtoms
      ∧ BubblesToFront toucherAtom prefixAtoms movedTarget movedPrefixAtoms
      ∧ movedTarget.generatorDom.length = 0
      ∧ movedTarget.leftContext.length = headAtom.leftContext.length
      ∧ arcStructureOfSpineList headAtom.codBoundaryLength tailList
          = arcStructureOfSpineList headAtom.codBoundaryLength (movedPrefixAtoms ++ suffixAtoms)

/-- ★ **The orbit witness discharges the whole cup case.**  Granted `ArcCupOrbitWitness`, the cup
case's full conclusion (a realized trace-equivalence bubble, a remainder chained at the head's
target boundary, tails arc-equal there) follows: the head fires at `bottomCount`
(`spineBoundaryChained_tail firstChained`), and the located data feed straight into
`cupHeadExtractionConclusion_ofLocatedBubbleWindowAndCancel`. -/
theorem spineArcHeadExtractionChained_cupCase_ofOrbitWitness
    {overallSource overallTarget : adjunctionGraph.Mode} (bottomCount : Nat)
    (headAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (hasCupDomArity : headAtom.generatorDom.length = 0)
    (hasCupCodArity : headAtom.generatorCod.length = 2)
    (tailList secondList :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (firstChained : SpineBoundaryChained bottomCount (headAtom :: tailList))
    (secondChained : SpineBoundaryChained bottomCount secondList)
    (orbit : ArcCupOrbitWitness headAtom tailList secondList) :
    ∃ matchedRemainder,
      SpineTraceEquiv adjunctionModeSignature secondList (headAtom :: matchedRemainder)
        ∧ SpineBoundaryChained headAtom.codBoundaryLength matchedRemainder
        ∧ arcStructureOfSpineList headAtom.codBoundaryLength tailList
            = arcStructureOfSpineList headAtom.codBoundaryLength matchedRemainder := by
  obtain ⟨prefixAtoms, toucherAtom, suffixAtoms, movedTarget, movedPrefixAtoms,
    doesSplitSpine, witness, movedDomPin, windowPin, tailsCancel⟩ := orbit
  exact cupHeadExtractionConclusion_ofLocatedBubbleWindowAndCancel bottomCount headAtom
    hasCupDomArity hasCupCodArity (spineBoundaryChained_tail firstChained).1
    tailList secondList secondChained prefixAtoms suffixAtoms movedPrefixAtoms
    toucherAtom movedTarget doesSplitSpine witness movedDomPin windowPin tailsCancel

/-! ## Honesty marker -/

/-- **Honesty marker — the cup case IS the orbit witness (peel campaign H).**
`spineArcHeadExtractionChained_cupCase_ofOrbitWitness` discharges the entire cup case from one
`ArcCupOrbitWitness` — the located cup carrying all five pins.  Combined with
`arcCupCase_locateAndBubble` (which supplies the split + bubble + `movedDomPin` from the dispatch
hypotheses), the ONLY residual of `fxMode_hasArcCellReconstruction` is now producing the last two
pins of the orbit witness: `windowPin` (the bubbled cup lands at the head's window) and
`tailsCancel` — the through-the-head trace re-selection the refuted unconditional cancel leaves
open.  This marker does NOT claim that witness exists.  `= true`. -/
def fxMode_hasArcCupCaseOrbitReduction : Bool := true

end FX1Poly.Polygraph
