import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupCaseOrbitReduction
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupCaseLocate

/-! # ArcCupOrbitPinsReduction — the orbit witness reduces to exactly its two open pins

`ArcCupOrbitWitness` bundles FIVE fields: the located split, the `BubblesToFront` bubble, `movedDomPin`
(dom-arity `0`), `windowPin` (the bubbled cup lands at the head's window), and `tailsCancel` (the tails'
arc structures agree at the head's target boundary).  The first three are SHIPPED unconditionally from
the dispatch hypotheses by `arcCupCase_locateAndBubble` (peel campaign H).  So inhabiting the whole
witness reduces to supplying just the last two pins — FOR whatever located witnesses the locator produces.

This brick is that reduction: given the two pins hold for every located split/bubble the locator could
emit, the full `ArcCupOrbitWitness` follows.  After it, the SOLE open content of the cup-head discharge
(#2152, hence #1996 `fxMode_hasArcCellReconstruction`) is crisply `windowPin ∧ tailsCancel` for the located
cup — `windowPin` the tracker flags as "window forced by arc-equality", `tailsCancel` the through-the-head
trace re-selection gated on `sameClassification` (the refuted unconditional cancel's residue).

Raw Lean 4 + Init; structural bundling of the shipped location with the two pins; per-declaration
`#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The orbit witness from its two open pins.**  With the shipped locator supplying the split, the
bubble, and `movedDomPin`, the full `ArcCupOrbitWitness` follows from the two remaining pins — `windowPin`
and `tailsCancel` — holding for whatever located witnesses the locator emits.  The `pins` hypothesis is
universally quantified over the locator's outputs precisely because the located split/bubble is an
existential; the proof discharges it at the concrete witnesses `arcCupCase_locateAndBubble` produces. -/
theorem arcCupOrbitWitness_ofWindowPinAndTailsCancel
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount : Nat)
    (headAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (hasCupDomArity : headAtom.generatorDom.length = 0)
    (hasCupCodArity : headAtom.generatorCod.length = 2)
    (tailList secondList :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (secondChained : SpineBoundaryChained bottomCount secondList)
    (arcEqual : arcStructureOfSpineList bottomCount (headAtom :: tailList)
        = arcStructureOfSpineList bottomCount secondList)
    (pins : ∀ (prefixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
      (toucherAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
      (suffixAtoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
      (movedTarget : SpineAtom adjunctionModeSignature overallSource overallTarget)
      (movedPrefixAtoms :
        List (SpineAtom adjunctionModeSignature overallSource overallTarget)),
      secondList = prefixAtoms ++ toucherAtom :: suffixAtoms →
      BubblesToFront toucherAtom prefixAtoms movedTarget movedPrefixAtoms →
      movedTarget.generatorDom.length = 0 →
      movedTarget.leftContext.length = headAtom.leftContext.length
        ∧ arcStructureOfSpineList headAtom.codBoundaryLength tailList
            = arcStructureOfSpineList headAtom.codBoundaryLength
                (movedPrefixAtoms ++ suffixAtoms)) :
    ArcCupOrbitWitness headAtom tailList secondList := by
  obtain ⟨prefixAtoms, toucherAtom, suffixAtoms, movedTarget, movedPrefixAtoms,
    doesSplitSpine, bubbleWitness, movedDomPin⟩ :=
    arcCupCase_locateAndBubble bottomCount headAtom hasCupDomArity hasCupCodArity tailList
      secondList secondChained arcEqual
  obtain ⟨windowPin, tailsCancel⟩ :=
    pins prefixAtoms toucherAtom suffixAtoms movedTarget movedPrefixAtoms doesSplitSpine
      bubbleWitness movedDomPin
  exact ⟨prefixAtoms, toucherAtom, suffixAtoms, movedTarget, movedPrefixAtoms,
    doesSplitSpine, bubbleWitness, movedDomPin, windowPin, tailsCancel⟩

/-! ## Honesty marker -/

/-- **Honesty marker — the orbit witness reduces to its two open pins (peel campaign H).**
`arcCupOrbitWitness_ofWindowPinAndTailsCancel`: with the shipped locator discharging the split, bubble,
and `movedDomPin`, the full `ArcCupOrbitWitness` follows from `windowPin ∧ tailsCancel` for the located
cup.  This crisply isolates the entire open content of the cup-head discharge (#2152 / #1996) as those two
pins.  What this marker does NOT claim: EITHER pin — `windowPin` (window forced by arc-equality) nor
`tailsCancel` (the `sameClassification`-gated through-the-head re-selection; the refuted unconditional
cancel's residue).  `= true`. -/
def fxMode_hasArcCupOrbitPinsReduction : Bool := true

end FX1Poly.Polygraph
