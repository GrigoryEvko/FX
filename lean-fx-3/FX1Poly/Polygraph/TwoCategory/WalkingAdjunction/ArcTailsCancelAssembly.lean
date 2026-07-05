import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupHeadRealizeAssembly

/-! # ArcTailsCancelAssembly — the cup cancel's field decomposition (peel campaign H)

The cup case's residual `tailsCancel` is a `FullArcStructure` equality
(`arcStructureOfSpineList targetBoundary tailList = arcStructureOfSpineList targetBoundary remainder`).
`FullArcStructure` is `{ diagram, cupCount, capCount, internalCupCounts, internalCapCounts }`, so that
equality decomposes componentwise into FIVE field-agreements — and the campaign has split exactly
along that seam:

  * the DIAGRAM leg (`diagram` — boundary port counts, canonical partner matching, loop count) ALWAYS
    agrees, even on the count-cancel's refuting witness (`arcCupObstruction_freshDiagram_agrees`, parity
    rung P-5d); this is the parity campaign's target;
  * the COUNT legs (`cupCount`, `capCount`, `internalCupCounts`, `internalCapCounts`) are what the
    unconditional cancel FORGETS (`not_arcCupHeadCancellationUnconditional` — the composite joins the
    peeled cup's legs, seeing only the SUM of the two legs' internal counts); the orbit's
    through-the-head re-selection realigns the leg attachment so the counts agree on the SELECTED
    remainder.

This brick ships the assembly seam itself: a generic field-wise `FullArcStructure` reconstruction and
the `tailsCancel`-shaped wrapper that combines the diagram leg with the four count legs.  With it, the
cup cancel's two halves (diagram — shipping; counts — the orbit) plug in independently.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- **A `FullArcStructure` equality from its five field-agreements.**  The arc structure is a flat
record of a boundary diagram plus the cup/cap totals and per-port internal counts, so equality
reconstructs field by field. -/
theorem FullArcStructure.eq_of_fields {first second : FullArcStructure}
    (diagramAgree : first.diagram = second.diagram)
    (cupCountAgree : first.cupCount = second.cupCount)
    (capCountAgree : first.capCount = second.capCount)
    (internalCupCountsAgree : first.internalCupCounts = second.internalCupCounts)
    (internalCapCountsAgree : first.internalCapCounts = second.internalCapCounts) :
    first = second := by
  obtain ⟨firstDiagram, firstCupCount, firstCapCount, firstInternalCupCounts,
    firstInternalCapCounts⟩ := first
  obtain ⟨secondDiagram, secondCupCount, secondCapCount, secondInternalCupCounts,
    secondInternalCapCounts⟩ := second
  have diagramEq : firstDiagram = secondDiagram := diagramAgree
  have cupCountEq : firstCupCount = secondCupCount := cupCountAgree
  have capCountEq : firstCapCount = secondCapCount := capCountAgree
  have internalCupCountsEq : firstInternalCupCounts = secondInternalCupCounts :=
    internalCupCountsAgree
  have internalCapCountsEq : firstInternalCapCounts = secondInternalCapCounts :=
    internalCapCountsAgree
  subst diagramEq cupCountEq capCountEq internalCupCountsEq internalCapCountsEq
  rfl

/-- ★ **The cup cancel from the diagram leg and the count legs.**  The `tailsCancel` the cup-head
discharge consumes (`arcStructureOfSpineList targetBoundary tailList = arcStructureOfSpineList
targetBoundary remainder`) follows from its diagram-agreement (the parity campaign's target, invariant
even where the counts are not) together with the four count-agreements (what the through-the-head
orbit re-selection restores on the SELECTED remainder).  The assembly seam: the two halves of the cup
cancel plug in independently. -/
theorem arcCupTailsCancel_ofDiagramAndCounts
    {overallSource overallTarget : adjunctionGraph.Mode}
    (targetBoundary : Nat)
    (tailList remainder :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (diagramAgree : (arcStructureOfSpineList targetBoundary tailList).diagram
        = (arcStructureOfSpineList targetBoundary remainder).diagram)
    (cupCountAgree : (arcStructureOfSpineList targetBoundary tailList).cupCount
        = (arcStructureOfSpineList targetBoundary remainder).cupCount)
    (capCountAgree : (arcStructureOfSpineList targetBoundary tailList).capCount
        = (arcStructureOfSpineList targetBoundary remainder).capCount)
    (internalCupCountsAgree : (arcStructureOfSpineList targetBoundary tailList).internalCupCounts
        = (arcStructureOfSpineList targetBoundary remainder).internalCupCounts)
    (internalCapCountsAgree : (arcStructureOfSpineList targetBoundary tailList).internalCapCounts
        = (arcStructureOfSpineList targetBoundary remainder).internalCapCounts) :
    arcStructureOfSpineList targetBoundary tailList
      = arcStructureOfSpineList targetBoundary remainder :=
  FullArcStructure.eq_of_fields diagramAgree cupCountAgree capCountAgree
    internalCupCountsAgree internalCapCountsAgree

/-! ## Honesty marker -/

/-- **Honesty marker — the cup cancel's field-decomposition seam is SHIPPED (peel campaign H).**
`FullArcStructure.eq_of_fields` reconstructs the arc-structure equality from its five field-agreements;
`arcCupTailsCancel_ofDiagramAndCounts` re-fronts it as the cup case's `tailsCancel`, splitting it into
the diagram leg (the parity campaign's target — invariant on the count-cancel's refuting witness) and
the four count legs (what the orbit's through-the-head re-selection restores).  What this marker does
NOT claim: EITHER leg — the general diagram agreement (the parity campaign is mid-flight; the MIXED
cell routes through the trace orbit) nor the count agreement on the selected remainder (the orbit).
`= true`. -/
def fxMode_hasArcTailsCancelAssembly : Bool := true

end FX1Poly.Polygraph
