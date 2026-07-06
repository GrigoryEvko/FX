import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupTailsCancelCounts

/-! # ArcCupTailsCancelInterface — the cup tails-cancel modulo the three orbit residuals (peel campaign H, count rung P-5d-interface)

The cup cancel's `tailsCancel` decomposes (`arcCupTailsCancel_ofDiagramAndCounts`) into FIVE field
agreements.  Two of them — the total `cupCount` / `capCount` legs — are now shipped
(`arcCupTailsCancel_countLegs_ofCupHead`), derived from the whole-spine arc equality plus the located
bubble's trace equivalence.  This brick fuses those two shipped legs with the three genuine orbit
residuals into the single `tailsCancel` the discharge consumes, drawing the residual interface sharp:

  * ★ `arcCupTailsCancel_ofCupHead_diagramAndInternals` — given the whole-spine arc equality, the bubble's
    trace equivalence, the located toucher being a cup, and the THREE orbit residuals (the fresh boundary
    DIAGRAM leg + the two per-port INTERNAL count legs `internalCupCounts` / `internalCapCounts`), the full
    `tailsCancel` follows: the two total count legs are supplied internally.

After this brick the cup discharge owes, beyond the located bubble + window pin, exactly the diagram leg
(the parity campaign) and the two internal-count legs (the leg-de-merge) — three field agreements, all
routed through the through-the-head trace orbit.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The cup tails-cancel from the diagram leg and the two internal-count legs.**  For a cup head,
the whole-spine arc equality (`arcEqual`) and the located bubble's trace equivalence (`atomicEquiv`)
supply the two TOTAL count legs (`arcCupTailsCancel_countLegs_ofCupHead`); combined with the fresh
boundary DIAGRAM agreement and the two per-port INTERNAL count agreements — the three residuals the
through-the-head trace orbit is charged with — the full `tailsCancel` at any target boundary follows
(`arcCupTailsCancel_ofDiagramAndCounts`). -/
theorem arcCupTailsCancel_ofCupHead_diagramAndInternals
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount targetBoundary : Nat)
    (headAtom : SpineAtom adjunctionModeSignature overallSource overallTarget)
    (hasCupDomArity : headAtom.generatorDom.length = 0)
    (hasCupCodArity : headAtom.generatorCod.length = 2)
    (tailList secondList remainder :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (arcEqual : arcStructureOfSpineList bottomCount (headAtom :: tailList)
        = arcStructureOfSpineList bottomCount secondList)
    (atomicEquiv : AtomicTraceEquiv adjunctionModeSignature secondList (headAtom :: remainder))
    (diagramAgree : (arcStructureOfSpineList targetBoundary tailList).diagram
        = (arcStructureOfSpineList targetBoundary remainder).diagram)
    (internalCupCountsAgree :
      (arcStructureOfSpineList targetBoundary tailList).internalCupCounts
        = (arcStructureOfSpineList targetBoundary remainder).internalCupCounts)
    (internalCapCountsAgree :
      (arcStructureOfSpineList targetBoundary tailList).internalCapCounts
        = (arcStructureOfSpineList targetBoundary remainder).internalCapCounts) :
    arcStructureOfSpineList targetBoundary tailList
      = arcStructureOfSpineList targetBoundary remainder := by
  obtain ⟨cupCountAgree, capCountAgree⟩ :=
    arcCupTailsCancel_countLegs_ofCupHead bottomCount targetBoundary headAtom hasCupDomArity
      hasCupCodArity tailList secondList remainder arcEqual atomicEquiv
  exact arcCupTailsCancel_ofDiagramAndCounts targetBoundary tailList remainder diagramAgree
    cupCountAgree capCountAgree internalCupCountsAgree internalCapCountsAgree

/-! ## Honesty marker -/

/-- **Honesty marker — the cup tails-cancel modulo the three orbit residuals (peel campaign H, count
rung P-5d-interface).**  `arcCupTailsCancel_ofCupHead_diagramAndInternals`: the full cup `tailsCancel`
follows from the whole-spine arc equality + the located bubble's trace equivalence + the located toucher
being a cup + the THREE orbit residuals (the fresh boundary diagram leg + the two per-port internal count
legs).  The two total count legs are supplied internally by the shipped
`arcCupTailsCancel_countLegs_ofCupHead`.  What this marker does NOT claim: the three residuals themselves
— the diagram agreement (the parity campaign) and the two internal-count agreements (the leg-de-merge),
both routed through the through-the-head trace orbit.  `= true`. -/
def fxMode_hasArcCupTailsCancelInterface : Bool := true

end FX1Poly.Polygraph
