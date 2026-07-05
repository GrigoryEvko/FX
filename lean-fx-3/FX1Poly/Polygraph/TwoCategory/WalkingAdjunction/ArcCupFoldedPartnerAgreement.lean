import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupDiagramAgreement
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupFoldedLegSwap

/-! # ArcCupFoldedPartnerAgreement — the per-index partner cancel under a same-classification precondition (peel campaign H, parity rung P-5e)

The fresh-diagram partner agreement decomposes per composite index into three cells by the
fused/off classification of the shifted probe in each of the two chained folded runs:

  * BOTH OFF both window legs — `arcCupHeadFolded_offFusedPartner_agrees` (rung P-5d): the
    transport collapses to the injective downshift, so equal composites lift to equal fresh
    partners;
  * BOTH FUSED to a window leg — `arcCupFoldedLegAttachment_agrees` (rung P-5b): the two
    matching branches chain and the two mixed branches are the leg swap, killed on the
    disciplined chained fragment;
  * the MIXED cell (fused in one run, off in the other) — NOT locally refutable
    (`ArcCupDiagramAgreement`'s honest boundary): the cup-count head-contribution asymmetry
    is absorbed by the leg-joined base census, so the two bases carry no cross-run
    inequality.

This brick assembles the two SAME-CLASSIFICATION cells into one per-index partner agreement,
consuming exactly a `sameClassification` precondition — the fused/off status of the probe
agrees across the two runs — which EXCLUDES the mixed cell by hypothesis.  That precondition
is precisely what the through-the-head trace orbit delivers: the orbit re-selects a
trace-equivalent second spine with no mixed cell against the first, and then this agreement
folds pointwise into the whole fresh-diagram partner-list equality.  The assembly draws the
honest seam: everything downstream of a mixed-free second spine is local and shipped; the
sole residual is the orbit producing that second spine.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The per-index fresh partner agreement under a same-classification precondition.**  At
a composite index whose shifted probe has the SAME fused/off status in both chained,
legs-separated runs (the `sameClassification` iff — fused-to-a-window-leg in the first run
exactly when fused in the second), the two fresh partner values coincide.  The precondition
rules out the mixed cell, so the proof dispatches on the shared status: both fused hands off
to the leg-attachment agreement (rung P-5b), both off to the off-fused agreement (rung
P-5d).  The `sameClassification` precondition is the through-the-head trace orbit's target
(a mixed-free second spine); with it, the fresh-diagram partner list agrees index by index. -/
theorem arcCupFoldedPartner_agrees_ofSameClassification
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat) (windowFits : windowPosition ≤ bottomCount)
    (firstAtoms secondAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (firstChained : SpineBoundaryChained (bottomCount + 2) firstAtoms)
    (secondChained : SpineBoundaryChained (bottomCount + 2) secondAtoms)
    (firstLegsSeparate : isSameComponent
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        firstAtoms).links windowPosition (windowPosition + 1) = false)
    (secondLegsSeparate : isSameComponent
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        secondAtoms).links windowPosition (windowPosition + 1) = false)
    (compositeEq : extractArc bottomCount
        (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) firstAtoms)
      = extractArc bottomCount
          (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) secondAtoms))
    (compositeIndex : Nat)
    (indexInRangeFirst : compositeIndex
      < bottomCount
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          firstAtoms).openWires.length)
    (indexInRangeSecond : compositeIndex
      < bottomCount
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          secondAtoms).openWires.length)
    (sameClassification :
      (partnerIndexOf
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            firstAtoms).links
          (List.range (bottomCount + 2)
            ++ (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              firstAtoms).openWires)
          (bottomCount + 2
            + (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              firstAtoms).openWires.length)
          (freshShiftAbove windowPosition 2 compositeIndex) = windowPosition
        ∨ partnerIndexOf
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              firstAtoms).links
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
                firstAtoms).openWires)
            (bottomCount + 2
              + (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
                firstAtoms).openWires.length)
            (freshShiftAbove windowPosition 2 compositeIndex) = windowPosition + 1)
      ↔ (partnerIndexOf
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            secondAtoms).links
          (List.range (bottomCount + 2)
            ++ (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              secondAtoms).openWires)
          (bottomCount + 2
            + (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              secondAtoms).openWires.length)
          (freshShiftAbove windowPosition 2 compositeIndex) = windowPosition
        ∨ partnerIndexOf
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              secondAtoms).links
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
                secondAtoms).openWires)
            (bottomCount + 2
              + (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
                secondAtoms).openWires.length)
            (freshShiftAbove windowPosition 2 compositeIndex) = windowPosition + 1)) :
    partnerIndexOf
        (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          firstAtoms).links
        (List.range (bottomCount + 2)
          ++ (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            firstAtoms).openWires)
        (bottomCount + 2
          + (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            firstAtoms).openWires.length)
        (freshShiftAbove windowPosition 2 compositeIndex)
      = partnerIndexOf
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            secondAtoms).links
          (List.range (bottomCount + 2)
            ++ (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              secondAtoms).openWires)
          (bottomCount + 2
            + (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              secondAtoms).openWires.length)
          (freshShiftAbove windowPosition 2 compositeIndex) := by
  refine dite
      (partnerIndexOf
          (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            firstAtoms).links
          (List.range (bottomCount + 2)
            ++ (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              firstAtoms).openWires)
          (bottomCount + 2
            + (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              firstAtoms).openWires.length)
          (freshShiftAbove windowPosition 2 compositeIndex) = windowPosition
        ∨ partnerIndexOf
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              firstAtoms).links
            (List.range (bottomCount + 2)
              ++ (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
                firstAtoms).openWires)
            (bottomCount + 2
              + (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
                firstAtoms).openWires.length)
            (freshShiftAbove windowPosition 2 compositeIndex) = windowPosition + 1)
      (fun firstFused => ?_) (fun firstNotFused => ?_)
  · exact arcCupFoldedLegAttachment_agrees bottomCount windowPosition windowFits
      firstAtoms secondAtoms firstChained secondChained compositeIndex
      indexInRangeFirst indexInRangeSecond firstFused (sameClassification.mp firstFused)
  · have secondNotFused := fun secondFused => firstNotFused (sameClassification.mpr secondFused)
    exact arcCupHeadFolded_offFusedPartner_agrees bottomCount windowPosition windowFits
      firstAtoms secondAtoms firstChained secondChained firstLegsSeparate secondLegsSeparate
      compositeEq compositeIndex indexInRangeFirst
      (fun leftHit => firstNotFused (Or.inl leftHit))
      (fun rightHit => firstNotFused (Or.inr rightHit))
      (fun leftHit => secondNotFused (Or.inl leftHit))
      (fun rightHit => secondNotFused (Or.inr rightHit))

/-! ## Honesty marker -/

/-- **Honesty marker — the per-index partner cancel is SHIPPED under a same-classification
precondition (peel campaign H, parity rung P-5e).**
`arcCupFoldedPartner_agrees_ofSameClassification`: at a composite index whose shifted probe
has the same fused/off status in both chained legs-separated runs, the two fresh partner
values coincide — both-fused dispatches to the leg-attachment agreement (P-5b), both-off to
the off-fused agreement (P-5d), and the mixed cell is excluded by the precondition.  What
this marker does NOT claim: the same-classification precondition itself — that is the
through-the-head trace orbit's job (re-selecting a mixed-free second spine), where the
refuted unconditional cancel's residue lives; nor the fold of this per-index agreement into
the whole fresh-diagram partner-list equality.  `= true`. -/
def fxMode_hasArcCupFoldedPartnerAgreement : Bool := true

end FX1Poly.Polygraph
