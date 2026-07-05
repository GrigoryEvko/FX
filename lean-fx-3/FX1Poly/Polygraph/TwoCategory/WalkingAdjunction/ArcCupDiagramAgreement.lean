import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupTransportReadoff
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupCancelObstruction
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingFreshUnshift

/-! # ArcCupDiagramAgreement — the partner cancel: the fresh DIAGRAM agrees where the counts do not (peel campaign H, parity rung P-5d)

The cup-head cancellation is REFUTED in FULL (`not_arcCupHeadCancellationUnconditional`):
two tails over the same peeled cup with equal composite extracts can differ at the fresh
boundary — the composite joins the peeled cup's legs, forgetting which leg each tail event
attached to.  But that forgetting is confined to the INTERNAL COUNTS: the fresh boundary
DIAGRAM (bottom count, top count, partner matching, loop count) is invariant.  This brick
establishes that isolation on both fronts.

  * `arcCupObstruction_freshDiagram_agrees` — the machine-checked witness: on the very
    obstruction pair whose fresh extracts DIFFER (internal cup counts `[1,0,0,0,1,0,0,0]`
    vs `[0,1,0,0,0,1,0,0]`), the fresh boundary DIAGRAMS are EQUAL.  The partner cancel is
    true exactly where the count cancel fails.

  * `arcCupHeadFolded_offFusedPartner_agrees` — the reusable local leg of the general
    partner cancel: at a composite index whose shifted probe is OFF both window legs in
    both runs, the two fresh partner values coincide.  Equal composite extracts read off
    the partner transport pointwise (rung P-5c); off both legs, the transport is the
    downshifted fresh partner, and the downshift is injective off the window pair.

What this brick does NOT close: the MIXED cell (probe fused to a leg in one run, off both
legs in the other).  That cell is not refuted by the local pointwise equalities alone —
the cup-count transport's head-contribution asymmetry (`+1` on the fused side, `+0` on the
off side) is absorbed by the leg-joined base census, which counts a DIFFERENT wire diagram
in each run, so the two bases carry no cross-run inequality.  The general fresh-diagram
agreement therefore routes through the through-the-head trace orbit (the obstruction's
prescribed correction), not a purely local cancel.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## The witness: the fresh diagram is invariant where the counts are not -/

set_option maxHeartbeats 1600000 in
/-- ★ **The partner cancel holds on the count cancel's refuting witness.**  The two
obstruction tails — whose fresh FULL extracts differ in their internal cup counts — have
EQUAL fresh boundary diagrams (bottom count `4`, top count `4`, partner list
`[4,5,6,7,0,1,2,3]`, loop count `0`).  The composite's forgetting is confined to the
internal counts; the matching is preserved. -/
theorem arcCupObstruction_freshDiagram_agrees :
    (extractArc 4
        (processArcSpine (ArcWireState.mk (List.range 4) [] 4 0 [] [])
          arcCupObstructionLeftTailAtoms)).diagram
      = (extractArc 4
          (processArcSpine (ArcWireState.mk (List.range 4) [] 4 0 [] [])
            arcCupObstructionRightTailAtoms)).diagram := by decide +kernel

/-! ## The off-fused branch of the partner transport -/

/-- The cup partner transport off BOTH window legs is the downshifted fresh partner: both
fused conditions fail, so the transport collapses to its `else` branch. -/
private theorem arcCupPartnerTransport_offFused
    (freshLinks : List (Nat × Nat)) (freshBoundary : List Nat)
    (freshTotal windowPosition compositeIndex : Nat)
    (offLeft : partnerIndexOf freshLinks freshBoundary freshTotal
      (freshShiftAbove windowPosition 2 compositeIndex) ≠ windowPosition)
    (offRight : partnerIndexOf freshLinks freshBoundary freshTotal
      (freshShiftAbove windowPosition 2 compositeIndex) ≠ windowPosition + 1) :
    arcCupPartnerTransport freshLinks freshBoundary freshTotal windowPosition compositeIndex
      = freshUnshiftAbove windowPosition 2
          (partnerIndexOf freshLinks freshBoundary freshTotal
            (freshShiftAbove windowPosition 2 compositeIndex)) := by
  show (if partnerIndexOf freshLinks freshBoundary freshTotal
          (freshShiftAbove windowPosition 2 compositeIndex) = windowPosition then
        (if partnerIndexOf freshLinks freshBoundary freshTotal (windowPosition + 1)
            = windowPosition + 1 then
          compositeIndex
        else
          freshUnshiftAbove windowPosition 2
            (partnerIndexOf freshLinks freshBoundary freshTotal (windowPosition + 1)))
      else if partnerIndexOf freshLinks freshBoundary freshTotal
          (freshShiftAbove windowPosition 2 compositeIndex) = windowPosition + 1 then
        (if partnerIndexOf freshLinks freshBoundary freshTotal windowPosition
            = windowPosition then
          compositeIndex
        else
          freshUnshiftAbove windowPosition 2
            (partnerIndexOf freshLinks freshBoundary freshTotal windowPosition))
      else
        freshUnshiftAbove windowPosition 2
          (partnerIndexOf freshLinks freshBoundary freshTotal
            (freshShiftAbove windowPosition 2 compositeIndex)))
    = freshUnshiftAbove windowPosition 2
        (partnerIndexOf freshLinks freshBoundary freshTotal
          (freshShiftAbove windowPosition 2 compositeIndex))
  rw [if_neg offLeft, if_neg offRight]

/-! ## The off-fused fresh partner agreement -/

/-- ★ **Off both window legs, the fresh partners agree across runs.**  At a composite index
whose shifted probe partners off both cup legs in each of two chained, legs-separated runs
with equal composite extracts, the two fresh partner values coincide.  The pointwise
partner transport (rung P-5c) collapses to the downshifted fresh partner on both sides; the
downshift is a left inverse of the shift off the window pair, so the equal downshifts lift
to equal fresh partners. -/
theorem arcCupHeadFolded_offFusedPartner_agrees
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
    (indexInRange : compositeIndex
      < bottomCount
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          firstAtoms).openWires.length)
    (firstOffLeft : partnerIndexOf
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
        (freshShiftAbove windowPosition 2 compositeIndex) ≠ windowPosition)
    (firstOffRight : partnerIndexOf
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
        (freshShiftAbove windowPosition 2 compositeIndex) ≠ windowPosition + 1)
    (secondOffLeft : partnerIndexOf
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
        (freshShiftAbove windowPosition 2 compositeIndex) ≠ windowPosition)
    (secondOffRight : partnerIndexOf
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
        (freshShiftAbove windowPosition 2 compositeIndex) ≠ windowPosition + 1) :
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
  have transportEq := arcCupHeadFolded_partnerTransport_pointwise bottomCount windowPosition
    windowFits firstAtoms secondAtoms firstChained secondChained firstLegsSeparate
    secondLegsSeparate compositeEq compositeIndex indexInRange
  rw [arcCupPartnerTransport_offFused
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
        windowPosition compositeIndex firstOffLeft firstOffRight,
      arcCupPartnerTransport_offFused
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
        windowPosition compositeIndex secondOffLeft secondOffRight] at transportEq
  have shifted := congrArg (freshShiftAbove windowPosition 2) transportEq
  rw [freshShiftAbove_ofUnshifted windowPosition
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
        (freshShiftAbove windowPosition 2 compositeIndex))
      firstOffLeft firstOffRight,
    freshShiftAbove_ofUnshifted windowPosition
      (partnerIndexOf
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
        (freshShiftAbove windowPosition 2 compositeIndex))
      secondOffLeft secondOffRight] at shifted
  exact shifted

/-! ## Honesty marker -/

/-- **Honesty marker — the partner cancel is SHIPPED for the off-fused leg + machine-checked
on the witness (peel campaign H, parity rung P-5d).**
`arcCupObstruction_freshDiagram_agrees`: the fresh boundary diagrams of the count-cancel's
refuting witness pair are EQUAL (the forgetting is confined to the internal counts).
`arcCupHeadFolded_offFusedPartner_agrees`: off both window legs, the fresh partners agree
across runs.  What this marker does NOT claim: the MIXED cell (fused in one run, off in the
other) — not refutable by the local pointwise equalities (the cup-count head-contribution
asymmetry is absorbed by the cross-run-incomparable base census), so the general
fresh-diagram agreement routes through the through-the-head trace orbit, not a local cancel.
`= true`. -/
def fxMode_hasArcCupDiagramAgreement : Bool := true

end FX1Poly.Polygraph
