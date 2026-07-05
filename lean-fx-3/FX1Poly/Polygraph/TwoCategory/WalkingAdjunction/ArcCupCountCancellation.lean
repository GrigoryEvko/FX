import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcHeadFoldedSim

/-! # ArcCupCountCancellation — the unconditional count legs of the cup partial cancel

The cup-head cancellation is REFUTED in full (`not_arcCupHeadCancellationUnconditional`):
the composite run joins the peeled cup's legs, so the per-strand internal counts forget the
leg-split.  But the COUNT legs survive, and they survive UNCONDITIONALLY — no chain
discipline, no leg separation, no window parity: two tails over the same peeled cup with
equal composite extracts have equal fresh boundary widths, equal fresh cup totals (the
composite counts the head's own event on both sides, and the extra event peels off), and
equal fresh cap totals.  Each leg is a projection of the composite equality rewritten
through the positional-simulation length lemmas.

These are the invariant base data the orbit realignment starts from: whatever second tail
realizes the same composite, its fresh run already agrees on every total — only the
partner matching (parity-gated) and the internal leg-split (orbit-gated) remain.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- **The cup-total cancel**: equal composite extracts over the same peeled cup force equal
FRESH cup-event totals — both composites count the head's own cup event, and the extra
`+ 1` peels off by successor injectivity. -/
theorem arcCupHeadFolded_cupTotal_cancel
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat)
    (firstAtoms secondAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (compositeEq : extractArc bottomCount
        (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) firstAtoms)
      = extractArc bottomCount
          (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) secondAtoms)) :
    (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        firstAtoms).cupEventNodes.length
      = (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          secondAtoms).cupEventNodes.length := by
  have compositeCupTotals : (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) firstAtoms).cupEventNodes.length
      = (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) secondAtoms).cupEventNodes.length :=
    congrArg FullArcStructure.cupCount compositeEq
  rw [arcCupHeadFolded_cupEventsLength bottomCount windowPosition firstAtoms,
    arcCupHeadFolded_cupEventsLength bottomCount windowPosition secondAtoms]
    at compositeCupTotals
  exact Nat.succ.inj compositeCupTotals

/-- **The cap-total cancel**: equal composite extracts over the same peeled cup force equal
FRESH cap-event totals — the cup head records no cap event, so the composite totals ARE the
fresh totals. -/
theorem arcCupHeadFolded_capTotal_cancel
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat)
    (firstAtoms secondAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (compositeEq : extractArc bottomCount
        (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) firstAtoms)
      = extractArc bottomCount
          (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) secondAtoms)) :
    (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        firstAtoms).capEventNodes.length
      = (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          secondAtoms).capEventNodes.length := by
  have compositeCapTotals : (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) firstAtoms).capEventNodes.length
      = (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) secondAtoms).capEventNodes.length :=
    congrArg FullArcStructure.capCount compositeEq
  rw [arcCupHeadFolded_capEventsLength bottomCount windowPosition firstAtoms,
    arcCupHeadFolded_capEventsLength bottomCount windowPosition secondAtoms]
    at compositeCapTotals
  exact compositeCapTotals

/-- **The width cancel**: equal composite extracts over the same peeled cup force equal
FRESH boundary widths — the composite top count reads the fresh top count on both sides
through the positional simulation. -/
theorem arcCupHeadFolded_topCount_cancel
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat)
    (firstAtoms secondAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (compositeEq : extractArc bottomCount
        (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) firstAtoms)
      = extractArc bottomCount
          (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) secondAtoms)) :
    (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        firstAtoms).openWires.length
      = (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          secondAtoms).openWires.length := by
  have compositeWidths : (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) firstAtoms).openWires.length
      = (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) secondAtoms).openWires.length :=
    congrArg (fun arcData => arcData.diagram.topCount) compositeEq
  rw [arcCupHeadFolded_openWiresLength bottomCount windowPosition firstAtoms,
    arcCupHeadFolded_openWiresLength bottomCount windowPosition secondAtoms]
    at compositeWidths
  exact compositeWidths

/-! ## Honesty marker -/

/-- **Honesty marker — the unconditional count legs of the cup partial cancel are SHIPPED
(peel campaign H, the orbit base data).**  `arcCupHeadFolded_cupTotal_cancel` /
`arcCupHeadFolded_capTotal_cancel` / `arcCupHeadFolded_topCount_cancel`: two tails over the
same peeled cup with equal composite extracts have equal fresh cup totals, cap totals, and
boundary widths — with NO chain, separation, or parity hypotheses.  What this marker does
NOT claim: the partner-matching cancel (the leg-swap scenario is only excluded by strand
parity — needs the arc-endpoint parity invariant on the chained fragment), the
internal-count cancel (REFUTED — `not_arcCupHeadCancellationUnconditional`), and the orbit
realignment, cup-front locate, and cup-head discharge above them.  `= true`. -/
def fxMode_hasArcCupCountCancellation : Bool := true

end FX1Poly.Polygraph
