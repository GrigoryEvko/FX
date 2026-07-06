import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupHeadStructure
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupLegSeparationFold

/-! # ArcCupChainedExtract — the cup-head extract with `legsSeparate` discharged (peel campaign H)

The cup-rung capstone `arcCupHeadFolded_extractArc` still carries a `legsSeparate` hypothesis
(the window legs stay fresh-separated).  The loop-freedom payoff
`arcCupHeadFolded_legsSeparate` DERIVES exactly that on the chained fragment at `base` window
parity — but the two were never wired together, so the capstone still demanded the obligation
externally.  This brick composes them: on the chained fragment with a base-parity window, the
composite cup-head extract equals the transported fresh extract with NO separate legs-separated
input.  The legs-connected ("cup-cancel") world is empty on the reconstruction fragment, so the
transport form is the whole story there.

This is purely additive — `arcCupHeadFolded_extractArc` is untouched; the RHS is its transport,
reproduced verbatim so the composition typechecks against it.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The cup-head `FullArcStructure` transport, `legsSeparate` discharged.**  On the chained
fragment with a base-parity window, `arcCupHeadFolded_legsSeparate` supplies the separated legs,
so the capstone transport holds from `(windowFits, windowParityIsBase, chained)` alone — the
legs-connected world is empty here. -/
theorem arcCupHeadFolded_extractArc_ofChained
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat) (windowFits : windowPosition ≤ bottomCount)
    (windowParityIsBase :
      adjunctionModeAtDistance overallSource windowPosition = AdjunctionMode.base)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained (bottomCount + 2) atoms) :
    extractArc bottomCount
        (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms)
      = { diagram :=
            { bottomCount := bottomCount,
              topCount := (extractArc (bottomCount + 2)
                (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] [])
                  atoms)).diagram.topCount,
              partner := (List.range
                  (bottomCount
                    + (processArcSpine
                      (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2)
                        0 [] [])
                      atoms).openWires.length)).map
                (arcCupPartnerTransport
                  (processArcSpine
                    (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                      [] [])
                    atoms).links
                  (List.range (bottomCount + 2)
                    ++ (processArcSpine
                      (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2)
                        0 [] [])
                      atoms).openWires)
                  (bottomCount + 2
                    + (processArcSpine
                      (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2)
                        0 [] [])
                      atoms).openWires.length)
                  windowPosition),
              loops := (extractArc (bottomCount + 2)
                (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] [])
                  atoms)).diagram.loops },
          cupCount := (extractArc (bottomCount + 2)
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms)).cupCount + 1,
          capCount := (extractArc (bottomCount + 2)
            (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              atoms)).capCount,
          internalCupCounts := (List.range
              (bottomCount
                + (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] [])
                  atoms).openWires.length)).map
            (arcCupCountTransport
              (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] [])
                atoms).links
              (List.range (bottomCount + 2)
                ++ (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] [])
                  atoms).openWires)
              (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] [])
                atoms).cupEventNodes
              windowPosition 1),
          internalCapCounts := (List.range
              (bottomCount
                + (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] [])
                  atoms).openWires.length)).map
            (arcCupCountTransport
              (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] [])
                atoms).links
              (List.range (bottomCount + 2)
                ++ (processArcSpine
                  (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                    [] [])
                  atoms).openWires)
              (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0
                  [] [])
                atoms).capEventNodes
              windowPosition 0) } :=
  arcCupHeadFolded_extractArc bottomCount windowPosition windowFits windowParityIsBase atoms
    chained
    (arcCupHeadFolded_legsSeparate bottomCount windowPosition windowFits windowParityIsBase
      atoms chained)

/-! ## Honesty marker -/

/-- **Honesty marker — the cup-head extract with `legsSeparate` discharged (peel campaign H).**
`arcCupHeadFolded_extractArc_ofChained`: the cup-rung capstone transport now holds on the
chained, base-parity-window fragment from `(windowFits, windowParityIsBase, chained)` alone —
the first consumer of `arcCupHeadFolded_legsSeparate`, closing the leg-separation obligation the
reconstruction fragment always satisfies.  What this marker does NOT claim: injectivity of the
transport (the `sameClassification` mixed-free re-selection the orbit supplies), or the
head-location driver discharging `SpineArcHeadExtractionChained`.  `= true`. -/
def fxMode_hasArcCupChainedExtract : Bool := true

end FX1Poly.Polygraph
