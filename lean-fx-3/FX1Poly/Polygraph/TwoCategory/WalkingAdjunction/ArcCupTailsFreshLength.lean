import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcHeadFoldedSim

/-! # ArcCupTailsFreshLength — the two tails share a fresh boundary length (peel campaign H)

The cup-head `tailsCancel` compares two spines' FRESH arc structures at boundary `bottomCount + 2`
(`arcStructureOfSpineList (bottomCount+2) tailList` vs the bubbled remainder).  Any per-port list
leg (partner / internal cup / internal cap) is a `map` over `List.range (bottomCount + 2 +
openWires.length)`, so the two lists live over the SAME range only once the two tails agree on
their fresh top-boundary length.  That agreement is a clean consequence of `compositeEq` alone:
the cup head leaves the top boundary length unchanged (`arcCupHeadFolded_openWiresLength`), and the
composite extracts agree on `diagram.topCount` (which IS the top-wire count, definitionally).  No
window parity, no legs-separated hypothesis — a pure length prerequisite for the list folds.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The two tails share a fresh top-boundary length.**  From the composite-extract equality
(the peeled cup at the window, then each tail) the two tails' fresh runs at boundary `bottomCount +
2` produce the same number of open wires: the cup head preserves the top-wire count
(`arcCupHeadFolded_openWiresLength`), and `compositeEq` forces the composite `diagram.topCount` —
definitionally the open-wire count — to agree. -/
theorem arcCupTails_freshOpenWiresLength_ofCompositeEq
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
  rw [← arcCupHeadFolded_openWiresLength bottomCount windowPosition firstAtoms,
    ← arcCupHeadFolded_openWiresLength bottomCount windowPosition secondAtoms]
  exact congrArg (fun arcStructure => arcStructure.diagram.topCount) compositeEq

/-! ## Honesty marker -/

/-- **Honesty marker — the two tails share a fresh boundary length (peel campaign H).**
`arcCupTails_freshOpenWiresLength_ofCompositeEq`: from the composite-extract equality the two cup
tails' fresh runs at `bottomCount + 2` produce equal open-wire counts — the length prerequisite
every per-port `tailsCancel` list fold (partner / internal cup / internal cap) needs so its two
`List.range`-indexed maps live over one range.  Pure `compositeEq` consequence, no parity or
legs-separated input.  What this marker does NOT claim: the list folds themselves, or the
`sameClassification` mixed-free re-selection they are gated on.  `= true`. -/
def fxMode_hasArcCupTailsFreshLength : Bool := true

end FX1Poly.Polygraph
