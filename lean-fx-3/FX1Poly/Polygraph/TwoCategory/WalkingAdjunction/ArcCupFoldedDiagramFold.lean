import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupFoldedPartnerAgreement
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingMapCongruence
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcPartitionCommute

/-! # ArcCupFoldedDiagramFold — folding the per-index cup-head partner cancel into the whole diagram partner list

`arcCupFoldedPartner_agrees_ofSameClassification` (peel campaign H, rung P-5e) proves the two chained runs' fresh
partner values COINCIDE at a single composite index, under a same-classification precondition at that index.  The
diagram field of `tailsCancel` needs the WHOLE partner list to agree — and a `DiagramType.partner` list is exactly
`(List.range total).map (partnerIndexOf …)`, so a pointwise agreement over the composite range folds into the
list equality by `natMapCongrOfMemAgree` (the propext-free `Nat`-list map congruence).

This brick ships two pieces:

  * `natRangeMapCongr` — the reusable range-map congruence: two `Nat`-maps that agree on every index below a bound
    map `List.range bound` to the same list.  This is the fold combinator every "pointwise-agreement over the
    composite range ⇒ whole-field equality" leg of the cup discharge consumes (diagram partners here, internal
    counts next);
  * `arcCupFoldedDiagramPartnerList_agrees` — the concrete diagram leg: given the per-index fresh-partner agreement
    across the whole composite range (the discharged conclusion of the per-index lemma), the two folded partner
    lists — mapped through `freshShiftAbove` — are equal.  The orbit supplies the per-index agreement pointwise by
    running `arcCupFoldedPartner_agrees_ofSameClassification` at each index of a mixed-free second spine.

What this brick does NOT do: produce the pointwise agreement itself (that is the per-index lemma under the orbit's
`sameClassification`), nor the folded↔clean transport that carries this folded-level equality down to the clean
`bottomCount + 2` seed the `FullArcStructure` diagram field lives at.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The range-map congruence.**  Two `Nat → Nat` maps that agree on every index strictly below `bound` send
`List.range bound` to the same list.  A four-line composite: `mem_range_imp_lt` turns each `value ∈ List.range
bound` membership into the `value < bound` bound the pointwise hypothesis needs, and `natMapCongrOfMemAgree` folds
the resulting per-element agreement structurally over the list — no `∈`-iff lemma, no `propext`. -/
theorem natRangeMapCongr (firstMap secondMap : Nat → Nat) (bound : Nat)
    (agree : ∀ index, index < bound → firstMap index = secondMap index) :
    (List.range bound).map firstMap = (List.range bound).map secondMap :=
  natMapCongrOfMemAgree firstMap secondMap (List.range bound)
    (fun value valueInRange => agree value (mem_range_imp_lt valueInRange))

/-- ★ **The folded diagram partner list agrees, given per-index agreement over the whole composite range.**  With
the two chained runs' fresh partner values coinciding at every composite index below the running range bound
(`bottomCount + firstAtoms`'s open-wire count), the two folded partner lists — each `List.range …` mapped through
the `freshShiftAbove`-shifted `partnerIndexOf` readoff — are equal.  A direct instance of `natRangeMapCongr` at the
two folded readoff maps.  The pointwise hypothesis is exactly the discharged conclusion of
`arcCupFoldedPartner_agrees_ofSameClassification`, so the orbit closes this leg by running that per-index lemma at
each index of a mixed-free second spine. -/
theorem arcCupFoldedDiagramPartnerList_agrees
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat)
    (firstAtoms secondAtoms :
      List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (pointwiseAgree : ∀ compositeIndex,
      compositeIndex < bottomCount
          + (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            firstAtoms).openWires.length →
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
            (freshShiftAbove windowPosition 2 compositeIndex)) :
    (List.range
          (bottomCount
            + (processArcSpine
              (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
              firstAtoms).openWires.length)).map
        (fun compositeIndex =>
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
            (freshShiftAbove windowPosition 2 compositeIndex))
      = (List.range
            (bottomCount
              + (processArcSpine
                (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
                firstAtoms).openWires.length)).map
          (fun compositeIndex =>
            partnerIndexOf
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
              (freshShiftAbove windowPosition 2 compositeIndex)) :=
  natRangeMapCongr _ _ _ pointwiseAgree

/-! ## Honesty markers -/

/-- **Honesty marker — the range-map congruence fold combinator is SHIPPED.**  `natRangeMapCongr`: two `Nat`-maps
agreeing below a bound map `List.range bound` identically (`mem_range_imp_lt` + `natMapCongrOfMemAgree`, propext-free).
This is the reusable fold every pointwise-agreement leg of the cup-head discharge consumes.  `= true`. -/
def fxMode_hasNatRangeMapCongr : Bool := true

/-- **Honesty marker — the folded diagram partner-list agreement is SHIPPED (peel campaign H).**
`arcCupFoldedDiagramPartnerList_agrees`: from the per-index fresh-partner agreement over the whole composite range,
the two folded partner lists coincide — the diagram leg of `tailsCancel` at the folded level.  What this marker does
NOT claim: the per-index agreement itself (the per-index lemma under the orbit's `sameClassification`), nor the
folded↔clean transport down to the `bottomCount + 2` seed.  `= true`. -/
def fxMode_hasArcCupFoldedDiagramFold : Bool := true

end FX1Poly.Polygraph
