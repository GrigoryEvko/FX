import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupFoldedDiagramFold
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupFoldedPartnerAgreement

/-! # ArcCupDiagramSameClassificationFold — the diagram partner list agrees from `sameClassification` at
every index (peel campaign H)

The diagram leg of the cup tails-cancel splits into two shipped halves that were never wired together:

  * `arcCupFoldedPartner_agrees_ofSameClassification` (ArcCupFoldedPartnerAgreement) — the PER-INDEX
    agreement: at one composite index, given the leg-attachment `sameClassification` iff (the fresh partner
    lands on a head window-leg in the first run exactly when in the second), the two fresh partner values
    coincide;
  * `arcCupFoldedDiagramPartnerList_agrees` (ArcCupFoldedDiagramFold) — the FOLD: a per-index partner
    agreement over the whole composite range lifts to the full partner-LIST equality.

This brick composes them: with `sameClassification` supplied at EVERY index (and the two runs sharing a
fresh boundary length, an easy consequence of the composite equality the orbit already carries), the whole
diagram partner list agrees.  So the diagram leg of the cup tails-cancel now rests on EXACTLY one crisp,
named residual — `∀ index, arcCupFreshPartnerLandsOnWindowLeg firstAtoms index ↔ … secondAtoms index` —
which is precisely the through-the-head trace orbit's target (a mixed-free second spine): the re-selection
chooses the cup whose leg-attachment classification matches the head's at every port.

Raw Lean 4 + Init; a fold over the shipped per-index agreement, the fresh-boundary-length bridge threaded
by the composite equality; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- **The leg-attachment classifier for one run at one composite index.**  The fresh partner of the given
composite index (shifted above the head's two fresh legs by `freshShiftAbove windowPosition 2`) lands on
one of the head's two window legs — `windowPosition` or `windowPosition + 1`.  The `sameClassification`
precondition of `arcCupFoldedPartner_agrees_ofSameClassification` is exactly the iff of this predicate
between the two runs; naming it makes the diagram leg's residual a single readable proposition. -/
def arcCupFreshPartnerLandsOnWindowLeg
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (compositeIndex : Nat) : Prop :=
  partnerIndexOf
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links
      (List.range (bottomCount + 2)
        ++ (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires)
      (bottomCount + 2
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length)
      (freshShiftAbove windowPosition 2 compositeIndex) = windowPosition
    ∨ partnerIndexOf
        (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).links
        (List.range (bottomCount + 2)
          ++ (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).openWires)
        (bottomCount + 2
          + (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).openWires.length)
        (freshShiftAbove windowPosition 2 compositeIndex) = windowPosition + 1

/-- ★ **The folded diagram partner list agrees from `sameClassification` at every index.**  With the head
legs fresh-separated in both runs, the composite extracts equal, the two runs sharing a fresh boundary
length, and the leg-attachment classification agreeing at every composite index
(`arcCupFreshPartnerLandsOnWindowLeg` iff), the whole transported partner list of the first run equals that
of the second: run the shipped per-index agreement at each index, fold over the range.  The diagram leg of
the cup tails-cancel is thereby reduced to EXACTLY the per-index `sameClassification` supply — the through-
the-head orbit's target. -/
theorem arcCupFoldedDiagramPartnerList_agrees_ofSameClassification
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
    (freshLengthAgree :
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        firstAtoms).openWires.length
      = (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          secondAtoms).openWires.length)
    (sameClassificationAll : ∀ compositeIndex,
      compositeIndex < bottomCount
          + (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            firstAtoms).openWires.length →
      (arcCupFreshPartnerLandsOnWindowLeg bottomCount windowPosition firstAtoms compositeIndex
        ↔ arcCupFreshPartnerLandsOnWindowLeg bottomCount windowPosition secondAtoms compositeIndex)) :
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
              (freshShiftAbove windowPosition 2 compositeIndex)) := by
  apply arcCupFoldedDiagramPartnerList_agrees bottomCount windowPosition firstAtoms secondAtoms
  intro compositeIndex indexInRangeFirst
  have indexInRangeSecond : compositeIndex < bottomCount
      + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          secondAtoms).openWires.length := by
    rw [← freshLengthAgree]; exact indexInRangeFirst
  exact arcCupFoldedPartner_agrees_ofSameClassification bottomCount windowPosition windowFits
    firstAtoms secondAtoms firstChained secondChained firstLegsSeparate secondLegsSeparate
    compositeEq compositeIndex indexInRangeFirst indexInRangeSecond
    (sameClassificationAll compositeIndex indexInRangeFirst)

/-! ## Honesty marker -/

/-- **Honesty marker — the diagram partner list agrees from per-index `sameClassification` (peel campaign
H).**  `arcCupFoldedDiagramPartnerList_agrees_ofSameClassification` composes the shipped per-index
leg-attachment agreement with the shipped range fold: given the leg-attachment classification iff at every
composite index (plus fresh-separated legs, equal composites, and the two runs' shared fresh boundary
length), the whole transported partner list agrees.  So the cup tails-cancel's DIAGRAM leg is reduced to
exactly one crisp residual — `∀ index, arcCupFreshPartnerLandsOnWindowLeg firstAtoms index ↔ … secondAtoms
index` — the through-the-head trace orbit's mixed-free target.  What this marker does NOT claim: that
per-index residual itself (the orbit re-selection supplies it by choosing the leg-matched cup), the two
INTERNAL count legs' analogous fold, nor the folded↔clean transport down to the seed.  `= true`. -/
def fxMode_hasArcCupDiagramSameClassificationFold : Bool := true

end FX1Poly.Polygraph
