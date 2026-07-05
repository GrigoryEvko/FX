import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCensusPartnerUnique
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcHeadReindex

/-! # ArcCensusCupHeadFolded — the census and its partner pin at the cup geometry's two states (peel campaign H, cup rung 2d-v)

The cup rewiring compares two folds: the COMPOSITE (a cup at the window, then the chained
atoms) and the FRESH run (the canonical seed two ports wider, then the same atoms).  This
brick lands the boundary census at BOTH folded states — the composite via the cup preservation
step then the fold transport, the fresh directly from the canonical-seed capstone — and
instantiates the partner pin at each: at either state, exhibiting one same-component candidate
evaluates the canonical partner.  These are the two evaluation devices the fused-component
rewiring dispatches with.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-! ## Private range plumbing (per-file copy, following the codebase pattern) -/

private theorem rangeLoopLength : (count : Nat) → (accumulated : List Nat) →
    (List.range.loop count accumulated).length = count + accumulated.length
  | 0, accumulated => (Nat.zero_add accumulated.length).symm
  | count + 1, accumulated => by
      have inner := rangeLoopLength count (count :: accumulated)
      show (List.range.loop count (count :: accumulated)).length
        = count + 1 + accumulated.length
      rw [inner]
      show count + (accumulated.length + 1) = count + 1 + accumulated.length
      rw [← Nat.add_assoc count accumulated.length 1,
        Nat.add_right_comm count accumulated.length 1]

private theorem rangeLength (count : Nat) : (List.range count).length = count := by
  show (List.range.loop count []).length = count
  rw [rangeLoopLength count []]
  exact Nat.add_zero count

/-! ## The census at the cup-head folded composite -/

/-- ★ **The boundary census holds at the cup-head folded composite**: the seed census
survives the head cup (the cup preservation step at the in-range window) and then the whole
chained fold (the fold transport, tracking the boundary through the cup's two extra ports). -/
theorem arcBoundaryCensus_cupHeadFolded
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat)
    (windowFits : windowPosition ≤ bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained (bottomCount + 2) atoms) :
    ArcBoundaryCensus bottomCount
      (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms) := by
  have seedCupInRange : windowPosition ≤ (List.range bottomCount).length := by
    rw [rangeLength bottomCount]
    exact windowFits
  have headCensus : ArcBoundaryCensus bottomCount
      (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        windowPosition) :=
    arcBoundaryCensus_stepCupArc bottomCount
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition
      (arcStateFresh_initial bottomCount) isUnionFindForest_nil
      (Nat.le_refl bottomCount) seedCupInRange
      (arcBoundaryCensus_initial bottomCount)
  exact arcBoundaryCensus_processArcSpine_ofChained atoms
    (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      windowPosition) (bottomCount + 2) bottomCount
    (stepCupArc_arcStateFresh
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition
      (arcStateFresh_initial bottomCount))
    (isUnionFindForest_stepCupArc
      (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] []) windowPosition
      isUnionFindForest_nil)
    (cupHeadOpenWires_length bottomCount windowPosition)
    chained
    (Nat.le_add_right bottomCount 3)
    headCensus

/-! ## The partner pins at the two folded states -/

/-- ★ The partner pin at the CUP-HEAD FOLDED COMPOSITE: exhibiting one same-component
candidate evaluates the composite's canonical partner. -/
theorem arcCupHeadFolded_partner_ofSameComponent
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat)
    (windowFits : windowPosition ≤ bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained (bottomCount + 2) atoms)
    (excludeIndex partnerCandidate : Nat)
    (excludeInRange : excludeIndex
      < bottomCount
        + (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires.length)
    (candidateInRange : partnerCandidate
      < bottomCount
        + (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires.length)
    (candidateNeExclude : partnerCandidate ≠ excludeIndex)
    (sameReads : isSameComponent
      (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (natListGetAt
        (List.range bottomCount
          ++ (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires) excludeIndex)
      (natListGetAt
        (List.range bottomCount
          ++ (processArcSpine
            (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
              windowPosition) atoms).openWires) partnerCandidate) = true) :
    partnerIndexOf
      (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links
      (List.range bottomCount
        ++ (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires)
      (bottomCount
        + (processArcSpine
          (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
            windowPosition) atoms).openWires.length)
      excludeIndex = partnerCandidate :=
  partnerIndexOf_uniqueSameComponent bottomCount
    (processArcSpine
      (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
        windowPosition) atoms)
    (arcBoundaryCensus_cupHeadFolded bottomCount windowPosition windowFits atoms chained)
    excludeIndex partnerCandidate excludeInRange candidateInRange candidateNeExclude
    sameReads

/-- ★ The partner pin at the FRESH FOLDED state (the canonical seed two ports wider):
exhibiting one same-component candidate evaluates the fresh run's canonical partner. -/
theorem arcFreshFolded_partner_ofSameComponent
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount : Nat)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained (bottomCount + 2) atoms)
    (excludeIndex partnerCandidate : Nat)
    (excludeInRange : excludeIndex
      < bottomCount + 2
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length)
    (candidateInRange : partnerCandidate
      < bottomCount + 2
        + (processArcSpine
          (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
          atoms).openWires.length)
    (candidateNeExclude : partnerCandidate ≠ excludeIndex)
    (sameReads : isSameComponent
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links
      (natListGetAt
        (List.range (bottomCount + 2)
          ++ (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).openWires) excludeIndex)
      (natListGetAt
        (List.range (bottomCount + 2)
          ++ (processArcSpine
            (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
            atoms).openWires) partnerCandidate) = true) :
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
      excludeIndex = partnerCandidate :=
  partnerIndexOf_uniqueSameComponent (bottomCount + 2)
    (processArcSpine
      (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] []) atoms)
    (arcBoundaryCensus_ofChainedSpineList (bottomCount + 2) atoms chained)
    excludeIndex partnerCandidate excludeInRange candidateInRange candidateNeExclude
    sameReads

/-- **Honesty marker — the folded census instances and their partner pins are SHIPPED (peel
campaign H, cup rung 2d-v).**  The census at the cup-head folded composite
(`arcBoundaryCensus_cupHeadFolded` — seed census through the head cup and the chained fold)
and the ready-to-dispatch partner pins at both states of the cup geometry
(`arcCupHeadFolded_partner_ofSameComponent` / `arcFreshFolded_partner_ofSameComponent`).
What this marker does NOT claim: the fused-component candidate exhibition itself (the joined
same-component chain through the cup legs) and the cup-cancellation endgame.  `= true`. -/
def fxMode_hasArcCensusCupHeadFolded : Bool := true

end FX1Poly.Polygraph
