import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcComponentShiftFold
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupSeedCorr
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCapSeedCorr

/-! # ArcHeadFoldedCorr — the component correspondence at the folded end states

The head-cancellation component invariant, END TO END: the seed pair (canonical composite
state with the peeled head fired, versus the fresh tail seed at the head's target boundary)
enters the whole-spine fold, and the correspondence emerges at the two runs' final links.
One theorem per head shape — the cup (legs at the window pair, allocator one ahead) and the
cap (degenerate legs, allocator three ahead) — each a single application of the fold at its
seed simulation, seed correspondence, seed forests, and seed translation law.

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

/-! ## The folded correspondences -/

/-- ★ **The cup-head correspondence at the folded end states**: running any boundary-chained
tail spine from the composite seed (peeled cup fired) and the fresh tail seed keeps every
`sigma`-image component query answering as the tail run with the window pair joined first. -/
theorem arcComponentShiftCorr_cupHeadFolded
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition : Nat) (windowFits : windowPosition ≤ bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained (bottomCount + 2) atoms) :
    ArcComponentShiftCorr
      (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
        [bottomCount, bottomCount + 1]) 1)
      windowPosition (windowPosition + 1)
      (processArcSpine
        (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
        atoms).links
      (processArcSpine
        (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links :=
  arcComponentShiftCorr_processArcSpine
    (arcHeadReindex (natListInsertAt (List.range bottomCount) windowPosition
      [bottomCount, bottomCount + 1]) 1)
    1 (bottomCount + 2) [bottomCount + 2] [] windowPosition (windowPosition + 1)
    (arcHeadReindex_cupSeedShifts bottomCount windowPosition)
    atoms
    (ArcWireState.mk (List.range (bottomCount + 2)) [] (bottomCount + 2) 0 [] [])
    (stepCupArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      windowPosition)
    (bottomCount + 2)
    (rangeLength (bottomCount + 2))
    chained
    (arcPositionalShiftSim_cupHeadSeed bottomCount windowPosition)
    isUnionFindForest_nil
    (isUnionFindForest_unionFindJoin
      (unionFindJoin [] bottomCount (bottomCount + 1)) (bottomCount + 2) bottomCount
      (isUnionFindForest_unionFindJoin [] bottomCount (bottomCount + 1)
        isUnionFindForest_nil))
    (arcComponentShiftCorr_cupHeadSeedState bottomCount windowPosition windowFits)

/-- ★ **The cap-head correspondence at the folded end states**: running any boundary-chained
tail spine from the composite seed (peeled cap fired) and the fresh tail seed keeps every
`sigma`-image component query answering as the tail run outright — degenerate legs, since
the cap consumed the pair the tail never sees. -/
theorem arcComponentShiftCorr_capHeadFolded
    {overallSource overallTarget : adjunctionGraph.Mode}
    (bottomCount windowPosition tailBoundary : Nat)
    (windowFits : windowPosition + 2 ≤ bottomCount)
    (tailBoundaryFits : tailBoundary + 2 = bottomCount)
    (atoms : List (SpineAtom adjunctionModeSignature overallSource overallTarget))
    (chained : SpineBoundaryChained tailBoundary atoms) :
    ArcComponentShiftCorr
      (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3)
      0 0
      (processArcSpine
        (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] []) atoms).links
      (processArcSpine
        (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
          windowPosition) atoms).links :=
  arcComponentShiftCorr_processArcSpine
    (arcHeadReindex (natListRemoveTwoAt (List.range bottomCount) windowPosition) 3)
    3 tailBoundary [] [bottomCount] 0 0
    (arcHeadReindex_capSeedShifts bottomCount windowPosition tailBoundary windowFits
      tailBoundaryFits)
    atoms
    (ArcWireState.mk (List.range tailBoundary) [] tailBoundary 0 [] [])
    (stepCapArc (ArcWireState.mk (List.range bottomCount) [] bottomCount 0 [] [])
      windowPosition)
    tailBoundary
    (rangeLength tailBoundary)
    chained
    (arcPositionalShiftSim_capHeadSeed bottomCount windowPosition tailBoundary windowFits
      tailBoundaryFits)
    isUnionFindForest_nil
    (isUnionFindForest_unionFindJoin
      (unionFindJoin [] (natListGetAt (List.range bottomCount) windowPosition)
        (natListGetAt (List.range bottomCount) (windowPosition + 1)))
      bottomCount (natListGetAt (List.range bottomCount) windowPosition)
      (isUnionFindForest_unionFindJoin []
        (natListGetAt (List.range bottomCount) windowPosition)
        (natListGetAt (List.range bottomCount) (windowPosition + 1))
        isUnionFindForest_nil))
    (arcComponentShiftCorr_capHeadSeedState bottomCount windowPosition tailBoundary
      windowFits tailBoundaryFits)

/-! ## Honesty marker -/

/-- **Honesty marker — the head-cancellation component correspondence at the FOLDED end
states (peel campaign H, fold rung CLOSED).**  Both head shapes: the cup-head and cap-head
seed pairs threaded through the whole-spine component fold over any boundary-chained tail
spine, yielding `ArcComponentShiftCorr` at the two runs' final links.  What this marker does
NOT claim: the extract correspondence (translating the links correspondence into equal
`FullArcStructure` extractions — the loops legs ride the loop-freedom invariant) and the
head-cancellation assembly itself.  `= true`. -/
def fxMode_hasArcHeadFoldedCorr : Bool := true

end FX1Poly.Polygraph
