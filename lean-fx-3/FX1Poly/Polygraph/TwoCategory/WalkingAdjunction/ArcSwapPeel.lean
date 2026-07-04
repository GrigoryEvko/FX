import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicSwap
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicSwapBoundary
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineBoundaryChain
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcFreshDecision
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapCorePackage
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapRenameable
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcBoundaryTracking

/-! # WalkingAdjunction/ArcSwapPeel — the peel: arc extraction along the whole trace equivalence

The peel induction over `AtomicTraceEquiv` at the walking adjunction: trace-equivalent spines
extract the SAME arc structure from any fresh, forest-rooted, boundary-tracking start state.
Each case rides a shipped ingredient — a realized swap goes through the atom-level dispatcher
(`arcSwapCorePackage_of_adjunctionSwap`) into the bare-spine rest consumer, with the window-fit
premise derived from the chained boundary; `consCongr` threads all five state invariants
through one arc step (freshness, forest, positivity, boundary bound, wire-count tracking); and
`symm` / `trans` recover the flipped / middle chainedness from the boundary-chain transfer.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The peel.**  Trace-equivalent spines over the walking adjunction extract equal arc
structures, from every start state that is fresh, forest-rooted, has positive `nextFresh`
bounding the extraction boundary, and whose open-wire count tracks the spine's chained
boundary. -/
theorem extractArc_eq_of_atomicTraceEquiv
    {overallSource overallTarget : adjunctionModeSignature.graph.Mode}
    {firstList secondList : List (SpineAtom adjunctionModeSignature overallSource overallTarget)}
    (traceEquiv : AtomicTraceEquiv adjunctionModeSignature firstList secondList) :
    ∀ (state : ArcWireState) (bottomCount boundaryLength : Nat),
      ArcStateFresh state → isUnionFindForest state.links →
      0 < state.nextFresh → bottomCount ≤ state.nextFresh →
      state.openWires.length = boundaryLength →
      SpineBoundaryChained boundaryLength firstList →
      extractArc bottomCount (processArcSpine state firstList)
        = extractArc bottomCount (processArcSpine state secondList) := by
  induction traceEquiv with
  | ofSwap swapStep =>
      cases swapStep with
      | @swap swapSourceMode swapMiddleLeft swapMiddleRight swapTargetMode
          oneCellFMid oneCellFHigh oneCellGLow oneCellGMid
          generatorLeft generatorRight leftAcc inertPath rightAcc rest =>
          intro state bottomCount boundaryLength fresh forest nextFreshPos boundaryBelowFresh
            wiresEq chained
          obtain ⟨headFires, _⟩ := spineBoundaryChained_tail chained
          have headFlat : leftAcc.length + oneCellFMid.length
              + (composePath (composePath inertPath oneCellGLow) rightAcc).length
              = boundaryLength := headFires
          rw [composePath_length_double inertPath oneCellGLow rightAcc,
            natSumFive_ofNestedTail leftAcc.length oneCellFMid.length inertPath.length
              oneCellGLow.length rightAcc.length] at headFlat
          have windowsFit : leftAcc.length + oneCellFMid.length + inertPath.length
              + oneCellGLow.length ≤ state.openWires.length := by
            rw [wiresEq, ← headFlat]
            exact Nat.le_add_right
              (leftAcc.length + oneCellFMid.length + inertPath.length + oneCellGLow.length)
              rightAcc.length
          exact extractArc_eq_rest_of_swapCorePackage bottomCount _ _
            (arcSwapCorePackage_of_adjunctionSwap generatorLeft generatorRight
              leftAcc inertPath rightAcc state fresh forest nextFreshPos
              bottomCount boundaryBelowFresh windowsFit) rest
  | refl _ => exact fun _ _ _ _ _ _ _ _ _ => rfl
  | symm innerEquiv innerHypothesis =>
      intro state bottomCount boundaryLength fresh forest nextFreshPos boundaryBelowFresh
        wiresEq chained
      exact (innerHypothesis state bottomCount boundaryLength fresh forest nextFreshPos
        boundaryBelowFresh wiresEq
        ((spineBoundaryChained_iff_of_atomicTraceEquiv innerEquiv boundaryLength).mpr
          chained)).symm
  | trans leftEquiv _ leftHypothesis rightHypothesis =>
      intro state bottomCount boundaryLength fresh forest nextFreshPos boundaryBelowFresh
        wiresEq chained
      exact (leftHypothesis state bottomCount boundaryLength fresh forest nextFreshPos
          boundaryBelowFresh wiresEq chained).trans
        (rightHypothesis state bottomCount boundaryLength fresh forest nextFreshPos
          boundaryBelowFresh wiresEq
          ((spineBoundaryChained_iff_of_atomicTraceEquiv leftEquiv boundaryLength).mp chained))
  | consCongr atom _ tailHypothesis =>
      intro state bottomCount boundaryLength fresh forest nextFreshPos boundaryBelowFresh
        wiresEq chained
      obtain ⟨headFires, tailChained⟩ := spineBoundaryChained_tail chained
      exact tailHypothesis (stepArcAtom state atom) bottomCount atom.codBoundaryLength
        (arcStateFresh_stepArcAtom state atom fresh)
        (isUnionFindForest_stepArcAtom state atom forest)
        (Nat.lt_of_lt_of_le nextFreshPos (stepArcAtom_nextFresh_le state atom))
        (Nat.le_trans boundaryBelowFresh (stepArcAtom_nextFresh_le state atom))
        (stepArcAtom_openWires_tracksBoundary state atom
          (adjunctionSpineAtom_hasCupOrCapArity atom) (wiresEq.trans headFires.symm))
        tailChained

/-- **Honesty marker — the PEEL is SHIPPED.**  `extractArc_eq_of_atomicTraceEquiv`: along ANY
`AtomicTraceEquiv` over the walking adjunction, the arc extraction is invariant — every swap
dispatches through `arcSwapCorePackage_of_adjunctionSwap` into the bare-spine rest consumer
with the window fit derived from the chained boundary, and the state invariants (fresh, forest,
`nextFresh` positivity/bound, wire-count boundary tracking) thread through `consCongr`.
What this marker does NOT claim: the ARC-4 reconstruction flip
(`fxMode_hasArcCellReconstruction`) — connecting this trace-equivalence invariance to the
matching-based reconstruction statement is the remaining rung. -/
def fxMode_hasArcTraceEquivExtraction : Bool := true

end FX1Poly.Polygraph
