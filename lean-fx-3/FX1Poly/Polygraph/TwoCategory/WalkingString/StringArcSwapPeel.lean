import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicSwap
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicSwapBoundary
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.SpineBoundaryChain
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcFreshDecision
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcSwapRenameable
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcBoundaryTracking
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcArity
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcSwapDispatch

/-! # WalkingString/StringArcSwapPeel — the peel: arc extraction along the whole trace equivalence (FC-3 item 1)

The peel induction over `AtomicTraceEquiv` at the walking ADJOINT TRIPLE: trace-equivalent string spines extract
the SAME arc structure from any fresh, forest-rooted, boundary-tracking start state.  This is the direct clone of
the walking-adjunction peel (`extractArc_eq_of_atomicTraceEquiv`), the substrate of which is entirely COLOUR-BLIND
and `{signature}`-generic upstream: the `ofSwap` case dispatches through the four-generator producer
`stringArcSwapCorePackage_of_stringSwap` into the bare-spine rest consumer, with the window-fit premise derived from
the chained boundary; `consCongr` threads all five state invariants through one arc step, discharging the arity
hypothesis via the four-generator classification `adjointTripleSpineAtom_hasCupOrCapArity`; and `symm` / `trans`
recover the flipped / middle chainedness from the boundary-chain transfer.

The ONLY two signature-keyed inputs are the swap-core producer and the arity dispatch — both shipped for the
three-generator seed (`StringArcSwapDispatch`, `StringArcArity`), colour-blind, no length-rigidity — so the whole
peel ports verbatim.  This is FC-3 item 1: the arc-preservation dispatch at the walking adjoint triple.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` gated in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

/-- ★ **The peel (walking adjoint triple).**  Trace-equivalent string spines extract equal arc structures, from
every start state that is fresh, forest-rooted, has positive `nextFresh` bounding the extraction boundary, and whose
open-wire count tracks the spine's chained boundary.  The direct four-generator analog of
`extractArc_eq_of_atomicTraceEquiv`: the swap case fires through `stringArcSwapCorePackage_of_stringSwap`, the
`consCongr` arity hypothesis through `adjointTripleSpineAtom_hasCupOrCapArity`, everything else the colour-blind
generic substrate. -/
theorem extractArc_eq_of_stringAtomicTraceEquiv
    {overallSource overallTarget : adjointTripleModeSignature.graph.Mode}
    {firstList secondList : List (SpineAtom adjointTripleModeSignature overallSource overallTarget)}
    (traceEquiv : AtomicTraceEquiv adjointTripleModeSignature firstList secondList) :
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
            (stringArcSwapCorePackage_of_stringSwap generatorLeft generatorRight
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
          (adjointTripleSpineAtom_hasCupOrCapArity atom) (wiresEq.trans headFires.symm))
        tailChained

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — the arc-preservation PEEL is SHIPPED at the walking adjoint triple (FC-3 item 1).**
`extractArc_eq_of_stringAtomicTraceEquiv`: along ANY `AtomicTraceEquiv` over the walking adjoint triple, the arc
extraction is invariant — every swap dispatches through the four-generator producer
`stringArcSwapCorePackage_of_stringSwap` into the bare-spine rest consumer with the window fit derived from the
chained boundary, and the state invariants (fresh, forest, `nextFresh` positivity/bound, wire-count boundary
tracking) thread through `consCongr`, the arity hypothesis discharged by the colour-blind four-generator
classification `adjointTripleSpineAtom_hasCupOrCapArity`.  This is the DIRECT clone of the adjunction peel
(`extractArc_eq_of_atomicTraceEquiv`): the whole substrate is `{signature}`-generic and colour-blind, and the two
signature-keyed inputs (the swap producer, the arity dispatch) are the shipped three-generator seeds — so item 1
ports with NO length-rigidity.  What this marker does NOT claim: items 2–5 (bubble-to-front, pure-block sort,
valley-append, the Piece-I oracle) or the reconstruction flip; those are the remaining rungs.  `= true`. -/
def fxString_hasArcTraceEquivExtraction : Bool := true

end FX1Poly.Polygraph
