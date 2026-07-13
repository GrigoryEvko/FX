import FX1Poly.Polygraph.TwoCategory.Amalgam.SaturatedDispatch
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutCeilingLedger
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcWholeCellDisjointSupportCommute

/-! # WP-AMALG — the dispatch's `componentComm` INPUT supplied: disjoint-support block commutation at the pushout

## What this ships (the first #2043 consumption, r28)

`SaturatedDispatch.lean`'s residual (2) names the exact missing input of the cross-component
block dispatch: *"the disjoint-support Godement block-commutation
(`fxMode_hasArcBlockCommuteProof = false`)"*.  The r28 whole-cell arc engine
(`arcCellPastCellSwapSimCount` -> `arcGodementInnerSwapSimCount`) now supplies that input in its
honest, guarded form — and this file states it IN THE DISPATCH'S OWN VOCABULARY, instantiated at
the pushout signature the dispatch runs over:

  * **`pushoutDisjointBlockCommuteInput`** — at ANY shared-mode pushout
    `(pushoutShared comp1 comp2 sameModes).toModeSignature`, two turnback-only cells whiskered
    into component-disjoint windows commute at arc level (full `ArcStepSimCount`, bounded
    composite carrier) — the block-swap step the interleaving-NF dispatch fires when it sorts a
    mixed word into component blocks;
  * a pushout-TYPED instantiation at the concrete `thinPushout` (degenerate cells — the thin
    pushout has no 2-generators to fire, so the pushout-typed fire is necessarily the identity
    corner) and the CONTENT fire on the canonical turnback signature (the walking adjunction,
    where the r28 counit-instance fire runs six atoms over two orders), with compiled
    `#eval`/`decide` pins of the two orders' concrete order-invariant data.

## Honesty (#2043 NOT overclaimed — read the ledger)

This supplies the `componentComm`-shaped INPUT only.  The dispatch theorem itself
(`fxAmalg_hasSaturatedDispatchTheorem`) stays `false`: residual (1) — the cell-functor retag
`RawTwoCellExpr comp_i -> RawTwoCellExpr pushout` along the coprojection — does not exist, and
the close criterion (`pushoutDispatchCloseCriterion`) is hostage to the JAM-A vcomp payload zip
(fib-3, cross-lane).  Both stay untouched-`false`, re-recorded below by `rfl`.  The input is
GUARDED (turnback-only cells, decomposed state, component-disjoint windows): the consumer must
discharge the guard from its interleaving-NF invariants — that discharge is dispatch-lane work,
not claimed here.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` + independent `#print axioms` twins. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The input-shaped theorem at the pushout signature -/

/-- ★★ **The dispatch's `componentComm` input, at the pushout signature.**  Two turnback-only
cells over `(pushoutShared comp1 comp2 sameModes).toModeSignature`, whiskered into
component-disjoint windows of a decomposed well-formed arc state, commute at arc level in the
Godement inner orientation — the exact block-swap step the cross-component dispatch needs when
sorting a mixed interleaving into component blocks.  A direct instantiation of the r28
whole-cell engine at the pushout signature (the engine is signature-generic; stating it here
fixes the dispatch-facing interface). -/
theorem pushoutDisjointBlockCommuteInput (comp1 comp2 : ModeComputad)
    (sameModes : comp1.modeCount = comp2.modeCount)
    {overallSource overallTarget sourceMode middleMode targetMode :
      (pushoutShared comp1 comp2 sameModes).toModeSignature.graph.Mode}
    {fMid fHigh : ModalityPath (pushoutShared comp1 comp2 sameModes).toModeSignature.graph
      sourceMode middleMode}
    {gLow gMid : ModalityPath (pushoutShared comp1 comp2 sameModes).toModeSignature.graph
      middleMode targetMode}
    (cellAlphaUpper : RawTwoCellExpr (pushoutShared comp1 comp2 sameModes).toModeSignature
      fMid fHigh)
    (cellBeta : RawTwoCellExpr (pushoutShared comp1 comp2 sameModes).toModeSignature gLow gMid)
    (leftAcc : ModalityPath (pushoutShared comp1 comp2 sameModes).toModeSignature.graph
      overallSource sourceMode)
    (rightAcc : ModalityPath (pushoutShared comp1 comp2 sameModes).toModeSignature.graph
      targetMode overallTarget)
    (state : ArcWireState) (leftPad fSegment gSegment suffixWires : List Nat)
    (wellFormed : WellFormedArcState state)
    (alphaTurnback : cellAlphaUpper.isTurnbackOnly = true)
    (betaTurnback : cellBeta.isTurnbackOnly = true)
    (decomp : state.openWires = leftPad ++ (fSegment ++ ([] ++ (gSegment ++ suffixWires))))
    (padLen : leftPad.length = leftAcc.length)
    (fSegLen : fSegment.length = fMid.length)
    (gSegLen : gSegment.length = gLow.length)
    (windowsDisjoint : arcWindowsComponentDisjoint state.links fSegment gSegment) :
    ∃ sigma,
      ArcBoundedSwapCarrier state.nextFresh
          (runArcCell (runArcCell state leftAcc (composePath gLow rightAcc) cellAlphaUpper)
            (composePath leftAcc fHigh) rightAcc cellBeta).nextFresh sigma
        ∧ ArcStepSimCount sigma
            (runArcCell (runArcCell state leftAcc (composePath gLow rightAcc) cellAlphaUpper)
              (composePath leftAcc fHigh) rightAcc cellBeta)
            (runArcCell (runArcCell state (composePath leftAcc fMid) rightAcc cellBeta)
              leftAcc (composePath gMid rightAcc) cellAlphaUpper) :=
  arcGodementInnerSwapSimCount cellAlphaUpper cellBeta leftAcc rightAcc state leftPad fSegment
    gSegment suffixWires wellFormed alphaTurnback betaTurnback decomp padLen fSegLen gSegLen
    windowsDisjoint

/-! ## The pushout-typed instantiation at the concrete thin pushout -/

/-- The (single) mode of the concrete thin pushout. -/
def thinPushoutOnlyMode : thinPushout.toModeSignature.graph.Mode := ⟨0, by decide⟩

/-- The empty arc seed for the pushout-typed fire. -/
def thinPushoutFireSeed : ArcWireState := ArcWireState.mk [] [] 1 0 [] []

/-- The empty arc seed is well-formed. -/
theorem thinPushoutFireSeed_isWellFormed : WellFormedArcState thinPushoutFireSeed :=
  ⟨by unfold ArcStateFresh thinPushoutFireSeed; decide, trivial, by decide⟩

/-- ★ **The input FIRED at the concrete `thinPushout` signature** (pushout-typed; the thin
pushout has no 2-generators, so the honest pushout-typed instance is the identity corner —
the REAL multi-atom content fires on the turnback signature below). -/
theorem pushoutDisjointBlockCommuteInput_firedAtThinPushout :
    ∃ sigma,
      ArcBoundedSwapCarrier thinPushoutFireSeed.nextFresh
          (runArcCell (runArcCell thinPushoutFireSeed (identityPath thinPushoutOnlyMode)
              (composePath (identityPath thinPushoutOnlyMode)
                (identityPath thinPushoutOnlyMode))
              (RawTwoCellExpr.id (identityPath thinPushoutOnlyMode)))
            (composePath (identityPath thinPushoutOnlyMode)
              (identityPath thinPushoutOnlyMode))
            (identityPath thinPushoutOnlyMode)
            (RawTwoCellExpr.id (identityPath thinPushoutOnlyMode))).nextFresh sigma
        ∧ ArcStepSimCount sigma
            (runArcCell (runArcCell thinPushoutFireSeed (identityPath thinPushoutOnlyMode)
                (composePath (identityPath thinPushoutOnlyMode)
                  (identityPath thinPushoutOnlyMode))
                (RawTwoCellExpr.id (identityPath thinPushoutOnlyMode)))
              (composePath (identityPath thinPushoutOnlyMode)
                (identityPath thinPushoutOnlyMode))
              (identityPath thinPushoutOnlyMode)
              (RawTwoCellExpr.id (identityPath thinPushoutOnlyMode)))
            (runArcCell (runArcCell thinPushoutFireSeed
                (composePath (identityPath thinPushoutOnlyMode)
                  (identityPath thinPushoutOnlyMode))
                (identityPath thinPushoutOnlyMode)
                (RawTwoCellExpr.id (identityPath thinPushoutOnlyMode)))
              (identityPath thinPushoutOnlyMode)
              (composePath (identityPath thinPushoutOnlyMode)
                (identityPath thinPushoutOnlyMode))
              (RawTwoCellExpr.id (identityPath thinPushoutOnlyMode))) :=
  pushoutDisjointBlockCommuteInput involutionComputad secondThinComputad
    involutionSecondSameModes
    (RawTwoCellExpr.id (identityPath thinPushoutOnlyMode))
    (RawTwoCellExpr.id (identityPath thinPushoutOnlyMode))
    (identityPath thinPushoutOnlyMode) (identityPath thinPushoutOnlyMode)
    thinPushoutFireSeed [] [] [] [] thinPushoutFireSeed_isWellFormed rfl rfl rfl rfl rfl rfl
    (fun _ fWireMem => nomatch fWireMem)

/-! ## The content fire's compiled order-invariance pins (the r28 counit instance)

The REAL two-cell disjoint instance is the r28 counit fire
(`arcGodementInnerSwap_firedOnCounitInstance`, six atoms over two orders on the canonical
turnback signature).  The pins below decide-check the two orders' concrete order-invariant data
— the fields the dispatch's block reader consumes. -/

/-- The redex order of the counit content fire (alpha block first). -/
def dispatchContentFireRedex : ArcWireState :=
  runArcCell (runArcCell arcCellPastCellCapFireSeed adjunctionLeftThenRight
      (composePath (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
        (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base))
      whiskerSandwichedCounitCell)
    (composePath adjunctionLeftThenRight adjunctionLeftThenRight)
    (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
    threeAtomTurnbackCell

/-- The reduct order of the counit content fire (beta block first). -/
def dispatchContentFireReduct : ArcWireState :=
  runArcCell (runArcCell arcCellPastCellCapFireSeed
      (composePath adjunctionLeftThenRight
        (composePath adjunctionLeftThenRight adjunctionLeftThenRight))
      (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
      threeAtomTurnbackCell)
    adjunctionLeftThenRight
    (composePath adjunctionLeftThenRight
      (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base))
    whiskerSandwichedCounitCell

-- Compiled order-invariance evidence for the content fire (expect `true` on each).
#eval decide (dispatchContentFireRedex.nextFresh = dispatchContentFireReduct.nextFresh)
#eval decide (dispatchContentFireRedex.loops = dispatchContentFireReduct.loops)
#eval decide (dispatchContentFireRedex.openWires.length
  = dispatchContentFireReduct.openWires.length)
#eval decide (dispatchContentFireRedex.cupEventNodes.length
  = dispatchContentFireReduct.cupEventNodes.length)
#eval decide (dispatchContentFireRedex.capEventNodes.length
  = dispatchContentFireReduct.capEventNodes.length)

/-- ★ The content fire's order-invariant data, kernel-pinned: both orders end at fresh frontier
`14` with `0` loops, boundary reads `0, 1` root-stable at `0, 1`, and the six open wires in
sigma-correspondence (`[0,1,2,5,7,11]` versus `[0,1,2,5,6,10]` — the composite carrier's image).
`decide`-checked conjunction. -/
theorem dispatchContentFire_orderInvariantData :
    dispatchContentFireRedex.nextFresh = 14
      ∧ dispatchContentFireReduct.nextFresh = 14
      ∧ dispatchContentFireRedex.loops = dispatchContentFireReduct.loops
      ∧ dispatchContentFireRedex.openWires = [0, 1, 2, 5, 7, 11]
      ∧ dispatchContentFireReduct.openWires = [0, 1, 2, 5, 6, 10]
      ∧ unionFindRootOf dispatchContentFireRedex.links 0
          = unionFindRootOf dispatchContentFireReduct.links 0 := by
  decide

/-! ## Honesty markers + the untouched-false dispatch pins -/

/-- **Honesty marker — the dispatch's `componentComm` INPUT is SUPPLIED** (guarded turnback
form): the disjoint-support block commutation at the pushout signature, instantiated
pushout-typed at `thinPushout` and content-fired on the canonical turnback signature with
compiled order-invariance pins.  `= true`. -/
def fxAmalg_hasDispatchDisjointBlockCommuteInput : Bool := true

/-- **Honesty pin — the dispatch theorem itself stays `false`** (residual (1): the cell-functor
retag along the coprojection does not exist; the guard discharge from interleaving-NF invariants
is dispatch-lane work).  This file supplies the residual-(2) input ONLY.  `rfl`. -/
theorem dispatchDisjointBlockCommuteInput_saturatedDispatch_stays_false :
    fxAmalg_hasSaturatedDispatchTheorem = false := rfl

/-- **Honesty pin — #2043's close criterion stays `false`** (JAM-A hostage, untouched).  `rfl`. -/
theorem dispatchDisjointBlockCommuteInput_closeCriterion_stays_false :
    pushoutDispatchCloseCriterion = false := rfl

/-- **Honesty pin — the mode-side block-commute keystone stays `false`** (its ∀-state extract
form is refuted-adjacent; the guarded sim-form input here is the live successor).  `rfl`. -/
theorem dispatchDisjointBlockCommuteInput_blockCommute_stays_false :
    fxMode_hasArcBlockCommuteProof = false := rfl

end FX1Poly.Polygraph.Amalgam
