import FX1Poly.Polygraph.TwoCategory.Amalgam.DispatchDisjointBlockCommuteInput
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutArcRetagTransport
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCoreSwapBridgedSeedRefutation

/-! # WP-AMALG — the CROSS-COMPONENT BLOCK DISPATCH: retag + guard discharge + the B5 input, wired

## What this ships (the furthest dispatch consequence reachable WITHOUT JAM-A)

The r28 dispatch brick (`DispatchDisjointBlockCommuteInput.lean`) supplied the dispatch's
`componentComm` input at the pushout signature, GUARDED (turnback cells, decomposed state,
component-disjoint windows), with two named follow-ups: the cell-functor retag and the guard
discharge.  This file wires all three into the named cross-component consequence:

  * **`arcWindowsComponentDisjoint_ofEmptyLinksCheck`** — THE GUARD DISCHARGE: at an UNBRIDGED
    seed (`links = []` — the canonical interleaving seed the dispatch runs from, where no prior
    merge exists), every wire is its own component, so the component-disjointness guard follows
    from plain LIST disjointness of the windows — checked by a computable `Bool`
    (`arcWindowsListDisjointCheck`), hence AUTOMATIC (`decide`) at every concrete dispatch
    site.  Cross-component windows at the pushout read disjoint wire sets by construction
    (disjoint generators feed disjoint blocks), so the guard holds automatically for
    cross-component pairs.  The r29 bridged-seed refutation
    (`not_arcGodementCoreSwapSimCount_atBridgedSeed`) shows this is SHARP: at a bridged seed
    the unguarded form is FALSE — the empty-links hypothesis is load-bearing, not cosmetic.
  * **`pushoutCrossComponentBlockDispatch`** — THE NAMED CONSEQUENCE: a comp1 turnback cell
    and a comp2 turnback cell, RETAGGED along the two real coprojections into any shared-mode
    pushout and whiskered into list-disjoint windows of an unbridged well-formed seed, commute
    at arc level (full `ArcStepSimCount`, bounded composite carrier) — UNCONDITIONALLY in the
    component-disjointness guard, which is discharged rather than assumed.  The retag bridges
    are `isTurnbackOnly_mapCellAlong` + `mapPath_length` (the arc retag transport brick).
  * fired on the DOUBLE-ADJUNCTION pushout (`adjunctionComputad +_M adjunctionComputad` — a
    genuine two-component pushout, four 1-generators, four 2-generators) with cap-bearing
    sandwiched-counit cells in BOTH windows: the guard is NON-vacuous (both windows nonempty,
    live cap reads on both sides), with `#eval decide` pins + a kernel-decided conjunction of
    the two orders' order-invariant data.

## What still hangs on JAM-A (recorded precisely, nothing overclaimed)

This is the block-SWAP engine consequence, not the dispatch DECIDER.  The dispatch theorem
(`fxAmalg_hasSaturatedDispatchTheorem`) and the #2043 close criterion
(`pushoutDispatchCloseCriterion`) stay `false`: what remains is exactly arm (c) of the ceiling
ledger — the vcomp common-refinement payload zip = the JAM-A per-gap descent composed with the
fib-3 WalkingMonad reconstructed word problem (completeness of the combined decider), which no
amount of block-commutation supplies.  Residuals (1) and (2) of the r3 dispatch ledger are now
BOTH discharged in their honest forms (retag = `mapCellAlong` + the arc retag transport; guard
= this file's empty-links discharge); the JAM-A hostage is the ONLY remaining wall.

Raw Lean 4 + Init; per-declaration `#assert_no_axioms` + independent `#print axioms` twins. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The computable window-disjointness check + the guard discharge -/

/-- The computable LIST-disjointness check on two wire windows (`Bool`, so every concrete
dispatch site discharges it by `decide`/`rfl`). -/
def arcWindowsListDisjointCheck (fWindow gWindow : List Nat) : Bool :=
  fWindow.all (fun fWire => gWindow.all (fun gWire => !(fWire == gWire)))

/-- A true `List.all` gives the predicate on every member (cons-structural, propext-free). -/
theorem natListAllTrueOfMem : (wires : List Nat) → (predicate : Nat → Bool) →
    wires.all predicate = true → ∀ wire ∈ wires, predicate wire = true
  | [], _, _, _, wireMem => nomatch wireMem
  | _ :: restWires, predicate, allTrue, wire, wireMem => by
      obtain ⟨headTrue, restTrue⟩ := boolBothTrueOfAndTrue allTrue
      cases wireMem with
      | head => exact headTrue
      | tail _ memRest => exact natListAllTrueOfMem restWires predicate restTrue wire memRest

/-- ★★ **THE GUARD DISCHARGE.**  At an UNBRIDGED state (`links = []`) every wire roots at
itself, so `isSameComponent` is literal wire equality — the r26/r28 component-disjointness
guard follows from the computable list-disjointness of the windows.  This is the "disjoint
generators imply disjoint components" law at the canonical dispatch seed: cross-component
blocks read disjoint wire sets, and with no prior merges disjoint wires ARE disjoint
components.  (The r29 bridged-seed refutation shows the `links = []` hypothesis is
load-bearing: one bridge across the windows makes the unguarded commutation FALSE.) -/
theorem arcWindowsComponentDisjoint_ofEmptyLinksCheck (fWindow gWindow : List Nat)
    (checkPasses : arcWindowsListDisjointCheck fWindow gWindow = true) :
    arcWindowsComponentDisjoint [] fWindow gWindow := by
  intro fWire fMem gWire gMem
  have gWindowAll : (gWindow.all (fun gWire => !(fWire == gWire))) = true :=
    natListAllTrueOfMem fWindow _ checkPasses fWire fMem
  have notBeq : (!(fWire == gWire)) = true :=
    natListAllTrueOfMem gWindow _ gWindowAll gWire gMem
  show (fWire == gWire) = false
  cases beqValue : (fWire == gWire) with
  | false => rfl
  | true => rw [beqValue] at notBeq; exact Bool.noConfusion notBeq

/-! ## THE NAMED CROSS-COMPONENT BLOCK DISPATCH -/

/-- ★★★ **The cross-component block dispatch at the pushout** — a component-1 turnback cell
and a component-2 turnback cell, retagged along the REAL coprojections into the shared-mode
pushout and whiskered into list-disjoint windows of an unbridged well-formed seed, commute at
arc level in the Godement inner orientation (full eight-field `ArcStepSimCount`, bounded
composite carrier).  The component-disjointness guard of the r28 engine is DISCHARGED (not
assumed): `links = []` + the computable window check give it via
`arcWindowsComponentDisjoint_ofEmptyLinksCheck`; the retag bridges are
`isTurnbackOnly_mapCellAlong` and `mapPath_length`.  This is the block-swap step the
interleaving-NF dispatch fires when sorting a mixed cross-component word into component
blocks, now UNCONDITIONAL at the canonical seed. -/
theorem pushoutCrossComponentBlockDispatch
    (comp1 comp2 : ModeComputad) (sameModes : comp1.modeCount = comp2.modeCount)
    {overallSource overallTarget alphaSource : Fin comp1.modeCount}
    {betaSource betaTarget : Fin comp2.modeCount}
    {fMid fHigh : ModalityPath comp1.toModeGraph alphaSource
      (castFinAcrossCount sameModes betaSource)}
    {gLow gMid : ModalityPath comp2.toModeGraph betaSource betaTarget}
    (cellAlphaUpper : RawTwoCellExpr comp1.toModeSignature fMid fHigh)
    (cellBeta : RawTwoCellExpr comp2.toModeSignature gLow gMid)
    (leftAcc : ModalityPath (pushoutShared comp1 comp2 sameModes).toModeGraph
      overallSource alphaSource)
    (rightAcc : ModalityPath (pushoutShared comp1 comp2 sameModes).toModeGraph
      (castFinAcrossCount sameModes betaTarget) overallTarget)
    (state : ArcWireState) (leftPad fSegment gSegment suffixWires : List Nat)
    (wellFormed : WellFormedArcState state)
    (alphaTurnback : cellAlphaUpper.isTurnbackOnly = true)
    (betaTurnback : cellBeta.isTurnbackOnly = true)
    (seedUnbridged : state.links = [])
    (decomp : state.openWires = leftPad ++ (fSegment ++ ([] ++ (gSegment ++ suffixWires))))
    (padLen : leftPad.length = leftAcc.length)
    (fSegLen : fSegment.length = fMid.length)
    (gSegLen : gSegment.length = gLow.length)
    (windowsCheck : arcWindowsListDisjointCheck fSegment gSegment = true) :
    ∃ sigma,
      ArcBoundedSwapCarrier state.nextFresh
          (runArcCell
            (runArcCell state leftAcc
              (composePath
                (mapPath (inclusionRightTwoReal comp1 comp2 sameModes).toComputadMorphism gLow)
                rightAcc)
              (mapCellAlong (inclusionLeftTwoReal comp1 comp2 sameModes) cellAlphaUpper))
            (composePath leftAcc
              (mapPath (inclusionLeftTwoReal comp1 comp2 sameModes).toComputadMorphism fHigh))
            rightAcc
            (mapCellAlong (inclusionRightTwoReal comp1 comp2 sameModes) cellBeta)).nextFresh
          sigma
        ∧ ArcStepSimCount sigma
            (runArcCell
              (runArcCell state leftAcc
                (composePath
                  (mapPath (inclusionRightTwoReal comp1 comp2 sameModes).toComputadMorphism gLow)
                  rightAcc)
                (mapCellAlong (inclusionLeftTwoReal comp1 comp2 sameModes) cellAlphaUpper))
              (composePath leftAcc
                (mapPath (inclusionLeftTwoReal comp1 comp2 sameModes).toComputadMorphism fHigh))
              rightAcc
              (mapCellAlong (inclusionRightTwoReal comp1 comp2 sameModes) cellBeta))
            (runArcCell
              (runArcCell state
                (composePath leftAcc
                  (mapPath (inclusionLeftTwoReal comp1 comp2 sameModes).toComputadMorphism fMid))
                rightAcc
                (mapCellAlong (inclusionRightTwoReal comp1 comp2 sameModes) cellBeta))
              leftAcc
              (composePath
                (mapPath (inclusionRightTwoReal comp1 comp2 sameModes).toComputadMorphism gMid)
                rightAcc)
              (mapCellAlong (inclusionLeftTwoReal comp1 comp2 sameModes) cellAlphaUpper)) := by
  have alphaRetagTurnback :
      (mapCellAlong (inclusionLeftTwoReal comp1 comp2 sameModes) cellAlphaUpper).isTurnbackOnly
        = true := by
    rw [isTurnbackOnly_mapCellAlong]; exact alphaTurnback
  have betaRetagTurnback :
      (mapCellAlong (inclusionRightTwoReal comp1 comp2 sameModes) cellBeta).isTurnbackOnly
        = true := by
    rw [isTurnbackOnly_mapCellAlong]; exact betaTurnback
  have fSegLenMapped : fSegment.length
      = (mapPath (inclusionLeftTwoReal comp1 comp2 sameModes).toComputadMorphism fMid).length := by
    rw [mapPath_length]; exact fSegLen
  have gSegLenMapped : gSegment.length
      = (mapPath (inclusionRightTwoReal comp1 comp2 sameModes).toComputadMorphism gLow).length := by
    rw [mapPath_length]; exact gSegLen
  have windowsDisjoint : arcWindowsComponentDisjoint state.links fSegment gSegment := by
    rw [seedUnbridged]
    exact arcWindowsComponentDisjoint_ofEmptyLinksCheck fSegment gSegment windowsCheck
  exact pushoutDisjointBlockCommuteInput comp1 comp2 sameModes
    (mapCellAlong (inclusionLeftTwoReal comp1 comp2 sameModes) cellAlphaUpper)
    (mapCellAlong (inclusionRightTwoReal comp1 comp2 sameModes) cellBeta)
    leftAcc rightAcc state leftPad fSegment gSegment suffixWires wellFormed
    alphaRetagTurnback betaRetagTurnback decomp padLen fSegLenMapped gSegLenMapped
    windowsDisjoint

/-! ## The fire: the double-adjunction pushout, cap-bearing cells in BOTH windows -/

/-- The single-`left` path of the adjunction computad in `Fin` coordinates (`base -> tip`). -/
def adjunctionComputadLeftOnlyPath :
    ModalityPath adjunctionComputad.toModeGraph (⟨0, by decide⟩ : Fin 2) (⟨1, by decide⟩ : Fin 2) :=
  ModalityPath.cons
    (⟨⟨0, by decide⟩, rfl⟩ : adjunctionComputad.Modality ⟨0, by decide⟩ ⟨1, by decide⟩)
    (ModalityPath.nil (graph := adjunctionComputad.toModeGraph) ⟨1, by decide⟩)

/-- The single-`right` path (`tip -> base`). -/
def adjunctionComputadRightOnlyPath :
    ModalityPath adjunctionComputad.toModeGraph (⟨1, by decide⟩ : Fin 2) (⟨0, by decide⟩ : Fin 2) :=
  ModalityPath.cons
    (⟨⟨1, by decide⟩, rfl⟩ : adjunctionComputad.Modality ⟨1, by decide⟩ ⟨0, by decide⟩)
    (ModalityPath.nil (graph := adjunctionComputad.toModeGraph) ⟨0, by decide⟩)

/-- The whisker-sandwiched reconstructed counit — a CAP at window-relative position `1`
(`[left,right,left,right] => [left,right]` in `Fin` coordinates), the reconstructed-signature
twin of the bespoke `whiskerSandwichedCounitCell`. -/
def adjunctionComputadSandwichedCounitCell :
    RawTwoCellExpr adjunctionComputad.toModeSignature
      (composePath adjunctionComputadLeftOnlyPath
        (composePath adjunctionComputadReconstructedRightThenLeft
          adjunctionComputadRightOnlyPath))
      (composePath adjunctionComputadLeftOnlyPath
        (composePath (ModalityPath.nil (graph := adjunctionComputad.toModeGraph) ⟨1, by decide⟩)
          adjunctionComputadRightOnlyPath)) :=
  RawTwoCellExpr.whiskerLeft adjunctionComputadLeftOnlyPath
    (RawTwoCellExpr.whiskerRight adjunctionComputadRightOnlyPath
        (RawTwoCellExpr.gen adjunctionComputad_reconstructsCounit :
          RawTwoCellExpr adjunctionComputad.toModeSignature
            adjunctionComputadReconstructedRightThenLeft
            (ModalityPath.nil (graph := adjunctionComputad.toModeGraph) ⟨1, by decide⟩))
      : RawTwoCellExpr adjunctionComputad.toModeSignature
          (composePath adjunctionComputadReconstructedRightThenLeft
            adjunctionComputadRightOnlyPath)
          (composePath (ModalityPath.nil (graph := adjunctionComputad.toModeGraph) ⟨1, by decide⟩)
            adjunctionComputadRightOnlyPath))

/-- The sandwiched reconstructed counit is turnback-only (`rfl`). -/
theorem adjunctionComputadSandwichedCounitCell_isTurnbackOnly :
    adjunctionComputadSandwichedCounitCell.isTurnbackOnly = true := rfl

/-- The eight-wire unbridged seed for the cross-component fire (f-window `[0,1,2,3]`,
g-window `[4,5,6,7]`). -/
def crossComponentFireSeed : ArcWireState := ArcWireState.mk [0, 1, 2, 3, 4, 5, 6, 7] [] 8 0 [] []

/-- The fire seed is well-formed. -/
theorem crossComponentFireSeed_isWellFormed : WellFormedArcState crossComponentFireSeed :=
  ⟨by unfold ArcStateFresh crossComponentFireSeed; decide, trivial, by decide⟩

/-- The pushout-level empty path at the shared base mode of the double-adjunction pushout. -/
def doubleAdjunctionPushoutNilBase :
    ModalityPath (pushoutShared adjunctionComputad adjunctionComputad rfl).toModeGraph
      (⟨0, by decide⟩ : Fin 2) (⟨0, by decide⟩ : Fin 2) :=
  ModalityPath.nil
    (graph := (pushoutShared adjunctionComputad adjunctionComputad rfl).toModeGraph)
    ⟨0, by decide⟩

/-- ★★ **The cross-component block dispatch FIRED on the double-adjunction pushout** — the
component-1 sandwiched counit (cap reading window wires `1, 2`) against the component-2
sandwiched counit (cap reading window wires `5, 6`), retagged along the two REAL coprojections
into `adjunctionComputad +_M adjunctionComputad`, from the unbridged eight-wire seed: the guard
is NON-vacuous (both windows nonempty, live cap reads on both sides) and discharged
automatically by the computable window check. -/
theorem crossComponentBlockDispatch_firedOnDoubleAdjunction :
    ∃ sigma,
      ArcBoundedSwapCarrier crossComponentFireSeed.nextFresh
          (runArcCell
            (runArcCell crossComponentFireSeed doubleAdjunctionPushoutNilBase
              (composePath
                (mapPath (inclusionRightTwoReal adjunctionComputad adjunctionComputad
                    rfl).toComputadMorphism
                  (composePath adjunctionComputadLeftOnlyPath
                    (composePath adjunctionComputadReconstructedRightThenLeft
                      adjunctionComputadRightOnlyPath)))
                doubleAdjunctionPushoutNilBase)
              (mapCellAlong (inclusionLeftTwoReal adjunctionComputad adjunctionComputad rfl)
                adjunctionComputadSandwichedCounitCell))
            (composePath doubleAdjunctionPushoutNilBase
              (mapPath (inclusionLeftTwoReal adjunctionComputad adjunctionComputad
                  rfl).toComputadMorphism
                (composePath adjunctionComputadLeftOnlyPath
                  (composePath
                    (ModalityPath.nil (graph := adjunctionComputad.toModeGraph) ⟨1, by decide⟩)
                    adjunctionComputadRightOnlyPath))))
            doubleAdjunctionPushoutNilBase
            (mapCellAlong (inclusionRightTwoReal adjunctionComputad adjunctionComputad rfl)
              adjunctionComputadSandwichedCounitCell)).nextFresh
          sigma
        ∧ ArcStepSimCount sigma
            (runArcCell
              (runArcCell crossComponentFireSeed doubleAdjunctionPushoutNilBase
                (composePath
                  (mapPath (inclusionRightTwoReal adjunctionComputad adjunctionComputad
                      rfl).toComputadMorphism
                    (composePath adjunctionComputadLeftOnlyPath
                      (composePath adjunctionComputadReconstructedRightThenLeft
                        adjunctionComputadRightOnlyPath)))
                  doubleAdjunctionPushoutNilBase)
                (mapCellAlong (inclusionLeftTwoReal adjunctionComputad adjunctionComputad rfl)
                  adjunctionComputadSandwichedCounitCell))
              (composePath doubleAdjunctionPushoutNilBase
                (mapPath (inclusionLeftTwoReal adjunctionComputad adjunctionComputad
                    rfl).toComputadMorphism
                  (composePath adjunctionComputadLeftOnlyPath
                    (composePath
                      (ModalityPath.nil (graph := adjunctionComputad.toModeGraph) ⟨1, by decide⟩)
                      adjunctionComputadRightOnlyPath))))
              doubleAdjunctionPushoutNilBase
              (mapCellAlong (inclusionRightTwoReal adjunctionComputad adjunctionComputad rfl)
                adjunctionComputadSandwichedCounitCell))
            (runArcCell
              (runArcCell crossComponentFireSeed
                (composePath doubleAdjunctionPushoutNilBase
                  (mapPath (inclusionLeftTwoReal adjunctionComputad adjunctionComputad
                      rfl).toComputadMorphism
                    (composePath adjunctionComputadLeftOnlyPath
                      (composePath adjunctionComputadReconstructedRightThenLeft
                        adjunctionComputadRightOnlyPath))))
                doubleAdjunctionPushoutNilBase
                (mapCellAlong (inclusionRightTwoReal adjunctionComputad adjunctionComputad rfl)
                  adjunctionComputadSandwichedCounitCell))
              doubleAdjunctionPushoutNilBase
              (composePath
                (mapPath (inclusionRightTwoReal adjunctionComputad adjunctionComputad
                    rfl).toComputadMorphism
                  (composePath adjunctionComputadLeftOnlyPath
                    (composePath
                      (ModalityPath.nil (graph := adjunctionComputad.toModeGraph) ⟨1, by decide⟩)
                      adjunctionComputadRightOnlyPath)))
                doubleAdjunctionPushoutNilBase)
              (mapCellAlong (inclusionLeftTwoReal adjunctionComputad adjunctionComputad rfl)
                adjunctionComputadSandwichedCounitCell)) :=
  pushoutCrossComponentBlockDispatch adjunctionComputad adjunctionComputad rfl
    (alphaSource := ⟨0, by decide⟩) (betaSource := ⟨0, by decide⟩) (betaTarget := ⟨0, by decide⟩)
    adjunctionComputadSandwichedCounitCell adjunctionComputadSandwichedCounitCell
    doubleAdjunctionPushoutNilBase doubleAdjunctionPushoutNilBase
    crossComponentFireSeed [] [0, 1, 2, 3] [4, 5, 6, 7] []
    crossComponentFireSeed_isWellFormed
    adjunctionComputadSandwichedCounitCell_isTurnbackOnly
    adjunctionComputadSandwichedCounitCell_isTurnbackOnly
    rfl rfl rfl rfl rfl rfl

/-! ## The fire's compiled order-invariance pins -/

/-- The redex order of the cross-component fire (component-1 block first). -/
def crossComponentFireRedex : ArcWireState :=
  runArcCell
    (runArcCell crossComponentFireSeed doubleAdjunctionPushoutNilBase
      (composePath
        (mapPath (inclusionRightTwoReal adjunctionComputad adjunctionComputad
            rfl).toComputadMorphism
          (composePath adjunctionComputadLeftOnlyPath
            (composePath adjunctionComputadReconstructedRightThenLeft
              adjunctionComputadRightOnlyPath)))
        doubleAdjunctionPushoutNilBase)
      (mapCellAlong (inclusionLeftTwoReal adjunctionComputad adjunctionComputad rfl)
        adjunctionComputadSandwichedCounitCell))
    (composePath doubleAdjunctionPushoutNilBase
      (mapPath (inclusionLeftTwoReal adjunctionComputad adjunctionComputad
          rfl).toComputadMorphism
        (composePath adjunctionComputadLeftOnlyPath
          (composePath
            (ModalityPath.nil (graph := adjunctionComputad.toModeGraph) ⟨1, by decide⟩)
            adjunctionComputadRightOnlyPath))))
    doubleAdjunctionPushoutNilBase
    (mapCellAlong (inclusionRightTwoReal adjunctionComputad adjunctionComputad rfl)
      adjunctionComputadSandwichedCounitCell)

/-- The reduct order of the cross-component fire (component-2 block first). -/
def crossComponentFireReduct : ArcWireState :=
  runArcCell
    (runArcCell crossComponentFireSeed
      (composePath doubleAdjunctionPushoutNilBase
        (mapPath (inclusionLeftTwoReal adjunctionComputad adjunctionComputad
            rfl).toComputadMorphism
          (composePath adjunctionComputadLeftOnlyPath
            (composePath adjunctionComputadReconstructedRightThenLeft
              adjunctionComputadRightOnlyPath))))
      doubleAdjunctionPushoutNilBase
      (mapCellAlong (inclusionRightTwoReal adjunctionComputad adjunctionComputad rfl)
        adjunctionComputadSandwichedCounitCell))
    doubleAdjunctionPushoutNilBase
    (composePath
      (mapPath (inclusionRightTwoReal adjunctionComputad adjunctionComputad
          rfl).toComputadMorphism
        (composePath adjunctionComputadLeftOnlyPath
          (composePath
            (ModalityPath.nil (graph := adjunctionComputad.toModeGraph) ⟨1, by decide⟩)
            adjunctionComputadRightOnlyPath)))
      doubleAdjunctionPushoutNilBase)
    (mapCellAlong (inclusionLeftTwoReal adjunctionComputad adjunctionComputad rfl)
      adjunctionComputadSandwichedCounitCell)

-- Compiled order-invariance evidence for the cross-component fire (expect `true` on each).
#eval decide (crossComponentFireRedex.nextFresh = crossComponentFireReduct.nextFresh)
#eval decide (crossComponentFireRedex.loops = crossComponentFireReduct.loops)
#eval decide (crossComponentFireRedex.openWires.length
  = crossComponentFireReduct.openWires.length)
#eval decide (crossComponentFireRedex.capEventNodes.length
  = crossComponentFireReduct.capEventNodes.length)
/-- ★ The cross-component fire's order-invariant data, kernel-pinned: both orders end at fresh
frontier `10` with equal loops, the open wires are BYTE-IDENTICAL `[0, 3, 4, 7]` (fresh
allocation is position-independent, and each cap consumes only its own window), and — the
sharp CONTRAST with the r29 bridged-seed asymmetry — the consumed old wires `1` and `5` root
IDENTICALLY in both orders (`2` and `6` respectively): at the unbridged seed the merge orders
cannot interact, which is exactly what the discharged guard buys.  `decide`-checked. -/
theorem crossComponentFire_orderInvariantData :
    crossComponentFireRedex.nextFresh = 10
      ∧ crossComponentFireReduct.nextFresh = 10
      ∧ crossComponentFireRedex.loops = crossComponentFireReduct.loops
      ∧ crossComponentFireRedex.openWires = [0, 3, 4, 7]
      ∧ crossComponentFireReduct.openWires = [0, 3, 4, 7]
      ∧ unionFindRootOf crossComponentFireRedex.links 1
          = unionFindRootOf crossComponentFireReduct.links 1
      ∧ unionFindRootOf crossComponentFireRedex.links 5
          = unionFindRootOf crossComponentFireReduct.links 5 := by
  decide

/-! ## Honesty markers + the untouched-false dispatch pins -/

/-- ★★ **Honesty marker — the CROSS-COMPONENT BLOCK DISPATCH ships.**  The guard discharge
(`arcWindowsComponentDisjoint_ofEmptyLinksCheck`: unbridged seed + computable window check
imply the r26/r28 component guard — sharp by the r29 bridged-seed refutation) wired with the
arc retag transport and the r28 `componentComm` input into the named consequence
`pushoutCrossComponentBlockDispatch`: retagged component turnback cells commute at arc level
at any shared-mode pushout from the canonical seed, guard discharged automatically; fired
non-vacuously on the double-adjunction pushout (cap-bearing cells in BOTH windows).  `= true`. -/
def fxAmalg_hasCrossComponentBlockDispatch : Bool := true

/-- **Honesty pin — the dispatch theorem itself STAYS `false`** (the JAM-A hostage: the vcomp
common-refinement payload zip = the per-gap descent + the fib-3 WalkingMonad reconstruction —
the combined decider's COMPLETENESS, which block commutation does not supply).  `rfl`. -/
theorem crossComponentBlockDispatch_saturatedDispatch_stays_false :
    fxAmalg_hasSaturatedDispatchTheorem = false := rfl

/-- **Honesty pin — #2043's close criterion STAYS `false`** (JAM-A hostage, untouched).  `rfl`. -/
theorem crossComponentBlockDispatch_closeCriterion_stays_false :
    pushoutDispatchCloseCriterion = false := rfl

/-- **Honesty pin — the r29 bridged-seed decision STANDS** (`rfl` re-record): the guard
discharged here cannot be dropped — at a bridged seed the unguarded commutation is refuted. -/
theorem crossComponentBlockDispatch_bridgedSeedSharpnessStands :
    fxMode_hasArcCoreSwapBridgedSeedDecision = true := rfl

end FX1Poly.Polygraph.Amalgam
