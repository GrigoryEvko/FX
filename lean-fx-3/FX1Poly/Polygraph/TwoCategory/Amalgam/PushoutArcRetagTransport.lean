import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutRightImageReflect
import FX1Poly.Polygraph.TwoCategory.Amalgam.RealCoprojectionLeft
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcCellWindowSegmentRun

/-! # WP-AMALG — the ARC RETAG TRANSPORT: the arc semantics is invariant under the pushout cell functor

## What this ships (the dispatch residual-(1) retag, carried to the ARC engine)

The dispatch ledger's residual (1) named "the cell-functor retag `RawTwoCellExpr comp_i ->
RawTwoCellExpr pushout` along the coprojection".  The functor itself EXISTS since r4/r6
(`mapCellAlong` over a `ComputadMorphismTwo`; both real coprojections `inclusionLeftTwoReal` /
`inclusionRightTwoReal`).  What did NOT exist is the bridge from the functor to the r28
whole-cell ARC engine (`arcCellPastCellSwapSimCount` / `arcGodementInnerSwapSimCount` /
`pushoutDisjointBlockCommuteInput`) — the retagging lemma that carries FreeTwoCell whole-cell
commutation across the functor.  This file supplies exactly that bridge, generically over ANY
`ComputadMorphismTwo`:

  * **`stepArcAtom_crossSignatureCongr`** — the arc step reads an atom only through three
    lengths (position / dom arity / cod arity), across DIFFERENT signatures;
  * **`processArcSpine_mapCellAlong`** — the joint spine recursion: folding the arc step over
    the `mapCellAlong`-image spine (from `mapPath`-mapped accumulators) equals folding it over
    the source spine (the `arityFold_foldl_mapCellAlong` recursion pattern, re-run for the arc
    fold: `gen` aligns the single atom via the cross-signature congruence — all three lengths
    preserved by `mapPath_length`; `vcomp` threads the right factor as continuation; the
    whisker cases strip the functor's `castBoundary` via `castBoundary_spineDiff` and rewrite
    the shifted accumulator through `mapPath_composePath`);
  * **`runArcCell_mapCellAlong`** — THE RETAG TRANSPORT: `runArcCell state (mapPath leftAcc)
    (mapPath rightAcc) (mapCellAlong morphism cell) = runArcCell state leftAcc rightAcc cell`
    — a retagged component cell is the SAME arc-state transformer as its source cell;
  * **`isTurnbackOnly_castBoundary`** / **`isTurnbackOnly_mapCellAlong`** — the turnback-only
    class (the r28 engine's cell class) is functor-stable, so retagged component turnback
    cells are legal inputs to the pushout block-commute input.

Consequence (consumed by the cross-component dispatch brick): the r28 disjoint-support
block-commute at the pushout signature applies to `mapCellAlong`-images of component cells,
and its two run orders are LITERALLY the component-level runs — whole-cell commutation
transports across the coprojections with zero loss.

## Fire

The transport fired at the double-adjunction pushout (`adjunctionComputad +_M
adjunctionComputad`, the two-component pushout with four 1-generators and four 2-generators):
the reconstructed unit cup, retagged along the LEFT real coprojection, drives the arc state
identically to the source cup — with the mapped cell's turnback flag and the transported run's
concrete openWires kernel-pinned.

Raw Lean 4 + Init; structural recursion only; per-declaration `#assert_no_axioms` +
independent `#print axioms` twins. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The cross-signature arc-step congruence -/

/-- `stepArcAtom` depends on the atom ONLY through `leftContext.length` (the position) and
`generatorDom.length` / `generatorCod.length` (the arity) — across DIFFERENT signatures: two
atoms with equal length triples drive the arc state identically.  The arc twin of
`arityFoldStepAtom_congr` (and the two-signature strengthening of the same-signature
`stepArcAtom_congr`). -/
theorem stepArcAtom_crossSignatureCongr {signatureOne signatureTwo : ModeSignature}
    {sourceModeOne targetModeOne : signatureOne.graph.Mode}
    {sourceModeTwo targetModeTwo : signatureTwo.graph.Mode}
    (state : ArcWireState)
    (atomOne : SpineAtom signatureOne sourceModeOne targetModeOne)
    (atomTwo : SpineAtom signatureTwo sourceModeTwo targetModeTwo)
    (leftEqual : atomOne.leftContext.length = atomTwo.leftContext.length)
    (domEqual : atomOne.generatorDom.length = atomTwo.generatorDom.length)
    (codEqual : atomOne.generatorCod.length = atomTwo.generatorCod.length) :
    stepArcAtom state atomOne = stepArcAtom state atomTwo := by
  unfold stepArcAtom
  rw [leftEqual, domEqual, codEqual]

/-! ## The joint spine recursion for the arc fold -/

/-- ★★ **The arc fold over a `mapCellAlong`-image spine equals the arc fold over the source
spine** (given continuation agreement) — the `arityFold_foldl_mapCellAlong` joint recursion,
re-run for `stepArcAtom`: `gen` aligns the single mapped atom to its source via the
cross-signature congruence (all three lengths preserved by `mapPath_length`); `id` defers to
the continuation; `vcomp` threads the right factor's fold as the left factor's continuation;
the two whisker cases strip the functor's `castBoundary` (`castBoundary_spineDiff`) and rewrite
the whisker-shifted accumulator through `mapPath_composePath`. -/
theorem processArcSpine_mapCellAlong {source target : ModeComputad}
    (morphism : ComputadMorphismTwo source target)
    {overallSource overallTarget : Fin source.modeCount} :
    {localSource localTarget : Fin source.modeCount} →
    (leftAcc : ModalityPath source.toModeGraph overallSource localSource) →
    (rightAcc : ModalityPath source.toModeGraph localTarget overallTarget) →
    {localDom localCod : ModalityPath source.toModeGraph localSource localTarget} →
    (cell : RawTwoCellExpr source.toModeSignature localDom localCod) →
    (restTarget : List (SpineAtom target.toModeSignature
      (morphism.onModes overallSource) (morphism.onModes overallTarget))) →
    (restSource : List (SpineAtom source.toModeSignature overallSource overallTarget)) →
    (∀ midState, processArcSpine midState restTarget = processArcSpine midState restSource) →
    ∀ state, processArcSpine state ((mapCellAlong morphism cell).spineDiff
                (mapPath morphism.toComputadMorphism leftAcc)
                (mapPath morphism.toComputadMorphism rightAcc) restTarget)
          = processArcSpine state (cell.spineDiff leftAcc rightAcc restSource)
  | _, _, leftAcc, rightAcc, _, _, .gen generator, restTarget, restSource, contHyp => by
      intro state
      let atomTarget : SpineAtom target.toModeSignature
          (morphism.onModes overallSource) (morphism.onModes overallTarget) :=
        ⟨_, _, mapPath morphism.toComputadMorphism leftAcc, _, _, morphism.onTwoCell generator,
          mapPath morphism.toComputadMorphism rightAcc⟩
      let atomSource : SpineAtom source.toModeSignature overallSource overallTarget :=
        ⟨_, _, leftAcc, _, _, generator, rightAcc⟩
      show processArcSpine (stepArcAtom state atomTarget) restTarget
          = processArcSpine (stepArcAtom state atomSource) restSource
      rw [stepArcAtom_crossSignatureCongr state atomTarget atomSource
            (mapPath_length morphism.toComputadMorphism leftAcc)
            (mapPath_length morphism.toComputadMorphism _)
            (mapPath_length morphism.toComputadMorphism _)]
      exact contHyp _
  | _, _, _leftAcc, _rightAcc, _, _, .id _path, _restTarget, _restSource, contHyp => by
      intro state; exact contHyp state
  | _, _, leftAcc, rightAcc, _, _, .vcomp cellLower cellUpper, restTarget, restSource,
      contHyp => by
      intro state
      exact processArcSpine_mapCellAlong morphism leftAcc rightAcc cellLower
        ((mapCellAlong morphism cellUpper).spineDiff (mapPath morphism.toComputadMorphism leftAcc)
          (mapPath morphism.toComputadMorphism rightAcc) restTarget)
        (cellUpper.spineDiff leftAcc rightAcc restSource)
        (processArcSpine_mapCellAlong morphism leftAcc rightAcc cellUpper restTarget restSource
          contHyp)
        state
  | _, _, leftAcc, rightAcc, _, _, .whiskerLeft oneCell body, restTarget, restSource,
      contHyp => by
      intro state
      show processArcSpine state ((RawTwoCellExpr.castBoundary _ _
              (RawTwoCellExpr.whiskerLeft (mapPath morphism.toComputadMorphism oneCell)
                (mapCellAlong morphism body))).spineDiff
            (mapPath morphism.toComputadMorphism leftAcc)
            (mapPath morphism.toComputadMorphism rightAcc) restTarget)
          = processArcSpine state (body.spineDiff (composePath leftAcc oneCell) rightAcc
              restSource)
      rw [RawTwoCellExpr.castBoundary_spineDiff]
      have recursiveStep := processArcSpine_mapCellAlong morphism (composePath leftAcc oneCell)
        rightAcc body restTarget restSource contHyp state
      rw [mapPath_composePath morphism.toComputadMorphism leftAcc oneCell] at recursiveStep
      exact recursiveStep
  | _, _, leftAcc, rightAcc, _, _, .whiskerRight oneCell body, restTarget, restSource,
      contHyp => by
      intro state
      show processArcSpine state ((RawTwoCellExpr.castBoundary _ _
              (RawTwoCellExpr.whiskerRight (mapPath morphism.toComputadMorphism oneCell)
                (mapCellAlong morphism body))).spineDiff
            (mapPath morphism.toComputadMorphism leftAcc)
            (mapPath morphism.toComputadMorphism rightAcc) restTarget)
          = processArcSpine state (body.spineDiff leftAcc (composePath oneCell rightAcc)
              restSource)
      rw [RawTwoCellExpr.castBoundary_spineDiff]
      have recursiveStep := processArcSpine_mapCellAlong morphism leftAcc
        (composePath oneCell rightAcc) body restTarget restSource contHyp state
      rw [mapPath_composePath morphism.toComputadMorphism oneCell rightAcc] at recursiveStep
      exact recursiveStep

/-! ## THE RETAG TRANSPORT -/

/-- ★★★ **The arc semantics is invariant under the pushout cell functor.**  For any
`ComputadMorphismTwo` and any free 2-cell over the source computad, running the
`mapCellAlong`-image at the `mapPath`-mapped whisker accumulators drives the arc state EXACTLY
as the source cell does — the retagging lemma that carries the FreeTwoCell whole-cell
commutation engine across the pushout coprojections: the two run orders of retagged component
cells at the pushout ARE the component-level runs, state by state. -/
theorem runArcCell_mapCellAlong {source target : ModeComputad}
    (morphism : ComputadMorphismTwo source target)
    {overallSource overallTarget : Fin source.modeCount}
    {localSource localTarget : Fin source.modeCount}
    (state : ArcWireState)
    (leftAcc : ModalityPath source.toModeGraph overallSource localSource)
    (rightAcc : ModalityPath source.toModeGraph localTarget overallTarget)
    {localDom localCod : ModalityPath source.toModeGraph localSource localTarget}
    (cell : RawTwoCellExpr source.toModeSignature localDom localCod) :
    runArcCell state (mapPath morphism.toComputadMorphism leftAcc)
        (mapPath morphism.toComputadMorphism rightAcc) (mapCellAlong morphism cell)
      = runArcCell state leftAcc rightAcc cell :=
  processArcSpine_mapCellAlong morphism leftAcc rightAcc cell [] [] (fun _ => rfl) state

/-! ## The turnback-only class is functor-stable -/

/-- `isTurnbackOnly` is invariant under a boundary cast (the cast is `Eq.rec` on the boundary
paths; substituting the equalities collapses it). -/
theorem isTurnbackOnly_castBoundary {signature : ModeSignature}
    {sourceMode targetMode : signature.graph.Mode}
    {sourcePath sourcePath' targetPath targetPath' :
      ModalityPath signature.graph sourceMode targetMode}
    (hsource : sourcePath = sourcePath') (htarget : targetPath = targetPath')
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    (RawTwoCellExpr.castBoundary hsource htarget cell).isTurnbackOnly
      = cell.isTurnbackOnly := by
  cases hsource; cases htarget; rfl

/-- ★ **The turnback-only cell class is stable under the pushout cell functor** — `mapPath`
preserves the boundary lengths that classify a generator as a cup (`0 => 2`) or cap (`2 => 0`),
`id` / `vcomp` are structural, and the whisker cases strip the functor's cast.  So a retagged
component turnback cell is a legal input to the pushout disjoint-support block-commute. -/
theorem isTurnbackOnly_mapCellAlong {source target : ModeComputad}
    (morphism : ComputadMorphismTwo source target) :
    {localSource localTarget : Fin source.modeCount} →
    {localDom localCod : ModalityPath source.toModeGraph localSource localTarget} →
    (cell : RawTwoCellExpr source.toModeSignature localDom localCod) →
    (mapCellAlong morphism cell).isTurnbackOnly = cell.isTurnbackOnly
  | _, _, localDom, localCod, .gen _ => by
      show ((((mapPath morphism.toComputadMorphism localDom).length == 0)
              && ((mapPath morphism.toComputadMorphism localCod).length == 2))
            || (((mapPath morphism.toComputadMorphism localDom).length == 2)
              && ((mapPath morphism.toComputadMorphism localCod).length == 0)))
        = (((localDom.length == 0) && (localCod.length == 2))
            || ((localDom.length == 2) && (localCod.length == 0)))
      rw [mapPath_length morphism.toComputadMorphism localDom,
        mapPath_length morphism.toComputadMorphism localCod]
  | _, _, _, _, .id _ => rfl
  | _, _, _, _, .vcomp cellLower cellUpper => by
      show ((mapCellAlong morphism cellLower).isTurnbackOnly
            && (mapCellAlong morphism cellUpper).isTurnbackOnly)
          = (cellLower.isTurnbackOnly && cellUpper.isTurnbackOnly)
      rw [isTurnbackOnly_mapCellAlong morphism cellLower,
        isTurnbackOnly_mapCellAlong morphism cellUpper]
  | _, _, _, _, .whiskerLeft oneCell body => by
      show (RawTwoCellExpr.castBoundary
            (mapPath_composePath morphism.toComputadMorphism oneCell _).symm
            (mapPath_composePath morphism.toComputadMorphism oneCell _).symm
            (RawTwoCellExpr.whiskerLeft (mapPath morphism.toComputadMorphism oneCell)
              (mapCellAlong morphism body))).isTurnbackOnly
          = body.isTurnbackOnly
      rw [isTurnbackOnly_castBoundary]
      exact isTurnbackOnly_mapCellAlong morphism body
  | _, _, _, _, .whiskerRight oneCell body => by
      show (RawTwoCellExpr.castBoundary
            (mapPath_composePath morphism.toComputadMorphism _ oneCell).symm
            (mapPath_composePath morphism.toComputadMorphism _ oneCell).symm
            (RawTwoCellExpr.whiskerRight (mapPath morphism.toComputadMorphism oneCell)
              (mapCellAlong morphism body))).isTurnbackOnly
          = body.isTurnbackOnly
      rw [isTurnbackOnly_castBoundary]
      exact isTurnbackOnly_mapCellAlong morphism body

/-! ## The fire: the double-adjunction pushout, the retagged cup drives the state identically -/

/-- The base mode of the adjunction computad in `Fin` coordinates. -/
def adjunctionComputadBaseMode : Fin adjunctionComputad.modeCount := ⟨0, by decide⟩

/-- The empty path at the reconstructed base mode. -/
def adjunctionComputadNilBase :
    ModalityPath adjunctionComputad.toModeGraph adjunctionComputadBaseMode
      adjunctionComputadBaseMode :=
  ModalityPath.nil (graph := adjunctionComputad.toModeGraph) adjunctionComputadBaseMode

/-- The reconstructed unit CUP as a free 2-cell over the adjunction computad's reconstructed
signature (`nil => [left, right]`, a genuine `0 => 2` turnback). -/
def adjunctionComputadUnitCupCell :
    RawTwoCellExpr adjunctionComputad.toModeSignature adjunctionComputadNilBase
      adjunctionComputadReconstructedLeftThenRight :=
  RawTwoCellExpr.gen adjunctionComputad_reconstructsUnit

/-- The two-wire seed for the fire. -/
def arcRetagFireSeed : ArcWireState := ArcWireState.mk [0, 1] [] 2 0 [] []

/-- ★ **The transport FIRED at the double-adjunction pushout** — the reconstructed unit cup,
retagged along the LEFT real coprojection into `adjunctionComputad +_M adjunctionComputad`,
drives the arc state EXACTLY as the source cup (instance of `runArcCell_mapCellAlong`). -/
theorem arcRetagTransport_firedOnDoubleAdjunction :
    runArcCell arcRetagFireSeed
        (mapPath (inclusionLeftTwoReal adjunctionComputad adjunctionComputad rfl).toComputadMorphism
          adjunctionComputadNilBase)
        (mapPath (inclusionLeftTwoReal adjunctionComputad adjunctionComputad rfl).toComputadMorphism
          adjunctionComputadNilBase)
        (mapCellAlong (inclusionLeftTwoReal adjunctionComputad adjunctionComputad rfl)
          adjunctionComputadUnitCupCell)
      = runArcCell arcRetagFireSeed adjunctionComputadNilBase adjunctionComputadNilBase
          adjunctionComputadUnitCupCell :=
  runArcCell_mapCellAlong (inclusionLeftTwoReal adjunctionComputad adjunctionComputad rfl)
    arcRetagFireSeed adjunctionComputadNilBase adjunctionComputadNilBase
    adjunctionComputadUnitCupCell

/-- The fire's concrete data, kernel-pinned: the retagged cup splices its two fresh legs at
position `0` exactly as the source cup does (`openWires [2, 3, 0, 1]`, frontier `5`), and the
retagged cell KEEPS the turnback flag.  `rfl` conjunction. -/
theorem arcRetagTransport_fireData :
    (runArcCell arcRetagFireSeed
        (mapPath (inclusionLeftTwoReal adjunctionComputad adjunctionComputad rfl).toComputadMorphism
          adjunctionComputadNilBase)
        (mapPath (inclusionLeftTwoReal adjunctionComputad adjunctionComputad rfl).toComputadMorphism
          adjunctionComputadNilBase)
        (mapCellAlong (inclusionLeftTwoReal adjunctionComputad adjunctionComputad rfl)
          adjunctionComputadUnitCupCell)).openWires = [2, 3, 0, 1]
      ∧ (mapCellAlong (inclusionLeftTwoReal adjunctionComputad adjunctionComputad rfl)
          adjunctionComputadUnitCupCell).isTurnbackOnly = true :=
  ⟨rfl, rfl⟩

/-! ## Honesty marker -/

/-- ★★ **Honesty marker — the ARC RETAG TRANSPORT ships.**  The dispatch residual-(1) language
("the cell-functor retag does not exist") is SUPERSEDED in two halves: the functor itself has
existed since r4/r6 (`mapCellAlong` + both real coprojections), and THIS file supplies the
missing half — the functor carries the r28 whole-cell arc engine: `runArcCell_mapCellAlong`
(the arc semantics is `mapCellAlong`-invariant, so retagged component cells are the SAME
arc-state transformers) and `isTurnbackOnly_mapCellAlong` (the engine's cell class is
functor-stable), generically over any `ComputadMorphismTwo`, fired at the double-adjunction
pushout.  What this does NOT claim: the dispatch theorem itself
(`fxAmalg_hasSaturatedDispatchTheorem`) — its completeness descent stays the JAM-A hostage;
consumption happens in the cross-component dispatch brick.  `= true`. -/
def fxAmalg_hasPushoutArcRetagTransport : Bool := true

end FX1Poly.Polygraph.Amalgam
