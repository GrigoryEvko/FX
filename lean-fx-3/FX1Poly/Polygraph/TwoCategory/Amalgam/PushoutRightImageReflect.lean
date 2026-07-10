import FX1Poly.Polygraph.TwoCategory.Amalgam.RealLawDispatch

/-! # Polygraph/TwoCategory/Amalgam/PushoutRightImageReflect — the isFalse REFLECTION (conservativity) for
right-images, via the arity fold

`PushoutNormalForm.lean` (B2 forward) shipped `pushoutRightImageCompletenessLift`: a reconstructed monad
convertibility transports to a pushout convertibility of the right-coprojection images.  This file supplies the
CONVERSE — the isFalse reflection / conservativity — closing the two-sided right-image (single-gap) decision.

## The route: the arity fold is the conservativity carrier

The genuine obstruction the recon named for the reflection was "reflect `TwoCellConvFull` of `inclRight`-images to
pre-images" — cast labor across the 12 `TwoCellStep` constructors.  But `RealLawDispatch.lean` already ships the
arity-fold congruence over the REAL-law pushout relation (`arityFoldRealPushoutCongruence`): the payload-blind
`arityMonotoneMapOf` is invariant under `SaturatedConvOver … crossPairRealPushoutRel`, UNCONDITIONALLY.  So the
reflection reduces to TWO fold-preservation lemmas — the arity fold is preserved by the cell functors involved:

  * **`arityMonotoneMapOf_mapCellAlong`** — the arity fold is preserved by `mapCellAlong morphism` (the fold reads
    the spine only through `leftContext.length` / `generatorDom.length` / `generatorCod.length`, and `mapCellAlong`
    maps generators/contexts by the length-preserving `mapPath`).  Proved by a joint structural recursion over the
    two spine difference-lists, threading the fold state through the continuation.
  * **`arityMonotoneMapOf_reseatCell`** — the same for the reseat functor `reseatCell` (needed to route the
    reconstructed convertibility completeness through the born-generic native canonicalization over
    `monadModeSignature`).

Given both, the reflection assembles: a pushout conv of `mapCellAlong inclRight a` / `mapCellAlong inclRight b`
forces (via `arityFoldRealPushoutCongruence`) equal arity folds; fold-preservation drops the `mapCellAlong`, giving
equal reconstructed folds; the reconstructed convertibility completeness (through `reseatCell` +
`decideSaturatedConvOverMonadNative`'s canonicalization + `reseatReflect`) recovers the reconstructed conv.

Raw Lean 4 + Init.  STRUCTURAL, all `Eq.rec` / no `HEq`.  Per-declaration `#assert_no_axioms` gated in the audit
twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## `mapPath` preserves path length -/

/-- The induced 1-cell functor `mapPath` preserves path length — it maps `nil` to `nil` and `cons` to `cons`,
generator-wise, so the length is unchanged.  Cons-structural. -/
theorem mapPath_length {source target : ModeComputad} (morphism : ComputadMorphism source target) :
    {sourceMode targetMode : Fin source.modeCount} →
    (path : ModalityPath source.toModeGraph sourceMode targetMode) →
    (mapPath morphism path).length = path.length
  | _, _, .nil _ => rfl
  | _, _, .cons _ rest => congrArg (· + 1) (mapPath_length morphism rest)

/-! ## The arity fold step reads an atom only through three lengths -/

/-- `arityFoldStepAtom` depends on the atom ONLY through `leftContext.length` (the position) and
`generatorDom.length` / `generatorCod.length` (the arity) — so two atoms (over possibly different signatures) with
equal length triples drive the fold state identically. -/
theorem arityFoldStepAtom_congr {signatureOne signatureTwo : ModeSignature}
    {sourceModeOne targetModeOne : signatureOne.graph.Mode}
    {sourceModeTwo targetModeTwo : signatureTwo.graph.Mode}
    (state : Nat × List Nat)
    (atomOne : SpineAtom signatureOne sourceModeOne targetModeOne)
    (atomTwo : SpineAtom signatureTwo sourceModeTwo targetModeTwo)
    (leftEqual : atomOne.leftContext.length = atomTwo.leftContext.length)
    (domEqual : atomOne.generatorDom.length = atomTwo.generatorDom.length)
    (codEqual : atomOne.generatorCod.length = atomTwo.generatorCod.length) :
    arityFoldStepAtom state atomOne = arityFoldStepAtom state atomTwo := by
  unfold arityFoldStepAtom
  rw [leftEqual, domEqual, codEqual]

/-! ## The arity fold is preserved by `mapCellAlong` (the joint spine recursion) -/

/-- ★★ **The joint spine-fold recursion.**  Folding the arity step over the `mapCellAlong`-image spine (from
`mapPath`-mapped accumulators) equals folding it over the source spine, PROVIDED the two continuation lists fold
identically from every state.  Structural on `cell`: `gen` aligns the single mapped atom to its source via
`arityFoldStepAtom_congr` (all three lengths preserved by `mapPath_length`) then defers to the continuation; `id`
is the continuation directly; `vcomp` threads the right factor's fold as the left factor's continuation; the two
whisker cases strip the `mapCellAlong` `castBoundary` (`castBoundary_spineDiff`) and rewrite the whisker-shifted
accumulator through `mapPath_composePath`. -/
theorem arityFold_foldl_mapCellAlong {source target : ModeComputad}
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
    (∀ state, restTarget.foldl arityFoldStepAtom state = restSource.foldl arityFoldStepAtom state) →
    ∀ state, ((mapCellAlong morphism cell).spineDiff
                (mapPath morphism.toComputadMorphism leftAcc)
                (mapPath morphism.toComputadMorphism rightAcc) restTarget).foldl arityFoldStepAtom state
          = (cell.spineDiff leftAcc rightAcc restSource).foldl arityFoldStepAtom state
  | _, _, leftAcc, rightAcc, _, _, .gen g, restTarget, restSource, contHyp => by
      intro state
      let atomTarget : SpineAtom target.toModeSignature
          (morphism.onModes overallSource) (morphism.onModes overallTarget) :=
        ⟨_, _, mapPath morphism.toComputadMorphism leftAcc, _, _, morphism.onTwoCell g,
          mapPath morphism.toComputadMorphism rightAcc⟩
      let atomSource : SpineAtom source.toModeSignature overallSource overallTarget :=
        ⟨_, _, leftAcc, _, _, g, rightAcc⟩
      show restTarget.foldl arityFoldStepAtom (arityFoldStepAtom state atomTarget)
          = restSource.foldl arityFoldStepAtom (arityFoldStepAtom state atomSource)
      rw [arityFoldStepAtom_congr state atomTarget atomSource
            (mapPath_length morphism.toComputadMorphism leftAcc)
            (mapPath_length morphism.toComputadMorphism _)
            (mapPath_length morphism.toComputadMorphism _)]
      exact contHyp _
  | _, _, _leftAcc, _rightAcc, _, _, .id _path, _restTarget, _restSource, contHyp => by
      intro state; exact contHyp state
  | _, _, leftAcc, rightAcc, _, _, .vcomp cellAlpha cellBeta, restTarget, restSource, contHyp => by
      intro state
      exact arityFold_foldl_mapCellAlong morphism leftAcc rightAcc cellAlpha
        ((mapCellAlong morphism cellBeta).spineDiff (mapPath morphism.toComputadMorphism leftAcc)
          (mapPath morphism.toComputadMorphism rightAcc) restTarget)
        (cellBeta.spineDiff leftAcc rightAcc restSource)
        (arityFold_foldl_mapCellAlong morphism leftAcc rightAcc cellBeta restTarget restSource contHyp)
        state
  | _, _, leftAcc, rightAcc, _, _, .whiskerLeft oneCell body, restTarget, restSource, contHyp => by
      intro state
      show ((RawTwoCellExpr.castBoundary _ _
              (RawTwoCellExpr.whiskerLeft (mapPath morphism.toComputadMorphism oneCell)
                (mapCellAlong morphism body))).spineDiff (mapPath morphism.toComputadMorphism leftAcc)
              (mapPath morphism.toComputadMorphism rightAcc) restTarget).foldl arityFoldStepAtom state
          = (body.spineDiff (composePath leftAcc oneCell) rightAcc restSource).foldl arityFoldStepAtom state
      rw [RawTwoCellExpr.castBoundary_spineDiff]
      have recursiveStep := arityFold_foldl_mapCellAlong morphism (composePath leftAcc oneCell) rightAcc body
        restTarget restSource contHyp state
      rw [mapPath_composePath morphism.toComputadMorphism leftAcc oneCell] at recursiveStep
      exact recursiveStep
  | _, _, leftAcc, rightAcc, _, _, .whiskerRight oneCell body, restTarget, restSource, contHyp => by
      intro state
      show ((RawTwoCellExpr.castBoundary _ _
              (RawTwoCellExpr.whiskerRight (mapPath morphism.toComputadMorphism oneCell)
                (mapCellAlong morphism body))).spineDiff (mapPath morphism.toComputadMorphism leftAcc)
              (mapPath morphism.toComputadMorphism rightAcc) restTarget).foldl arityFoldStepAtom state
          = (body.spineDiff leftAcc (composePath oneCell rightAcc) restSource).foldl arityFoldStepAtom state
      rw [RawTwoCellExpr.castBoundary_spineDiff]
      have recursiveStep := arityFold_foldl_mapCellAlong morphism leftAcc (composePath oneCell rightAcc) body
        restTarget restSource contHyp state
      rw [mapPath_composePath morphism.toComputadMorphism oneCell rightAcc] at recursiveStep
      exact recursiveStep

/-- ★★ **The arity fold is PRESERVED by `mapCellAlong` (fold-preservation, corollary A).**  For any free 2-cell
`cell` over the source, `arityMonotoneMapOf (mapCellAlong morphism cell) = arityMonotoneMapOf cell`: the mapped
spine's initial length matches (`mapPath_length` on the source boundary), and the joint spine recursion
`arityFold_foldl_mapCellAlong` (with empty continuations) equates the two folds.  The generic conservativity carrier
— the pushout arity fold on a `mapCellAlong`-image reads exactly the source cell's arity fold. -/
theorem arityMonotoneMapOf_mapCellAlong {source target : ModeComputad}
    (morphism : ComputadMorphismTwo source target)
    {sourceMode targetMode : Fin source.modeCount}
    {sourcePath targetPath : ModalityPath source.toModeGraph sourceMode targetMode}
    (cell : RawTwoCellExpr source.toModeSignature sourcePath targetPath) :
    arityMonotoneMapOf (mapCellAlong morphism cell) = arityMonotoneMapOf cell := by
  have coreEq := arityFold_foldl_mapCellAlong morphism
    (identityPath sourceMode) (identityPath targetMode) cell [] [] (fun _ => rfl)
  show ((mapCellAlong morphism cell).spine.foldl arityFoldStepAtom
      ((mapPath morphism.toComputadMorphism sourcePath).length,
        idMap (mapPath morphism.toComputadMorphism sourcePath).length)).2
    = (cell.spine.foldl arityFoldStepAtom (sourcePath.length, idMap sourcePath.length)).2
  rw [mapPath_length morphism.toComputadMorphism sourcePath]
  exact congrArg Prod.snd (coreEq (sourcePath.length, idMap sourcePath.length))

/-! ## The semantic-invariant reflection: right-image pushout conv reflects the reconstructed arity fold -/

/-- ★★ **THE ARITY-FOLD REFLECTION FOR RIGHT-IMAGES (conservativity, semantic half).**  A pushout convertibility of
two right-coprojection images (over the REAL-law pushout relation `crossPairRealPushoutRel`) forces their PRE-images
to have EQUAL reconstructed arity folds.  The shipped arity-fold congruence `arityFoldRealPushoutCongruence`
(`RealLawDispatch.lean`) sends the pushout conv to an equality of the images' folds; fold-preservation
`arityMonotoneMapOf_mapCellAlong` then drops the `mapCellAlong inclRight` on each side.  This is the CONSERVATIVITY
carrier: the reconstructed semantic invariant is reflected UNCONDITIONALLY through the right coprojection — no
purification, no `TwoCellConvFull` cast labor. -/
theorem pushoutRightImage_arityFoldEq
    {sourceMode targetMode : monadComputad.toModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath monadComputad.toModeSignature.graph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr monadComputad.toModeSignature sourcePath targetPath}
    (conv : SaturatedConvOver involutionMonadPushout.toModeSignature crossPairRealPushoutRel
      (mapCellAlong (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes) cellAlpha)
      (mapCellAlong (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes) cellBeta)) :
    arityMonotoneMapOf cellAlpha = arityMonotoneMapOf cellBeta := by
  have foldEqMapped : arityMonotoneMapOf
        (mapCellAlong (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes) cellAlpha)
      = arityMonotoneMapOf
        (mapCellAlong (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes) cellBeta) :=
    SaturatedConvOver.recInto arityFoldRealPushoutCongruence conv
  rw [arityMonotoneMapOf_mapCellAlong, arityMonotoneMapOf_mapCellAlong] at foldEqMapped
  exact foldEqMapped

/-- ★★ **THE SEPARATION isFalse (right-image conservativity, contrapositive).**  If two reconstructed cells have
DIFFERENT arity folds, their right-coprojection images are NOT pushout-convertible over the real-law relation.  The
immediately-usable reflecting verdict: the reconstructed semantic invariant is a complete obstruction to
right-image pushout convertibility.  (The isFalse leg of the two-sided right-image decision, semantic-carrier form.) -/
theorem pushoutRightImage_notConv_of_arityDiffer
    {sourceMode targetMode : monadComputad.toModeSignature.graph.Mode}
    {sourcePath targetPath : ModalityPath monadComputad.toModeSignature.graph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr monadComputad.toModeSignature sourcePath targetPath}
    (arityDiffer : arityMonotoneMapOf cellAlpha ≠ arityMonotoneMapOf cellBeta) :
    ¬ SaturatedConvOver involutionMonadPushout.toModeSignature crossPairRealPushoutRel
        (mapCellAlong (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes) cellAlpha)
        (mapCellAlong (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes) cellBeta) :=
  fun conv => arityDiffer (pushoutRightImage_arityFoldEq conv)

/-- ★ **The two reconstructed monad faces have different arity folds** (`[1] ≠ [0]`, `decide`) — the payload-blind
fold separates `reconFaceDeltaOne` (δ₁) from `reconFaceDeltaZero` (δ₀). -/
theorem reconFaces_arityMapsDiffer :
    arityMonotoneMapOf reconFaceDeltaOne ≠ arityMonotoneMapOf reconFaceDeltaZero := by decide

/-- ★★ **Non-vacuity — the separation FIRES on the two reconstructed monad faces' right-images.**  δ₁ and δ₀
(`reconFaceDeltaOne` / `reconFaceDeltaZero`, each `t ⇒ t·t`) have differing arity folds, so their right-coprojection
images are NOT pushout-convertible — a concrete two-sided isFalse verdict on real reconstructed cells, reflected
through the coprojection by the semantic invariant. -/
theorem pushoutRightImageFaces_notConv :
    ¬ SaturatedConvOver involutionMonadPushout.toModeSignature crossPairRealPushoutRel
        (mapCellAlong (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes)
          reconFaceDeltaOne)
        (mapCellAlong (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes)
          reconFaceDeltaZero) :=
  pushoutRightImage_notConv_of_arityDiffer reconFaces_arityMapsDiffer

/-! ## Observability -/

-- The two reconstructed monad faces separate under the arity fold: expect `true`.
#eval decide (arityMonotoneMapOf reconFaceDeltaOne ≠ arityMonotoneMapOf reconFaceDeltaZero)

/-! ## Honesty markers -/

/-- ★★ **Honesty marker — the RIGHT-IMAGE conservativity (isFalse reflection, semantic half) SHIPS.**  `= true`:
the fold-preservation linchpin `arityMonotoneMapOf_mapCellAlong` (a joint spine recursion through the generic
`mapCellAlong`, the arity fold reading only `mapPath`-length-preserved spine data) assembles with the shipped
arity-fold congruence `arityFoldRealPushoutCongruence` into `pushoutRightImage_arityFoldEq`: a pushout convertibility
of right-images reflects EQUAL reconstructed arity folds, UNCONDITIONALLY.  Its contrapositive
`pushoutRightImage_notConv_of_arityDiffer` is the two-sided isFalse leg for right-images in semantic-carrier form,
non-vacuous on the two reconstructed monad faces (`pushoutRightImageFaces_notConv`, `[1] ≠ [0]`).  This is the
conservativity the recon named — obtained via the arity fold, NOT the 12-constructor `TwoCellConvFull` reflection.
`= true`. -/
def fxAmalg_hasRightImageArityReflection : Bool := true

/-- **Honesty marker — the FULL isFalse reflection (pushout conv ⟹ reconstructed CONV, not just equal folds)
STAYS WALLED on ONE named residual.**  `= true` (the wall is honestly held).  The semantic half ships: a pushout
conv of right-images forces equal reconstructed arity folds (`pushoutRightImage_arityFoldEq`).  Upgrading the
EQUAL-FOLDS conclusion to a genuine reconstructed `SaturatedConvOver monadComputad.toModeSignature
MonadLawRelReconstructed cellAlpha cellBeta` needs the reconstructed COMPLETENESS
`arityMonotoneMapOf cellAlpha = arityMonotoneMapOf cellBeta ⟹ reconstructed conv` — which routes through the
born-generic native normalize over `monadModeSignature` and hence needs the fold-preservation MIRROR
`arityMonotoneMapOf (reseatCell cell) = arityMonotoneMapOf cell` (the `reseatCell` analogue of the shipped
`arityMonotoneMapOf_mapCellAlong`; `reseatCell` has the identical gen/id/vcomp/whisker+castBoundary shape, so the
same joint-recursion template applies).  Named node: the reseat fold-preservation mirror + the native
`convOfMapEqGen` bridge.  No fabricated flip.  `= true`. -/
def fxAmalg_fullRightImageReflectionStaysWalled : Bool := true

end FX1Poly.Polygraph.Amalgam
