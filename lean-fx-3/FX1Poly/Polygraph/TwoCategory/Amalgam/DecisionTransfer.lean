import FX1Poly.Polygraph.TwoCategory.Amalgam.Modularity
import FX1Poly.Polygraph.TwoCategory.Amalgam.DeciderReseat

/-! # Polygraph/TwoCategory/Amalgam/DecisionTransfer — the decision transfer, the concrete demonstrator (BOTH
verdicts), and the OMEGA-5 cell-side handoff (WP-AMALG-2 r1, B3)

The payoff of the modularity theorem (B2) at the DECISION level: the pushout's saturated convertibility is
`Decidable` from the component decisions, and — for the disjoint scope — the decider is TOTAL and computes both
verdicts.  This file (i) routes the decision transfer THROUGH the B2 biconditional, (ii) exercises the concrete
`involution +_M monad` demonstrator on the DISPATCH-MAP images (both verdicts, fresh), and (iii) states the
OMEGA-5 cell-side handoff — the amalgamated-product tensor `⊗_k` OMEGA-5's enriched-check needs, now inhabited by
the soundness functor.

## The decision transfer (through B2)

`involutionMonadPushoutDecisionViaModularity` decides `SaturatedConvOver involutionMonadPushout crossPairPushoutRel`
by deciding the FREE `TwoCellConvFull` (the FREE-7 decision `decideTwoCellConvFull` over the reconstructed
signature's free `DecidableEq` data) and transporting the verdict across the B2 biconditional
`involutionMonadPushoutConvIffFree`.  This is the Decidable-for-the-pushout-from-the-components with the transfer
made explicit through the modularity theorem, not through an internal iff.

## The concrete demonstrator, BOTH verdicts (the recon pick)

The LIVE recon pick is `ComposableFragmentDispatch.involutionMonadEmptyRowsDispatch` (the real walking-involution
walker stored as `dl`, the free monad decider as `dr`).  Here its combined decider is exercised on the DISPATCH-MAP
IMAGES directly — the un-whiskered monad faces δ₁ (`pushoutFaceDeltaOne`) and δ₀ (`pushoutFaceDeltaZero`),
parallel by definitional `t·id = t`: δ₁ vs δ₀ decides `isFalse` (distinct monotone maps `[1]` / `[0]`), δ₁ vs δ₁
decides `isTrue`.  Fresh verdicts (not the s-whiskered `crossPair` pair), tying B3 straight to B1's dispatch map.
The modularity-routed decider reproduces both on the s-whiskered pair.

## The `fxAmalg_hasDispatchTheorem` flip — HELD (honest)

`Dispatch.lean`'s `DispatchDecidability` records the combined decider at the interface `DecidableTwoCellConvFor`
= `Decidable (TwoCellConv …)` — the PLAIN RST-closure of the 3-cell rewrite, WITHOUT the completed interchange /
whisker functoriality.  Its total decider is the deferred Gratzer convergence
(`fxMode_hasConvergentThreeCellSystem = false`); the shipped `decideTwoCellConvFull` decides the strictly LARGER
`TwoCellConvFull`, which does NOT transfer to the plain `TwoCellConv`.  So `DispatchDecidability`'s combined-decider
arrow is NOT hypothesis-free inhabitable, and `fxAmalg_hasDispatchTheorem` STAYS `false` — the flip is NOT
fabricated.  The honest, achievable interface is the SATURATED one (`DecidableSaturatedConvForRel`), where the
transfer DOES ship (`fxAmalg_hasComposableFragmentDispatch = true`, this file's decider).

## The OMEGA-5 cell-side handoff

`Omega/Graded/GradedCompositionLedger.lean`'s jam `fxOmega5_enrichedFunctorCellSideReached = false` names its blocking
node as `fxAmalg_hasDispatchTheorem` (the FULL decidability).  But the OMEGA-5 cell-side functor `check (a *_k b) =
check a ⊗_k check b` needs only the SOUNDNESS functor — the amalgamated-product object
`(pushoutShared, SaturatedConvOverPushout)`, the arrow `⊗_k = mapCellAlong`, and the composition law
`mapCellAlong_preservesConvUnconditional` — all of which SHIP.  This file packages that arrow
(`omegaFiveTensorSoundnessLeft` / `omegaFiveTensorSoundnessRight` / `omegaFiveTensorComposition`) under
OMEGA-5-facing names as the handoff: the arrow OMEGA-5 waits on is inhabited without the full-decidability wall.
(This file edits NOTHING in the Omega lane; it states the handoff on the Amalgam side.)

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The decision transfer, routed through the B2 biconditional -/

/-- ★ **The decision transfer through modularity** — a TOTAL decider for the `involution +_M monad` pushout's
saturated convertibility, obtained by deciding the FREE `TwoCellConvFull` (FREE-7's `decideTwoCellConvFull` over the
reconstructed signature's free `DecidableEq` data) and transporting each verdict across the B2 biconditional
`involutionMonadPushoutConvIffFree`.  The Decidable-for-the-pushout-from-the-components, with the transfer made
explicit through the modularity theorem. -/
def involutionMonadPushoutDecisionViaModularity :
    DecidableSaturatedConvForRel involutionMonadPushout.toModeSignature crossPairPushoutRel :=
  fun cellAlpha cellBeta =>
    match decideTwoCellConvFull (reconstructedSignatureModeDecEq involutionMonadPushout)
        (reconstructedSignatureModalityDecEq involutionMonadPushout)
        (reconstructedSignatureTwoCellDecEq involutionMonadPushout) cellAlpha cellBeta with
    | isTrue full => isTrue ((involutionMonadPushoutConvIffFree cellAlpha cellBeta).mpr full)
    | isFalse notFull =>
        isFalse (fun conv => notFull ((involutionMonadPushoutConvIffFree cellAlpha cellBeta).mp conv))

/-! ## The concrete demonstrator, BOTH verdicts — on the DISPATCH-MAP images -/

/-- The shipped combined decider (`involutionMonadEmptyRowsDispatch`) on the dispatch-map image faces δ₁ vs δ₀
(the un-whiskered monad faces `pushoutFaceDeltaOne` / `pushoutFaceDeltaZero`, parallel by `t·id = t`), read as a
`Bool`.  Expect `false`: distinct Δ-monotone maps `[1]` / `[0]`. -/
def dispatchedFaceSeparatingVerdict : Bool :=
  match involutionMonadEmptyRowsDispatch.combinedDecider pushoutFaceDeltaOne pushoutFaceDeltaZero with
  | isTrue _ => true
  | isFalse _ => false

/-- The shipped combined decider on δ₁ vs δ₁, read as a `Bool`.  Expect `true`: a cell is convertible to itself. -/
def dispatchedFaceReflexiveVerdict : Bool :=
  match involutionMonadEmptyRowsDispatch.combinedDecider pushoutFaceDeltaOne pushoutFaceDeltaOne with
  | isTrue _ => true
  | isFalse _ => false

/-- The modularity-routed decider on the s-whiskered interleaving pair `crossPairAlpha` vs `crossPairBeta`, read as
a `Bool`.  Expect `false`: reproduces the separation through the B2 transfer. -/
def modularityDecisionSeparatingVerdict : Bool :=
  match involutionMonadPushoutDecisionViaModularity crossPairAlpha crossPairBeta with
  | isTrue _ => true
  | isFalse _ => false

/-- The modularity-routed decider on the reflexive pair `crossPairAlpha` vs `crossPairAlpha`, read as a `Bool`.
Expect `true`. -/
def modularityDecisionReflexiveVerdict : Bool :=
  match involutionMonadPushoutDecisionViaModularity crossPairAlpha crossPairAlpha with
  | isTrue _ => true
  | isFalse _ => false

-- The dispatch-map faces δ₁ vs δ₀ separate: expect `false`.
#eval dispatchedFaceSeparatingVerdict
-- The dispatch-map face δ₁ vs itself: expect `true`.
#eval dispatchedFaceReflexiveVerdict
-- The modularity-routed decision separates the s-whiskered interleaving pair: expect `false`.
#eval modularityDecisionSeparatingVerdict
-- The modularity-routed decision on the reflexive pair: expect `true`.
#eval modularityDecisionReflexiveVerdict

/-! ## The OMEGA-5 cell-side handoff — the amalgamated-product tensor `⊗_k`, inhabited -/

/-- ★ **The `⊗_k` composition law OMEGA-5 consumes** — the amalgamated-product tensor arrow `⊗_k = mapCellAlong`
preserves convertibility UNCONDITIONALLY: a component (block) convertibility transports to a pushout convertibility
of the images.  Re-exposed under the OMEGA-5-facing name as the enriched-check cell-side composition
`check (a *_k b) = check a ⊗_k check b`.  This is `mapCellAlong_preservesConvUnconditional`, the composition law
the OMEGA-5 cell-side functor waits on — it SHIPS, so the cell-side is NOT gated on the full decidability the jam's
NAMED node pointed at. -/
theorem omegaFiveTensorComposition {source target : ModeComputad}
    (morphism : ComputadMorphismTwo source target)
    {baseRelSrc : CellRel source.toModeSignature} {baseRelTgt : CellRel target.toModeSignature}
    (rowMap : {sourceMode targetMode : Fin source.modeCount} →
      {sourcePath targetPath : ModalityPath source.toModeGraph sourceMode targetMode} →
      {cellA cellB : RawTwoCellExpr source.toModeSignature sourcePath targetPath} →
      baseRelSrc cellA cellB →
      baseRelTgt (mapCellAlong morphism cellA) (mapCellAlong morphism cellB))
    {sourceMode targetMode : Fin source.modeCount}
    {sourcePath targetPath : ModalityPath source.toModeGraph sourceMode targetMode}
    {cellAlpha cellBeta : RawTwoCellExpr source.toModeSignature sourcePath targetPath}
    (conv : SaturatedConvOver source.toModeSignature baseRelSrc cellAlpha cellBeta) :
    SaturatedConvOver target.toModeSignature baseRelTgt
      (mapCellAlong morphism cellAlpha) (mapCellAlong morphism cellBeta) :=
  mapCellAlong_preservesConvUnconditional morphism rowMap conv

/-- ★ **The `⊗_k` LEFT leg, inhabited concretely** — a component-1 (involution block) convertibility transports into
the `involution +_M monad` amalgam by the soundness functor (`pushoutPreservesConvLeft`).  A concrete inhabitant of
the OMEGA-5 tensor arrow on the left factor. -/
def omegaFiveTensorSoundnessLeft :=
  pushoutPreservesConvLeft involutionMonadSameModes
    (inclusionLeftTwo involutionComputad monadComputad involutionMonadSameModes rfl)
    (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes)
    (emptyCellRel involutionComputad.toModeSignature)
    (emptyCellRel monadComputad.toModeSignature)
    (SaturatedConvOver.refl (RawTwoCellExpr.id (signature := involutionComputad.toModeSignature)
      (ModalityPath.nil (graph := involutionComputad.toModeGraph) (⟨0, by decide⟩ : Fin 1))))

/-- ★ **The `⊗_k` RIGHT leg, inhabited concretely on a real monad law** — the monad unit's RIGHT-whisker law
`eta ▷ id ≈ eta` (a genuine, non-reflexive component convertibility) transports into the amalgam by the soundness
functor (`pushoutPreservesConvRight`).  A concrete inhabitant of the OMEGA-5 tensor arrow on the real-2-generator
right factor. -/
def omegaFiveTensorSoundnessRight :=
  pushoutPreservesConvRight involutionMonadSameModes
    (inclusionLeftTwo involutionComputad monadComputad involutionMonadSameModes rfl)
    (inclusionRightTwoReal involutionComputad monadComputad involutionMonadSameModes)
    (emptyCellRel involutionComputad.toModeSignature)
    (emptyCellRel monadComputad.toModeSignature)
    (SaturatedConvOver.ofFull
      (TwoCellConvFull.whiskerRightUnit
        (RawTwoCellExpr.gen (signature := monadComputad.toModeSignature) monadComputadReconstructsUnit)))

/-! ## Honesty markers -/

/-- ★ **Honesty marker — the DECISION TRANSFER ships (B3).**  The pushout's saturated convertibility is decided
FROM the components: `involutionMonadPushoutDecisionViaModularity` routes the FREE-7 decision through the B2
biconditional; the concrete `involution +_M monad` demonstrator computes BOTH verdicts on the dispatch-map images
(`dispatchedFaceSeparatingVerdict = false`, `dispatchedFaceReflexiveVerdict = true`) and on the s-whiskered pair
through the transfer (`modularityDecisionSeparatingVerdict = false`, `modularityDecisionReflexiveVerdict = true`).
Empty-law / disjoint scope, matching B2.  `= true`. -/
def fxAmalg_hasDecisionTransfer : Bool := true

/-- ★ **Honesty marker — the OMEGA-5 cell-side handoff is INHABITED.**  The amalgamated-product tensor `⊗_k` the
OMEGA-5 enriched-check cell-side needs (`check (a *_k b) = check a ⊗_k check b`) is the SOUNDNESS functor —
`mapCellAlong` with composition law `mapCellAlong_preservesConvUnconditional` (`omegaFiveTensorComposition`) and both
legs concretely inhabited at the witness pushout (`omegaFiveTensorSoundnessLeft` on the involution block,
`omegaFiveTensorSoundnessRight` on a real monad law).  The jam `fxOmega5_enrichedFunctorCellSideReached`'s NAMED
node `fxAmalg_hasDispatchTheorem` (FULL decidability) is the WRONG gate — the cell-side functor needs SOUNDNESS, which
ships.  OMEGA-6 can wire `⊗_k` to this arrow rather than wait on completeness.  `= true`. -/
def fxAmalg_hasOmegaFiveCellSideHandoff : Bool := true

/-- **Honesty marker — `fxAmalg_hasDispatchTheorem` STAYS walled (NOT flipped).**  `DispatchDecidability`'s combined
decider lives at the PLAIN `DecidableTwoCellConvFor` = `Decidable (TwoCellConv …)` interface, whose total decider is
the deferred Gratzer convergence (`fxMode_hasConvergentThreeCellSystem = false`); the shipped `decideTwoCellConvFull`
decides the strictly LARGER `TwoCellConvFull` and does NOT transfer to plain `TwoCellConv`.  So the arrow is NOT
hypothesis-free inhabitable and the flip is HELD — honest.  The achievable transfer is the SATURATED one
(`fxAmalg_hasDecisionTransfer` / `fxAmalg_hasComposableFragmentDispatch`).  `= true` — the wall STANDS
(the r1 verifier caught the original `:= false` as a telling-word polarity violation: the name asserts
"stays walled", so the honest value while the wall stands is `true`). -/
def fxAmalg_dispatchTheoremStaysWalled : Bool := true

end FX1Poly.Polygraph.Amalgam
