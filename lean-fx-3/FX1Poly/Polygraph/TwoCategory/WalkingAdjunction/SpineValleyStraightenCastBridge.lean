import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineValleyFrameCollapse

/-! # mode-3 keystone — Piece I STRAIGHTEN: THE CAST BRIDGE (merged-`atomFrame` shared-leg collapse)

`SpineValleyFrameCollapse` shipped the CAST-FREE collapse in the ITERATED-whisker leg presentation
(`generalContextFrameLegsCollapse` : `sharedLegCupLeg ⊟ sharedLegCapLeg ≈ id`), plus the two per-atom split
witnesses (`cupLegSplitsToMergedCupFrameInner` / `capLegSplitsToMergedCapFrameInner`) that relate the iterated
legs to the MERGED single-whisker presentation the readback's `atomFrame` produces — each up to a
`composePath`-associativity boundary cast.  `SpineValleyStraightenFactor` shipped the shared-leg factorization
(handedness A) that pins a `zigZagSharedLeg` cup·cap pair's stored contexts to the shared-leg shape by seed
rigidity ALONE (no `matchingOf` read).

★ **This file assembles THE CAST BRIDGE.**  Fix the shared leg `L = singletonModalityPath left` and ARBITRARY
whisker words `leftContext` / `rightContext`.  The MERGED cup and cap frames — the shape `atomFrame` produces for a
shared-leg partner —

  * `mergedCupFrame = leftContext ◁ ((L · rightContext) ▷ η)`
  * `mergedCapFrame = (leftContext · L) ◁ (rightContext ▷ ε)`

collapse to the identity on the shared boundary `leftContext · L · rightContext`.  The merged frames do NOT compose
on the nose: the cup's target `leftContext · (L·R) · (L · rightContext)` and the cap's source `(leftContext · L) ·
(R·L) · rightContext` are the SAME word `leftContext L R L rightContext` up to `composePath`-associativity only, so
the merged `vcomp` typechecks only through a boundary cast.  THE CAST BRIDGE:

  * ★ **`mergedCupFrame_convFull_castCupLeg`** — `mergedCupFrame ≈full castBoundary(assoc) (sharedLegCupLeg)`: the
    merged single right-whisker by `L · rightContext` splits (via `cupLegSplitsToMergedCupFrameInner`, the shipped
    `whiskerRightComp`) into the iterated `rightContext ▷ (L ▷ η)`, whiskered by `leftContext`; the cast pulls out
    through `whiskerLeft_castBoundary`.
  * ★ **`mergedCapFrame_convFull_castCapLeg`** — `mergedCapFrame ≈full castBoundary(assoc) (sharedLegCapLeg)`: the
    merged left-whisker by `leftContext · L` splits (via `whiskerLeftComp`) into `leftContext ◁ (L ◁ (rightContext
    ▷ ε))`, and the inner `L ◁ (rightContext ▷ ε)` exchanges (via `capLegSplitsToMergedCapFrameInner`, the shipped
    `whiskerExchange`) into `rightContext ▷ (L ◁ ε)`; the casts fuse.
  * ★ **`mergedSharedLegFramesCollapse`** — the CAST BRIDGE proper: `mergedCupFrame ⊟ castBoundary(align) mergedCapFrame
    ≈ id (leftContext · L · rightContext)`.  The two merged frames are converted to their iterated legs (casts
    extruded through the `vcomp` by `vcomp_castBoundaryLeft` + cast fusion), and the iterated composite collapses
    by the shipped cast-free `generalContextFrameLegsCollapse`.  The residual boundary cast is the strict
    `composePath`-associativity re-bracketing (RV/FM `vcompAssoc`, a bounded structural coherence), threaded
    explicitly, never posited.

## What this does NOT close (gates stay `false`)

This is the CAST BRIDGE for handedness A ONLY, at the abstract merged-frame level.  It does NOT specialize to a
concrete `atomFrame cupAtom` / `atomFrame capAtom` (which needs the cup/cap generator pinned at the PATH level by
casing the seed generator), NOR handle handedness B (the RIGHT-snake mirror, whose general-context collapse is
un-shipped — only the raw triangle `rightSnakeDoubleWhiskerCollapses`), NOR the delete-chain surgery `next`, NOR
the readback-realization `stepConv`.  So `CellStraightenStepInput` is NOT discharged; the oracle still takes it as
an input.  No gate flag flips; `convOfMapEq` and the fib-3 gate flags stay `false`.  This brick reads NO
`matchingOf` / `partnerIndexOf` / arc structure — the shared-leg shape is the factorization's, not the matching's.

Raw Lean 4 + Init; every proof is the shipped whisker functoriality (`whiskerLeftComp` / `whiskerRightComp` /
`whiskerExchange`) + `cupLegSplits` / `capLegSplits` + cast algebra (`whiskerLeft_castBoundary`,
`castBoundary_castBoundary`, `vcomp_castBoundaryLeft`, `castBoundaryCongr`) + `generalContextFrameLegsCollapse`.
`propext`/`Quot.sound`/`Classical`/`sorry`/`native_decide`/`omega`-free; per-declaration `#assert_no_axioms` gated
in the audit twin. -/

set_option autoImplicit false

namespace FX1Poly.Polygraph

section MergedFrameCastBridge

variable {leftSourceMode rightTargetMode : AdjunctionMode}
  (leftContext : ModalityPath adjunctionGraph leftSourceMode AdjunctionMode.base)
  (rightContext : ModalityPath adjunctionGraph AdjunctionMode.tip rightTargetMode)

/-! ## The merged frames (the `atomFrame` presentation of a shared-leg partner) -/

/-- The merged cup frame `leftContext ◁ ((L · rightContext) ▷ η)` — the shape `atomFrame` produces for a
shared-leg cup (its stored right context being `L · rightContext`). -/
def mergedCupFrame :
    RawTwoCellExpr adjunctionModeSignature
      (composePath leftContext
        (composePath (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
          (composePath (singletonModalityPath AdjunctionModality.left) rightContext)))
      (composePath leftContext
        (composePath adjunctionLeftThenRight
          (composePath (singletonModalityPath AdjunctionModality.left) rightContext))) :=
  RawTwoCellExpr.whiskerLeft leftContext
    (RawTwoCellExpr.whiskerRight
      (composePath (singletonModalityPath AdjunctionModality.left) rightContext)
      adjunctionUnitTwoCell)

/-- The merged cap frame `(leftContext · L) ◁ (rightContext ▷ ε)` — the shape `atomFrame` produces for a
shared-leg cap (its stored left context being `leftContext · L`). -/
def mergedCapFrame :
    RawTwoCellExpr adjunctionModeSignature
      (composePath (composePath leftContext (singletonModalityPath AdjunctionModality.left))
        (composePath adjunctionRightThenLeft rightContext))
      (composePath (composePath leftContext (singletonModalityPath AdjunctionModality.left))
        (composePath (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip) rightContext)) :=
  RawTwoCellExpr.whiskerLeft
    (composePath leftContext (singletonModalityPath AdjunctionModality.left))
    (RawTwoCellExpr.whiskerRight rightContext adjunctionCounitTwoCell)

/-! ## The cup bridge: the merged cup frame IS the iterated cup leg, up to an associativity cast -/

/-- ★ **The cup half of THE CAST BRIDGE.**  The merged cup frame `leftContext ◁ ((L · rightContext) ▷ η)` is
`TwoCellConvFull` to the iterated cup leg `sharedLegCupLeg` up to a `composePath`-associativity boundary cast: the
merged single right-whisker splits (`cupLegSplitsToMergedCupFrameInner`, the shipped `whiskerRightComp`) into
`rightContext ▷ (L ▷ η)`, and lifting that through `leftContext ◁ -` and pulling the cast out
(`whiskerLeft_castBoundary`) lands the iterated leg. -/
theorem mergedCupFrame_convFull_castCupLeg :
    TwoCellConvFull adjunctionModeSignature (mergedCupFrame leftContext rightContext)
      (sharedLegCupLeg leftContext rightContext) := by
  have lifted := TwoCellConvFull.whiskerLeftCongr leftContext
    (cupLegSplitsToMergedCupFrameInner rightContext)
  rw [RawTwoCellExpr.whiskerLeft_castBoundary] at lifted
  exact lifted

/-! ## The cap bridge: the merged cap frame IS the iterated cap leg, up to associativity casts -/

/-- ★ **The cap half of THE CAST BRIDGE.**  The merged cap frame `(leftContext · L) ◁ (rightContext ▷ ε)` is
`TwoCellConvFull` to the iterated cap leg `sharedLegCapLeg` up to `composePath`-associativity boundary casts: the
merged composite left-whisker `leftContext · L` splits (`whiskerLeftComp`) into `leftContext ◁ (L ◁ (rightContext ▷
ε))`, and the inner `L ◁ (rightContext ▷ ε)` exchanges (`capLegSplitsToMergedCapFrameInner`, the shipped
`whiskerExchange`) into `rightContext ▷ (L ◁ ε)`; the two casts fuse. -/
theorem mergedCapFrame_convFull_castCapLeg :
    TwoCellConvFull adjunctionModeSignature (mergedCapFrame leftContext rightContext)
      (RawTwoCellExpr.castBoundary
        ((congrArg (composePath leftContext)
            (composePath_assoc (singletonModalityPath AdjunctionModality.left)
              adjunctionRightThenLeft rightContext)).trans
          (composePath_assoc leftContext (singletonModalityPath AdjunctionModality.left)
            (composePath adjunctionRightThenLeft rightContext)).symm)
        ((congrArg (composePath leftContext)
            (composePath_assoc (singletonModalityPath AdjunctionModality.left)
              (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip) rightContext)).trans
          (composePath_assoc leftContext (singletonModalityPath AdjunctionModality.left)
            (composePath (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip) rightContext)).symm)
        (sharedLegCapLeg leftContext rightContext)) := by
  have innerConv := TwoCellConvFull.whiskerLeftCongr leftContext
    (capLegSplitsToMergedCapFrameInner rightContext)
  rw [RawTwoCellExpr.whiskerLeft_castBoundary] at innerConv
  have splitOuter := TwoCellConvFull.whiskerLeftComp leftContext
    (singletonModalityPath AdjunctionModality.left)
    (RawTwoCellExpr.whiskerRight rightContext adjunctionCounitTwoCell)
  have combined := splitOuter.trans
    (TwoCellConvFull.castBoundaryCongr
      (composePath_assoc leftContext (singletonModalityPath AdjunctionModality.left)
        (composePath adjunctionRightThenLeft rightContext)).symm
      (composePath_assoc leftContext (singletonModalityPath AdjunctionModality.left)
        (composePath (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip) rightContext)).symm
      innerConv)
  rw [RawTwoCellExpr.castBoundary_castBoundary] at combined
  exact combined

/-! ## THE CAST BRIDGE — the merged shared-leg frames collapse to the identity -/

/-- The alignment cast: the merged cap frame's SOURCE `(leftContext · L) · (R·L) · rightContext` equals the merged
cup frame's TARGET `leftContext · (L·R) · (L · rightContext)` — the SAME word `leftContext L R L rightContext`, up
to `composePath`-associativity (the `leftContext · L` prefix re-brackets).  This is the RV/FM `vcompAssoc`
re-bracketing: a strict, on-the-nose associativity coherence, threaded explicitly. -/
theorem mergedFramesAlign :
    composePath (composePath leftContext (singletonModalityPath AdjunctionModality.left))
        (composePath adjunctionRightThenLeft rightContext)
      = composePath leftContext
        (composePath adjunctionLeftThenRight
          (composePath (singletonModalityPath AdjunctionModality.left) rightContext)) :=
  composePath_assoc leftContext (singletonModalityPath AdjunctionModality.left)
    (composePath adjunctionRightThenLeft rightContext)

/-- The endpoint cast: the merged cap frame's TARGET `(leftContext · L) · rightContext` equals the shared boundary
`leftContext · L · rightContext` (the merged cup frame's source) — again `composePath`-associativity of the
`leftContext · L` prefix. -/
theorem mergedFramesEndpoint :
    composePath (composePath leftContext (singletonModalityPath AdjunctionModality.left))
        (composePath (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.tip) rightContext)
      = composePath leftContext
        (composePath (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
          (composePath (singletonModalityPath AdjunctionModality.left) rightContext)) :=
  composePath_assoc leftContext (singletonModalityPath AdjunctionModality.left) rightContext

/-- ★★ **THE CAST BRIDGE (handedness A).**  The merged cup and cap frames — the shape the readback's `atomFrame`
produces for a shared-leg partner — collapse to the identity on the shared boundary `leftContext · L ·
rightContext`: `mergedCupFrame ⊟ castBoundary(align) mergedCapFrame ≈ id`.  The merged `vcomp` typechecks only
through the `composePath`-associativity boundary cast `mergedFramesAlign` (the cup's target and cap's source are the
same word, differently bracketed — the honest cast the design predicts).  The proof lifts each merged frame to its
iterated leg (`mergedCupFrame_convFull_castCupLeg` / `mergedCapFrame_convFull_castCapLeg`, both up to
associativity casts BETWEEN DEFINITIONALLY-EQUAL boundaries, hence cast-invisible), and the iterated composite
collapses by the shipped cast-free `generalContextFrameLegsCollapse`.  This is the strict, bounded
associativity-transport (RV Prop 3.3.4 `vcompAssoc`), consumed — not posited. -/
theorem mergedSharedLegFramesCollapse :
    SaturatedTwoCellConv
      (RawTwoCellExpr.vcomp (mergedCupFrame leftContext rightContext)
        (RawTwoCellExpr.castBoundary (mergedFramesAlign leftContext rightContext)
          (mergedFramesEndpoint leftContext rightContext) (mergedCapFrame leftContext rightContext)))
      (RawTwoCellExpr.id (signature := adjunctionModeSignature)
        (composePath leftContext
          (composePath (ModalityPath.nil (graph := adjunctionGraph) AdjunctionMode.base)
            (composePath (singletonModalityPath AdjunctionModality.left) rightContext)))) :=
  let capCastConv :
      TwoCellConvFull adjunctionModeSignature
        (RawTwoCellExpr.castBoundary (mergedFramesAlign leftContext rightContext)
          (mergedFramesEndpoint leftContext rightContext) (mergedCapFrame leftContext rightContext))
        (sharedLegCapLeg leftContext rightContext) := by
    have transported := TwoCellConvFull.castBoundaryCongr (mergedFramesAlign leftContext rightContext)
      (mergedFramesEndpoint leftContext rightContext)
      (mergedCapFrame_convFull_castCapLeg leftContext rightContext)
    rw [RawTwoCellExpr.castBoundary_castBoundary] at transported
    exact transported
  SaturatedTwoCellConv.trans
    (SaturatedTwoCellConv.vcompCongrLeft
      (RawTwoCellExpr.castBoundary (mergedFramesAlign leftContext rightContext)
        (mergedFramesEndpoint leftContext rightContext) (mergedCapFrame leftContext rightContext))
      (SaturatedTwoCellConv.ofFull (mergedCupFrame_convFull_castCupLeg leftContext rightContext)))
    (SaturatedTwoCellConv.trans
      (SaturatedTwoCellConv.vcompCongrRight (sharedLegCupLeg leftContext rightContext)
        (SaturatedTwoCellConv.ofFull capCastConv))
      (generalContextFrameLegsCollapse leftContext rightContext))

end MergedFrameCastBridge

/-! ## Honesty marker -/

/-- **★ ESTABLISHED — THE CAST BRIDGE (handedness A) is LANDED, in the merged-`atomFrame` readback form.**
`mergedSharedLegFramesCollapse` proves `mergedCupFrame ⊟ castBoundary(align) mergedCapFrame ≈ id` on the shared
boundary `leftContext · L · rightContext`, for ARBITRARY whisker words.  The two merged frames ARE the readback's
`atomFrame` shapes for a shared-leg cup / cap (`mergedCupFrame = leftContext ◁ ((L · rightContext) ▷ η)` =
`atomFrame` of a cup with stored right context `L · rightContext`; `mergedCapFrame = (leftContext · L) ◁
(rightContext ▷ ε)`).  The merged `vcomp` typechecks only through the `composePath`-associativity boundary cast
`mergedFramesAlign` — the honest cast the design predicts: the cup's target `leftContext · (L·R) · (L ·
rightContext)` and the cap's source `(leftContext · L) · (R·L) · rightContext` are the SAME word, differently
bracketed.  The bridge lifts each merged frame to its iterated leg (`mergedCupFrame_convFull_castCupLeg` cast-free
by defeq; `mergedCapFrame_convFull_castCapLeg` up to a `composePath`-assoc cast that FUSES with the alignment cast
to a defeq-invisible identity), and the iterated composite collapses by the shipped cast-free
`generalContextFrameLegsCollapse`.  This is the strict, bounded RV/FM `vcompAssoc` associativity-transport —
consumed, never posited.  Reads NO `matchingOf` / `partnerIndexOf` / arc structure: the shared-leg shape is the
seed-rigidity factorization's, not the matching's.

  What this marker does NOT close (gates stay `false`): (1) the atom-INSTANCE specialization — connecting a
  concrete `atomFrame cupAtom` / `atomFrame capAtom` variable to the merged frames needs the cup/cap generator
  pinned at the PATH level (case the seed generator; the shipped `sharedLegFactorHandednessA` pins only the
  contexts) plus the factorization substituted; (2) handedness B — the RIGHT-snake mirror, whose general-context
  collapse is un-shipped (only the raw triangle `rightSnakeDoubleWhiskerCollapses`); (3) the STRAIGHTEN producer
  proper — the delete-chain surgery `framedDeletePrefixChain` (a clone of `framedSwapPrefixChain` reconnecting via
  `cupCapDeletionReconnects`) and the readback-realization `stepConv` (`cell ≈ readback ≈ pre ⊟ tail = next` via
  `generalContextSnakeStraightensInContext`, NOT a spine-trace-equivalence since deletion changes the spine).  So
  `CellStraightenStepInput` is NOT discharged; `valleyCellDescentStepOracle` still takes it as an input, and
  `convOfMapEq` / the fib-3 gate flags stay `false`.  `= true`. -/
def fxMode_hasSpineValleyStraightenCastBridge : Bool := true

end FX1Poly.Polygraph
