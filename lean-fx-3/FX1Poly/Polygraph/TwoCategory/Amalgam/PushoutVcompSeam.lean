import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFinestLayout

/-! # Polygraph/TwoCategory/Amalgam/PushoutVcompSeam — THE midPath SEAM: the vcomp case of the whole-cell
factorization, keyed to the shared MIDDLE 1-cell (not a wall scaffold), and the composed-r8 counterexample now
FACTORS (WP-AMALG-2 r9, B3/B4)

r8 (`PushoutWallBlockRefutationLedger.lean`) jammed the vcomp case at `vcomp (gapVcompLayout fwU pairsU)
(gapVcompLayout fwL pairsL) ~ gapVcompLayout fw pairs` — unreachable because it tried to ZIP two SEPARATE recursive
`gapVcompLayout`s keyed to a wall SCAFFOLD (refuted: the wall-block list is not a dom-to-cod invariant).  r9 BYPASSES
that jam entirely: the two half-cells of a vertical composite are factored through ONE SHARED layout `(finalWall,
pairs)` aligned via `finestLayout` of the MIDDLE 1-cell `midPath` (a function of the word, keyed to the conserved
wall COUNT), then the crux `vcompGapInterchangeSplice` fires gap-by-gap.  No two `gapVcompLayout`s are ever vcomp-ed;
no wall scaffold is needed.

## The seam, keyed to the middle 1-cell

`pushoutFactorizeVcompSeam` takes two factorizations sharing ONE `(finalWall, pairs)` — `cellUpper ≈ gapUpperLayout`
(the top half, `gapDomLayout ⇒ gapMidLayout`) and `cellLower ≈ gapLowerLayout` (the bottom half, `gapMidLayout ⇒
gapCodLayout`), both through the SAME `gapMidLayout = finestLayout midPath` — and produces `vcomp cellUpper cellLower
≈ gapVcompLayout`.  Proof: thread `hUpper` / `hLower` through `vcompCongrLeft` / `vcompCongrRight`, then fire the r7
crux `vcompGapInterchangeSplice` (`vcomp (gapUpperLayout …) (gapLowerLayout …) ≈ gapVcompLayout …`).  The alignment
is keyed to the shared `pairs` (the finest slots of `midPath`), NOT to a wall skeleton — the empty gap (`gapDom =
nil`) absorbs exactly the r8 block-split.

## The composed-r8 counterexample now FACTORS

Compose the r8 refuting cell with a face firing INSIDE its split block:
`cellUpper = unitSplitsWallCell : s·s ==> s·t·s` (the `eta` creates the middle `t`), `cellLower = whiskerLeft s
(whiskerRight s pushoutFaceDeltaOne) : s·t·s ==> s·t·t·s` (the face `t ==> t·t` fires inside the split block).  Both
factor through ONE shared pair `vcompSplitBlockPair = {wall = s, gapDom = nil, gapMid = t, gapCod = t·t, upper = eta,
lower = δ₁}` — the empty `gapDom = nil` is the s·s domain's empty gap (width `0`), `gapMid = t` the s·t·s middle
(width `1`), `gapCod = t·t` the s·t·t·s codomain.  `vcompSplitBlockFactorization` is the full
`PushoutLayoutFactorization` of `vcomp cellUpper cellLower : s·s ==> s·t·t·s`, `rfl` boundary casts, seam conv.  The
r8 counterexample composed FACTORS.

## What STAYS WALLED (no flip)

The SEAM ships as a standalone lemma taking two finest-aligned factorizations; the composed-r8 witness confirms it
end-to-end.  But the total `pushoutFactorize` (an ARBITRARY cell factors) does NOT close: it needs the per-gap
reconstruction-inversion (recognize an arbitrary pure-`t` gap as a right-coprojected monad cell — the converse of
`interpretWordFrom_map`) and the whisker-frame `t`-run MERGE (a whiskering's frame `t`-run merges with the body's
leading/trailing gap — junction cast-bookkeeping), a separate multi-round arc.  So the seam narrows the wall to the
reconstruction-inversion; it does not remove it.  `fxAmalg_hasFullSaturatedPushoutDispatch` (`DispatchSaturated.lean`)
STAYS `false`; `fxAmalg_hasGeneralPushoutDispatch` (`PushoutBundle.lean`) STAYS `false`;
`fxAmalg_topFactorizationInductionStaysWalled` STAYS `true`.  #2043 does NOT close — the seam is not
arbitrary-cell coverage.  No fabricated flip.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## THE SEAM — the vcomp case keyed to the shared middle 1-cell -/

/-- ★★★ **THE midPath SEAM — the vcomp case of the whole-cell factorization, keyed to the shared MIDDLE 1-cell.**
Given a vertical composite `vcomp cellUpper cellLower` whose two halves factor through ONE SHARED layout `(finalWall,
pairs)` — `cellUpper ≈ gapUpperLayout finalWall pairs` (top half, `gapDomLayout ⇒ gapMidLayout`) and `cellLower ≈
gapLowerLayout finalWall pairs` (bottom half, `gapMidLayout ⇒ gapCodLayout`), sharing the middle boundary
`gapMidLayout finalWall pairs` — the whole composite factors: `vcomp cellUpper cellLower ≈ gapVcompLayout finalWall
pairs`.

Proof: `hUpper` threads through the LEFT factor (`vcompCongrLeft`), `hLower` through the RIGHT factor
(`vcompCongrRight`), reducing to `vcomp (gapUpperLayout …) (gapLowerLayout …)`, which the r7 crux
`vcompGapInterchangeSplice` collapses to `gapVcompLayout …` (iterated free interchange, gap-by-gap).  This BYPASSES
the r8 jam entirely — no two separate `gapVcompLayout`s are vcomp-ed, no wall SCAFFOLD is keyed; the alignment is the
SHARED `pairs` (the finest slots of the middle 1-cell), and the empty `gapDom = nil` slot absorbs exactly the r8
wall-block split.  Over ANY signature and base relation. -/
theorem pushoutFactorizeVcompSeam {signature : ModeSignature} {baseRel : CellRel signature}
    {oneMode : signature.graph.Mode}
    (finalWall : ModalityPath signature.graph oneMode oneMode)
    (pairs : List (VcompGapPair signature oneMode))
    {cellUpper : RawTwoCellExpr signature (gapDomLayout finalWall pairs) (gapMidLayout finalWall pairs)}
    {cellLower : RawTwoCellExpr signature (gapMidLayout finalWall pairs) (gapCodLayout finalWall pairs)}
    (hUpper : SaturatedConvOver signature baseRel cellUpper (gapUpperLayout finalWall pairs))
    (hLower : SaturatedConvOver signature baseRel cellLower (gapLowerLayout finalWall pairs)) :
    SaturatedConvOver signature baseRel
      (RawTwoCellExpr.vcomp cellUpper cellLower) (gapVcompLayout finalWall pairs) :=
  SaturatedConvOver.trans
    (SaturatedConvOver.vcompCongrLeft cellLower hUpper)
    (SaturatedConvOver.trans
      (SaturatedConvOver.vcompCongrRight (gapUpperLayout finalWall pairs) hLower)
      (vcompGapInterchangeSplice finalWall pairs))

/-- ★★ **The seam, packaged as a `PushoutLayoutFactorization`.**  Given the two finest-aligned half-factorizations,
`vcomp cellUpper cellLower` has a well-formed `PushoutLayoutFactorization` on the SHARED layout `(finalWall, pairs)`:
both boundary casts are `rfl` (the vcomp's domain / codomain ARE `gapDomLayout` / `gapCodLayout`), and the
convertibility is `pushoutFactorizeVcompSeam`.  This is the vcomp case of the top induction's per-cell output —
GIVEN the two half-cells' finest factorizations. -/
def pushoutFactorizeVcompLayout {signature : ModeSignature} (baseRel : CellRel signature)
    {oneMode : signature.graph.Mode}
    (finalWall : ModalityPath signature.graph oneMode oneMode)
    (pairs : List (VcompGapPair signature oneMode))
    (cellUpper : RawTwoCellExpr signature (gapDomLayout finalWall pairs) (gapMidLayout finalWall pairs))
    (cellLower : RawTwoCellExpr signature (gapMidLayout finalWall pairs) (gapCodLayout finalWall pairs))
    (hUpper : SaturatedConvOver signature baseRel cellUpper (gapUpperLayout finalWall pairs))
    (hLower : SaturatedConvOver signature baseRel cellLower (gapLowerLayout finalWall pairs)) :
    PushoutLayoutFactorization baseRel (RawTwoCellExpr.vcomp cellUpper cellLower) where
  finalWall := finalWall
  pairs := pairs
  domEq := rfl
  codEq := rfl
  conv := pushoutFactorizeVcompSeam finalWall pairs hUpper hLower

/-! ## The composed-r8 counterexample — the shared pair and the two half-cells -/

/-- The **shared wall/gap block** of the composed-r8 factorization — one pair keyed to the middle 1-cell `s·t·s`: a
leading `s`-wall, an EMPTY `gapDom = nil` (the s·s domain's width-`0` gap), a `gapMid = t` (the s·t·s middle), a
`gapCod = t·t` (the s·t·t·s codomain), the unit `eta` (`nil ==> t`) as `upper`, the face `δ₁` (`t ==> t·t`) as
`lower`.  The empty `gapDom` is precisely the empty-gap admission: the slot exists at width `0` in the domain and
widens as the firings advance. -/
def vcompSplitBlockPair : VcompGapPair involutionMonadPushout.toModeSignature monadPushMode where
  wall := monadPushSPath
  gapDom := ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode
  gapMid := monadPushTPath
  gapCod := composePath monadPushTPath monadPushTPath
  upper := pushoutEta
  lower := pushoutFaceDeltaOne

/-- The **lower half-cell** of the composed-r8 counterexample — the monad face `δ₁` (`t ==> t·t`) whiskered by an
`s` on each side: `whiskerLeft s (whiskerRight s δ₁) : s·t·s ==> s·t·t·s`.  It fires INSIDE the block the r8 `eta`
split (duplicating the middle `t`); its domain `s·t·s` is exactly `unitSplitsWallCell`'s codomain, so the two vcomp.
-/
def unitThenFaceLowerCell :
    RawTwoCellExpr involutionMonadPushout.toModeSignature
      (composePath monadPushSPath (composePath monadPushTPath monadPushSPath))
      (composePath monadPushSPath (composePath (composePath monadPushTPath monadPushTPath) monadPushSPath)) :=
  RawTwoCellExpr.whiskerLeft (signature := involutionMonadPushout.toModeSignature) monadPushSPath
    (RawTwoCellExpr.whiskerRight (signature := involutionMonadPushout.toModeSignature)
      monadPushSPath pushoutFaceDeltaOne)

/-- The **upper half-factorization** — `unitSplitsWallCell : s·s ==> s·t·s` factors through the shared block's UPPER
payload: `unitSplitsWallCell ≈ gapUpperLayout s [vcompSplitBlockPair] = hcomp (id s) (hcomp eta (id s))`.  The free
chain (`whiskerLeft_conv_hcompIdLeading` then `hcompCongrRight` of `whiskerRight_conv_hcompIdTrailing`) — the same
sub-chain as `unitSplitsWallFactorization`, stopping at the bare `eta` (not `vcomp eta id_t`). -/
theorem vcompSplitBlockUpperConv :
    SaturatedConvOver involutionMonadPushout.toModeSignature crossPairRealPushoutRel
      unitSplitsWallCell
      (RawTwoCellExpr.hcomp (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushSPath)
        (RawTwoCellExpr.hcomp pushoutEta
          (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushSPath))) :=
  SaturatedConvOver.trans
    (whiskerLeft_conv_hcompIdLeading monadPushSPath
      (RawTwoCellExpr.whiskerRight (signature := involutionMonadPushout.toModeSignature)
        monadPushSPath pushoutEta))
    (SaturatedConvOver.hcompCongrRight
      (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushSPath)
      (whiskerRight_conv_hcompIdTrailing monadPushSPath pushoutEta))

/-- The **lower half-factorization** — `unitThenFaceLowerCell : s·t·s ==> s·t·t·s` factors through the shared
block's LOWER payload: `unitThenFaceLowerCell ≈ gapLowerLayout s [vcompSplitBlockPair] = hcomp (id s) (hcomp δ₁ (id
s))`.  Identical free chain with `δ₁` in place of `eta`. -/
theorem vcompSplitBlockLowerConv :
    SaturatedConvOver involutionMonadPushout.toModeSignature crossPairRealPushoutRel
      unitThenFaceLowerCell
      (RawTwoCellExpr.hcomp (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushSPath)
        (RawTwoCellExpr.hcomp pushoutFaceDeltaOne
          (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushSPath))) :=
  SaturatedConvOver.trans
    (whiskerLeft_conv_hcompIdLeading monadPushSPath
      (RawTwoCellExpr.whiskerRight (signature := involutionMonadPushout.toModeSignature)
        monadPushSPath pushoutFaceDeltaOne))
    (SaturatedConvOver.hcompCongrRight
      (RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushSPath)
      (whiskerRight_conv_hcompIdTrailing monadPushSPath pushoutFaceDeltaOne))

/-- ★★★ **THE COMPOSED-r8 COUNTEREXAMPLE FACTORS.**  The r8 refuting cell composed with a face firing inside its
split block — `vcomp unitSplitsWallCell unitThenFaceLowerCell : s·s ==> s·t·t·s` — has a well-formed
`PushoutLayoutFactorization` on the SINGLE shared block `[vcompSplitBlockPair]`.  Both half-cells factor through the
SAME `(finalWall = s, pairs = [vcompSplitBlockPair])` (the finest slots of the middle 1-cell `s·t·s`), the empty
`gapDom = nil` absorbing the r8 wall-block split, and the seam `pushoutFactorizeVcompSeam` assembles them.  This is
the r8 jam, BYPASSED end-to-end at the real pushout signature: what r8 could not zip through a wall scaffold, r9
factors through the shared middle 1-cell.  `rfl` boundary casts. -/
def vcompSplitBlockFactorization :
    PushoutLayoutFactorization crossPairRealPushoutRel
      (RawTwoCellExpr.vcomp unitSplitsWallCell unitThenFaceLowerCell) :=
  pushoutFactorizeVcompLayout crossPairRealPushoutRel monadPushSPath [vcompSplitBlockPair]
    unitSplitsWallCell unitThenFaceLowerCell
    vcompSplitBlockUpperConv vcompSplitBlockLowerConv

/-! ## Honesty markers -/

/-- ★★★ **Honesty marker — THE midPath SEAM SHIPS, re-keyed off the refuted wall scaffold (WP-AMALG-2 r9, B3).**
`= true`: `pushoutFactorizeVcompSeam` discharges the vcomp case of the whole-cell factorization — given two
finest-aligned half-factorizations sharing ONE `(finalWall, pairs)` (the finest slots of the middle 1-cell
`midPath`), `vcomp cellUpper cellLower ≈ gapVcompLayout finalWall pairs` — by threading `hUpper` / `hLower` through
`vcompCongrLeft` / `vcompCongrRight` and firing the r7 crux `vcompGapInterchangeSplice`.  This BYPASSES the r8 jam
(`vcomp (gapVcompLayout fwU pairsU) (gapVcompLayout fwL pairsL) ~ gapVcompLayout fw pairs`): no two separate
`gapVcompLayout`s are ever vcomp-ed and no wall SCAFFOLD is keyed — the alignment is the shared `pairs`, and the
empty `gapDom = nil` slot absorbs the r8 wall-block split.  Non-vacuous end-to-end at the REAL pushout signature
(`vcompSplitBlockFactorization`: the r8 counterexample composed with a face firing inside its split block FACTORS,
`s·s ==> s·t·t·s`).  This re-keys the residual off the refuted wall-block skeleton onto the wall-count-invariant
finest decomposition.  `= true`. -/
def fxAmalg_hasMidPathVcompSeam : Bool := true

/-- ★★ **Honesty marker — the SEAM is not arbitrary-cell coverage; the reconstruction-inversion + whisker-frame
merge STAY walled; #2043 does NOT close (WP-AMALG-2 r9, B4).**  `= true` (the wall honestly held).  The seam
(`pushoutFactorizeVcompSeam`) discharges the vcomp case GIVEN two finest-aligned half-factorizations, and the
composed-r8 witness (`vcompSplitBlockFactorization`) confirms it end-to-end.  But the TOTAL `pushoutFactorize` (an
ARBITRARY pushout cell factors into a `VcompGapPair` layout) does NOT close: it still needs (1) the per-gap
RECONSTRUCTION-INVERSION — recognize an arbitrary pure-`t` gap as `mapCellAlong inclRight (monadCell)`, the converse
of `interpretWordFrom_map`, which the per-gap decider needs; (2) the WHISKER-FRAME `t`-run MERGE — a whiskering's
frame `t`-run merges with the body's leading / trailing gap, `hcomp (id oneCell_t-run) (body_leading_gap_cell)`,
junction cast-bookkeeping.  These are a separate multi-round arc (the recon's named residual).  So the seam NARROWS
the wall (the vcomp regrouping is a free coboundary, the alignment is re-keyed to the conserved wall count) but does
NOT remove it.  `fxAmalg_hasFullSaturatedPushoutDispatch` (`DispatchSaturated.lean`) STAYS `false` — the seam is not
the arbitrary-cell coverage its demand's residual (iii) requires; `fxAmalg_hasGeneralPushoutDispatch`
(`PushoutBundle.lean`) STAYS `false`; `fxAmalg_topFactorizationInductionStaysWalled`
(`PushoutVcompInterchangeSplice.lean`) STAYS `true`.  #2043 does NOT close.  Named node: the per-gap
reconstruction-inversion + the whisker-frame `t`-run merge of the top-level `pushoutFactorize` induction.  No
fabricated flip.  `= true`. -/
def fxAmalg_seamNotArbitraryCellCoverage : Bool := true

end FX1Poly.Polygraph.Amalgam
