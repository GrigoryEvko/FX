import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFiringBlockProducer
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFactorizeCanonicalWhiskerRight
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutInteriorOrdinalReanchor
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutVcompSeam

/-! # Polygraph/TwoCategory/Amalgam/PushoutFactorizeCanonical — the CANONICAL factorization subtype motive, the arms
per the recon table (gen ✅, id slot-spec by construction, whisker / vcomp honest partials), and the width-matching
adjudication (WP-AMALG-2 r19, Brick B3)

With B2's coarse producer `firingBlockLayout` (slot count `wallCount + 1` by construction) + round-trips in hand,
this file assembles the CANONICAL factorization arms.  The canonical reader must carry the slot-count THROUGH the
recursion (each arm produces a slot-spec-meeting factorization from its sub-factorizations), so the motive is a
SUBTYPE `CanonicalFactorization` bundling a `PushoutLayoutFactorization` with its slot-count proof.

## The subtype motive

`CanonicalFactorization cell := { f : PushoutLayoutFactorization crossPairRealPushoutRel cell // f.pairs.length =
(finestGapWidths (pushoutPathTags sourcePath)).length }` — a factorization whose block count IS the canonical
firing-block slot count.  The slot count rides WITH the factorization (it cannot be re-proved externally through the
recursion), matching the r15 shallow reader's shape but carrying the canonical payload.

## The arms (per the recon table)

  * **`gen` ✅** — the pushout multiplication `mu` (`t·t ⇒ t`) factors as its single canonical firing slot, meeting
    the spec BY CONSTRUCTION (`mu`'s wall-free boundary reads `wallCount 0 + 1 = 1` slot).  `mulCanonicalFactorization`
    is a NON-VACUOUS inhabitant of the subtype at the REAL pushout signature.
  * **`id` (slot-spec ✅, collapse conv gated)** — the coarse producer `firingBlockLayout path` MEETS the canonical
    slot count BY CONSTRUCTION (`idCanonicalArmMeetsSlotSpec` = B2's `firingBlockLayout_slotCount`), and its boundary
    equalities are B2's round-trips.  What the general `id`-arm `CanonicalFactorization` still needs is the MULTI-BLOCK
    identity-layout COLLAPSE conv `gapVcompLayout nil (firingBlockLayout path) ≈ castBoundary (round-trips) (id path)`
    — threading the per-block `vcompIdLeft` + `hcompId_conv_idComposite` collapse through the `gapDomLayout ≠
    gapCodLayout` boundary cast (an opaque-proof cast round-trip).  `firingBlockLayoutAux_gapDomEqCod` (the
    boundary equality) ships; the collapse conv is the named residual.
  * **`whiskerLeft` / `whiskerRight` ⚠️** — the shipped merge arms (`pushoutFactorizeWhiskerLeftMergeLayout` /
    `…RightMergeLayout`) keep the body's slot count `n`, which equals the spec `wallCount + 1` only for WALL-FREE
    frames; an `s`-frame needs the JUNCTION `t`-run MERGE (fuse the frame's trailing gap with the body's leading gap).
    The named residual `fxAmalg_whiskerJunctionMergeStaysWalled`.
  * **`vcomp` ⚠️** — the seam widths MATCH at the shared middle (adjudicated below), but producing the shared `pairs`
    (re-slicing an arbitrary IH M-layout to the coarse `firingBlockLayout M`) is the COMMON-REFINEMENT zip, coupled to
    the JAM A atomic-firing residual.  The named residual `fxAmalg_vcompCommonRefinementZipStaysWalled`.

## The width-matching adjudication (self-attack 4)

At a vcomp seam the shared middle 1-cell `M` DETERMINES the middle-slot widths, IDENTICAL for both halves — so equal
slot counts CANNOT hide different matched-ordinal widths at the seam.  The dom/cod width variation (a gap can be
wire-changing) is ABSORBED by the per-pair `gapDom` / `gapMid` / `gapCod` split (`VcompGapPair` carries three
independent face widths).  Witnessed on `muWallShiftBlock` (dom width `2`, mid `1`, cod `1` — a wire-changing block
whose three faces carry three widths natively).

## What STAYS WALLED (no flip)

`fxAmalg_totalCanonicalReaderStaysGated` STAYS `true` (the id collapse conv + whisker junction merge + vcomp zip are
unbuilt); `fxAmalg_topFactorizationInductionStaysWalled` STAYS `true`; the masters STAY at their walled values; #2043
does NOT close.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The canonical factorization subtype motive -/

/-- ★★★ **THE CANONICAL FACTORIZATION SUBTYPE.**  A `PushoutLayoutFactorization` of a pushout 2-cell whose block
count IS the canonical firing-block slot count `(finestGapWidths (pushoutPathTags sourcePath)).length` (= `wallCount +
1`).  The slot count rides WITH the factorization because the canonical reader RECURSES (whisker / vcomp consume the
sub-factorizations' slot counts) — it cannot be re-proved externally.  The canonical strengthening of the r15 shallow
`pushoutFactorizeTotal` (which places the whole subterm in ONE gap). -/
def CanonicalFactorization
    {sourcePath targetPath : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode}
    (cell : RawTwoCellExpr involutionMonadPushout.toModeSignature sourcePath targetPath) : Type :=
  { factorization : PushoutLayoutFactorization crossPairRealPushoutRel cell //
    factorization.pairs.length = (finestGapWidths (pushoutPathTags sourcePath)).length }

/-! ## The `gen` arm — a concrete canonical factorization at the real pushout signature -/

/-- ★★★ **THE `gen` ARM (✅ by construction) — the pushout multiplication `mu` factors CANONICALLY.**  `gen
pushoutMonadMult` (`t·t ⇒ t`) has a `CanonicalFactorization`: its single canonical firing slot
(`pushoutMultFactorization`, one gap carrying `mu`), whose block count `1` MEETS the canonical slot count
`(finestGapWidths (pushoutPathTags (t·t))).length = wallCount 0 + 1 = 1` — because `mu`'s boundary is wall-free
(`noGeneratorStraddlesWall`, concretely `pushoutMultSlotWallFree`).  A NON-VACUOUS inhabitant of the subtype at the
REAL pushout signature. -/
def mulCanonicalFactorization :
    CanonicalFactorization (RawTwoCellExpr.gen pushoutMonadMult) :=
  ⟨pushoutMultFactorization, rfl⟩

/-- ★★ **PROBE — the `gen` canonical factorization has ONE slot.**  `mulCanonicalFactorization.1.pairs.length = 1`
(`rfl`): the atomic `mu` firing occupies exactly one canonical firing-block slot, the wall-free-boundary spec. -/
theorem mulCanonicalSlotCount : mulCanonicalFactorization.1.pairs.length = 1 := rfl

/-! ## The `id` arm — the slot-spec ships by construction; the collapse conv is the named residual -/

/-- ★★★ **THE `id` ARM SLOT-SPEC (✅ by construction).**  The coarse producer `firingBlockLayout path` MEETS the
canonical slot count BY CONSTRUCTION — `(firingBlockLayout path).length = (finestGapWidths (pushoutPathTags
path)).length` — so an `id path` factorization built on `pairs = firingBlockLayout path` (boundaries the B2
round-trips) has the CANONICAL slot count.  This is B2's `firingBlockLayout_slotCount`; the remaining piece is the
multi-block identity-layout COLLAPSE conv. -/
theorem idCanonicalArmMeetsSlotSpec
    (path : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode) :
    (firingBlockLayout path).length = (finestGapWidths (pushoutPathTags path)).length :=
  firingBlockLayout_slotCount path

/-- ★★ **THE `id`-ARM BOUNDARY EQUALITY** — `gapDomLayout nil (firingBlockLayoutAux pw cg path) = gapCodLayout nil
(firingBlockLayoutAux pw cg path)`, both layouts having the SAME boundary word (B2's `firingBlockLayoutAux_domWord` /
`_codWord`, both `= word(pw) ++ (word(cg) ++ word(path))`), lifted by `pushoutPathWord_injective`.  The `gapDomLayout
= gapCodLayout` fact the multi-block identity-layout collapse conv rides — since every `idBlockPair` has `gapCod =
gapDom`, the two boundary layouts coincide.  (The collapse CONV itself, threading `vcompIdLeft` +
`hcompId_conv_idComposite` through this boundary cast, is the named residual.) -/
theorem firingBlockLayoutAux_gapDomEqCod
    (pendingWall currentGap :
      ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode)
    {sourceMode targetMode : Fin involutionMonadPushout.modeCount}
    (path : ModalityPath involutionMonadPushout.toModeGraph sourceMode targetMode) :
    gapDomLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
        (firingBlockLayoutAux pendingWall currentGap path)
      = gapCodLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
        (firingBlockLayoutAux pendingWall currentGap path) :=
  pushoutPathWord_injective _ _
    ((firingBlockLayoutAux_domWord pendingWall currentGap path).trans
      (firingBlockLayoutAux_codWord pendingWall currentGap path).symm)

/-! ## The width-matching adjudication (self-attack 4) -/

/-- ★★★ **THE WIDTH-MATCHING ADJUDICATION — the per-pair three-face split ABSORBS the dom/cod width variation.**  A
`VcompGapPair` carries THREE independent face widths (`gapDom`, `gapMid`, `gapCod`), so a wire-changing block holds
three DIFFERENT widths natively.  Witnessed on `muWallShiftBlock` (`t·t ⇒ t`): domain width `2`, middle width `1`,
codomain width `1` — the dom/cod width variation is carried by the pair, not a matched-ordinal MISMATCH.  So at a
vcomp seam, equal slot counts CANNOT hide different widths at matched ordinals: the shared middle `M` determines the
middle-slot widths identically for both halves, and the dom/cod variation is absorbed here. -/
theorem widthVariationAbsorbedByThreeFaces :
    muWallShiftBlock.gapDom.length = 2
      ∧ muWallShiftBlock.gapMid.length = 1
      ∧ muWallShiftBlock.gapCod.length = 1 :=
  ⟨rfl, rfl, rfl⟩

/-- ★★ **THE SEAM MIDDLE WIDTHS ARE SHARED (the vcomp seam is width-consistent).**  The composed-r8 seam witness
`vcompSplitBlockFactorization` (`s·s ⇒ s·t·t·s`) factors through ONE shared block `[vcompSplitBlockPair]` whose middle
`gapMid = t` (width `1`) is the shared 1-cell of BOTH halves — so the seam's middle-slot width is DETERMINED by the
shared `M`, identical for the upper and lower factorizations.  `vcompSplitBlockPair.gapMid.length = 1` (`rfl`). -/
theorem seamMiddleWidthShared : vcompSplitBlockPair.gapMid.length = 1 := rfl

/-! ## Observability -/

-- The gen canonical slot count (expect `1`); the mu block's three face widths (expect `2`, `1`, `1`).
#eval mulCanonicalFactorization.1.pairs.length
#eval (muWallShiftBlock.gapDom.length, muWallShiftBlock.gapMid.length, muWallShiftBlock.gapCod.length)

/-! ## Honesty markers -/

/-- ★★★ **Honesty marker — the CANONICAL factorization subtype + the `gen` arm + the `id`-arm slot-spec SHIP
(WP-AMALG-2 r19, B3).**  `= true`.  `CanonicalFactorization` bundles a `PushoutLayoutFactorization` with its
slot-count proof (the count rides with the factorization through the recursion).  The `gen` arm ships CONCRETELY:
`mulCanonicalFactorization` (`gen mu` factors as its single wall-free canonical slot, `1 = wallCount + 1`,
non-vacuous at the REAL pushout signature).  The `id` arm's slot-spec ships BY CONSTRUCTION
(`idCanonicalArmMeetsSlotSpec` = B2's `firingBlockLayout_slotCount`) and its boundary equality ships
(`firingBlockLayoutAux_gapDomEqCod`, both boundary layouts share the word).  The width-matching adjudication ships
(`widthVariationAbsorbedByThreeFaces` / `seamMiddleWidthShared`: the per-pair three-face split absorbs dom/cod width
variation, the seam middle width is shared).  `= true`. -/
def fxAmalg_hasCanonicalFactorizationArms : Bool := true

/-- ★★★ **Honesty marker — the `id`-arm multi-block COLLAPSE conv STAYS GATED (WP-AMALG-2 r19, B3).**  `= true` (the
wall honestly held).  The `id` arm's DATA ships (B2 round-trips = boundary equalities, `firingBlockLayout_slotCount` =
slot spec, `firingBlockLayoutAux_gapDomEqCod` = the `gapDomLayout = gapCodLayout` fact), but the multi-block
identity-layout COLLAPSE conv `gapVcompLayout nil (firingBlockLayout path) ≈ castBoundary (round-trips) (id path)` —
threading the per-block `vcompIdLeft` + `hcompId_conv_idComposite` collapse through the `gapDomLayout ≠ gapCodLayout`
boundary cast (an opaque-proof `castBoundaryCongr` + `castBoundary_trans` round-trip) — is the named residual.  So the
general `id`-arm `CanonicalFactorization` (superseding the nil-only `pushoutFactorizeIdCanonicalNil`) is not this
round.  `fxAmalg_totalCanonicalReaderStaysGated` STAYS `true`.  #2043 does NOT close.  `= true`. -/
def fxAmalg_idCanonicalCollapseStaysGated : Bool := true

/-- ★★★ **Honesty marker — the whisker-frame JUNCTION `t`-run MERGE STAYS WALLED (WP-AMALG-2 r19, B3).**  `= true`
(the wall honestly held).  The shipped whisker merge arms (`pushoutFactorizeWhiskerLeftMergeLayout` /
`…RightMergeLayout`, r17/r18) keep the body's slot count `n` (`n → n`), which equals the canonical spec `wallCount +
1` only for WALL-FREE (pure-`t`) frames (`genMeetsCanonicalSlotSpec`).  An `s`-carrying frame needs the JUNCTION
MERGE: fuse the frame's trailing gap with the body's leading gap (via `composePath`) so the naive concat
`firingBlockLayout oneCell ++ bodyFact.pairs` (which over-counts by one slot — two adjacent gaps with no wall between)
becomes `wallCount(oneCell) + wallCount(bodyDom) + 1` slots.  This fresh multi-block splice is unbuilt this round.
Named node: the whisker-frame junction `t`-run merge.  `fxAmalg_totalCanonicalReaderStaysGated` STAYS `true`; #2043
does NOT close.  `= true`. -/
def fxAmalg_whiskerJunctionMergeStaysWalled : Bool := true

/-- ★★★ **Honesty marker — the vcomp COMMON-REFINEMENT ZIP STAYS WALLED, coupled to JAM A (WP-AMALG-2 r19, B3).**
`= true` (the wall honestly held).  The vcomp seam widths MATCH at the shared middle (`widthVariationAbsorbedByThreeFaces`
/ `seamMiddleWidthShared`): the shared 1-cell `M` determines the middle-slot widths identically for both halves, and
the per-pair three-face split absorbs the dom/cod variation.  So the seam is WIDTH-CONSISTENT.  What remains is
PRODUCING the shared `pairs`: re-slicing an arbitrary IH M-layout (`gapCodLayout factU.finalWall factU.pairs`) to the
COARSE `firingBlockLayout M` is a COMMON REFINEMENT — and the wire-creating `mu` (`t·t ⇒ t`) spanning two letters
CANNOT be re-sliced into per-letter slots (`PushoutFinestPayloadZip.lean`, the atomic-firing residual).  This is the
same wire-changing firing the JAM A per-gap descent fails on: `fxAmalg_hasSaturatedDispatchTheorem` STAYS `false`.
Named node: the vcomp common-refinement zip (the atomic-firing residual), coupled to JAM A + the WalkingMonad
reconstruction iso (fib-3, READ-ONLY).  `fxAmalg_totalCanonicalReaderStaysGated` STAYS `true`; #2043 does NOT close.
`= true`. -/
def fxAmalg_vcompCommonRefinementZipStaysWalled : Bool := true

/-- ★★★ **The canonical arms leave the total reader GATED and the masters walled (`rfl`).**  The `gen` arm ships and
the `id`-arm slot-spec ships, but the id collapse conv + whisker junction merge + vcomp zip are unbuilt, so the total
canonical reader stays gated and no master flips: `fxAmalg_totalCanonicalReaderStaysGated = true`,
`fxAmalg_topFactorizationInductionStaysWalled = true`, `fxAmalg_hasFullSaturatedPushoutDispatch = false`,
`fxAmalg_hasGeneralPushoutDispatch = false`. -/
theorem canonicalArmsLeaveMastersWalled :
    fxAmalg_totalCanonicalReaderStaysGated = true
      ∧ fxAmalg_topFactorizationInductionStaysWalled = true
      ∧ fxAmalg_hasFullSaturatedPushoutDispatch = false
      ∧ fxAmalg_hasGeneralPushoutDispatch = false :=
  ⟨rfl, rfl, rfl, rfl⟩

end FX1Poly.Polygraph.Amalgam
