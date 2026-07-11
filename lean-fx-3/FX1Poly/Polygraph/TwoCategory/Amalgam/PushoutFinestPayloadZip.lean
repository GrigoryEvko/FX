import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutVcompSeam
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFinestBoundaries

/-! # Polygraph/TwoCategory/Amalgam/PushoutFinestPayloadZip — the payload zip's aligned TARGET: the vcomp seam keyed
to the finest common refinement of the middle 1-cell, exercised on the r8 shape; the firing-block payload re-slice
stays the honest residual (WP-AMALG-2 r13, the payload-zip round)

The r9 vcomp SEAM (`pushoutFactorizeVcompSeam`, `PushoutVcompSeam.lean`) zips two half-factorizations sharing ONE
`(finalWall, pairs)` layout at their common middle 1-cell.  The r12 all-boundary round-trips
(`gapDomLayout_finestLayout` / `gapMidLayout_finestLayout` / `gapCodLayout_finestLayout`) established that
`finestLayout G` presents `G` on all three boundaries (dom = mid = cod) — so `finestLayout G`, the UNIQUE per-letter
decomposition keyed to `pushoutPathWord` (the conserved invariant), is a LEGAL shared layout for BOTH halves of a
`vcomp` whose middle is `G`.  This file ships the seam INSTANTIATED at that finest common refinement — the aligned
target of the payload zip.

## What ships — the seam at the finest common refinement

  * **`pushoutFactorizeVcompSeamFinest`** — the seam specialized to `finalWall = nil`, `pairs = finestLayout G`: two
    cells factoring through `finestLayout G`'s slots vertically-compose to `gapVcompLayout nil (finestLayout G)`.  The
    finest layout is the per-letter (maximal) refinement of the word of `G`, hence the common refinement any two
    layouts of `G` share their SKELETON with (self-attack 5b below).
  * **`finestLayoutPresentsAllBoundaries`** — the three round-trips packaged: `finestLayout G` presents `G` as dom =
    mid = cod, the legality certificate the seam consumes on both halves.
  * **`finestLayoutAlignsR8Shape`** — the r8 counterexample MIDDLE 1-cell `s·t·s`'s finest layout presents it on all
    three boundaries: the r8 shape's SKELETON aligns to the finest keys (the recon's self-attack 5b), isolating the
    `eta`/`delta` FIRINGS (the payloads that widen the gaps) as the sole non-free content.
  * **`pushoutFactorizeVcompSeamFinestReflProbe`** — the seam-at-finest fires end-to-end on `finestLayout t` (the
    reflexive factorizations), a genuine reduction through the r7 crux `vcompGapInterchangeSplice`.

## The honest WALL: the firing-block payload re-slice (NOT this round)

`finestLayout` is the correct common refinement of the 1-cell SKELETON, but NOT of the PAYLOADS: its
`finestLetterPair` sets `upper := id`, `lower := id` (identity payloads), so `gapUpperLayout nil (finestLayout G)` is
(up to free absorption) the IDENTITY on `G`.  A real firing — e.g. `mu : t·t ⇒ t` sitting in a gap spanning two
letters — is ATOMIC and cannot be re-sliced into per-letter identity slots without destroying it.  So the genuine
payload zip (produce `cellUpper ≈ gapUpperLayout nil (finestLayout G)` from an arbitrary `cellUpper ≈ gapUpperLayout
fw pairs`) needs a FIRING-BLOCK decomposition (one gap-slot per maximal firing region, walls at per-letter positions)
whose wall skeleton is the wall-count invariant but whose gaps carry atomic firings — and a cell-level re-slice
consuming `finestGapWidthsAux_append` (the `ln` width merge, shipped r10) at the CELL level to fuse adjacent firing
regions across a `composePath` junction cast.  That is the named residual.

## What STAYS WALLED (no flip)

This ships the aligned TARGET of the payload zip (the seam at the finest common refinement) + the r8 skeleton
alignment — NOT the firing-block payload re-slice.  `fxAmalg_hasFullSaturatedPushoutDispatch`
(`DispatchSaturated.lean`) STAYS `false`; `fxAmalg_hasGeneralPushoutDispatch` (`PushoutBundle.lean`) STAYS `false`;
`fxAmalg_topFactorizationInductionStaysWalled` (`PushoutVcompInterchangeSplice.lean`) STAYS `true`.  #2043 does NOT
close.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The seam at the finest common refinement — the aligned target of the payload zip -/

/-- ★★★ **THE VCOMP SEAM AT THE FINEST COMMON REFINEMENT.**  The r9 seam `pushoutFactorizeVcompSeam` specialized to
`finalWall = nil`, `pairs = finestLayout middleOneCell` — the per-letter (maximal) refinement of the middle 1-cell's
word.  Two cells factoring through `finestLayout middleOneCell`'s slots (the upper through `gapDomLayout ⇒
gapMidLayout`, the lower through `gapMidLayout ⇒ gapCodLayout`) vertically-compose to `gapVcompLayout nil (finestLayout
middleOneCell)`.  Legalized by the r12 all-boundary round-trips (`finestLayoutPresentsAllBoundaries`): `finestLayout
middleOneCell` presents `middleOneCell` on all three boundaries, so it is a legal shared `(finalWall, pairs)` for BOTH
halves.  This is the ALIGNED TARGET of the payload zip — the seam keyed to the common refinement, not a wall
scaffold. -/
theorem pushoutFactorizeVcompSeamFinest {baseRel : CellRel involutionMonadPushout.toModeSignature}
    (middleOneCell : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode)
    {cellUpper : RawTwoCellExpr involutionMonadPushout.toModeSignature
        (gapDomLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
          (finestLayout middleOneCell))
        (gapMidLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
          (finestLayout middleOneCell))}
    {cellLower : RawTwoCellExpr involutionMonadPushout.toModeSignature
        (gapMidLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
          (finestLayout middleOneCell))
        (gapCodLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
          (finestLayout middleOneCell))}
    (hUpper : SaturatedConvOver involutionMonadPushout.toModeSignature baseRel cellUpper
        (gapUpperLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
          (finestLayout middleOneCell)))
    (hLower : SaturatedConvOver involutionMonadPushout.toModeSignature baseRel cellLower
        (gapLowerLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
          (finestLayout middleOneCell))) :
    SaturatedConvOver involutionMonadPushout.toModeSignature baseRel
      (RawTwoCellExpr.vcomp cellUpper cellLower)
      (gapVcompLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
        (finestLayout middleOneCell)) :=
  pushoutFactorizeVcompSeam (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
    (finestLayout middleOneCell) hUpper hLower

/-- ★★ **The finest layout presents its 1-cell on ALL THREE boundaries (the legality certificate).**  Packages the
three r12 round-trips: `gapDomLayout` / `gapMidLayout` / `gapCodLayout` at `nil` of `finestLayout middleOneCell` each
reconstruct `middleOneCell`.  This is exactly the certificate the seam-at-finest consumes to legalize `finestLayout
middleOneCell` as the shared `(finalWall, pairs)` for both halves of the `vcomp`. -/
theorem finestLayoutPresentsAllBoundaries
    (middleOneCell : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode) :
    gapDomLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
          (finestLayout middleOneCell) = middleOneCell
      ∧ gapMidLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
          (finestLayout middleOneCell) = middleOneCell
      ∧ gapCodLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
          (finestLayout middleOneCell) = middleOneCell :=
  ⟨gapDomLayout_finestLayout middleOneCell, gapMidLayout_finestLayout middleOneCell,
    gapCodLayout_finestLayout middleOneCell⟩

/-! ## Self-attack 5b — the r8 shape's skeleton aligns to the finest keys -/

/-- The r8 counterexample's MIDDLE 1-cell `s·t·s` (the codomain of `unitSplitsWallCell`, the domain of the lower
half-cell).  The `s`-walls flank the `t`-gap the `eta` created. -/
def r8MiddleOneCell : ModalityPath involutionMonadPushout.toModeGraph monadPushMode monadPushMode :=
  composePath monadPushSPath (composePath monadPushTPath monadPushSPath)

/-- ★★ **SELF-ATTACK 5b — the r8 shape's SKELETON aligns to the finest keys.**  The r8 middle 1-cell `s·t·s`'s finest
layout presents it on all three boundaries (dom = mid = cod = `s·t·s`).  Because `finestLayout` keys to
`pushoutPathWord` (the dom-to-cod-conserved invariant), two layouts of the SAME word share this finest SKELETON —
exactly the alignment the payload transport must respect.  The self-attack confirms the skeleton aligns and isolates
the `eta`/`delta` FIRINGS (which widen the gaps) as the sole non-free content — the atomic-firing obstruction of the
residual. -/
theorem finestLayoutAlignsR8Shape :
    gapDomLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
          (finestLayout r8MiddleOneCell) = r8MiddleOneCell
      ∧ gapMidLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
          (finestLayout r8MiddleOneCell) = r8MiddleOneCell
      ∧ gapCodLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
          (finestLayout r8MiddleOneCell) = r8MiddleOneCell :=
  finestLayoutPresentsAllBoundaries r8MiddleOneCell

/-! ## Non-vacuity — the seam-at-finest fires end-to-end -/

/-- ★★ **The seam-at-finest FIRES end-to-end on `finestLayout t`.**  The reflexive factorizations (`cellUpper =
gapUpperLayout`, `cellLower = gapLowerLayout`) vertically-compose, through the seam at the finest layout of the
single-letter 1-cell `t`, to `gapVcompLayout nil (finestLayout t)` — a genuine reduction of the r7 crux
`vcompGapInterchangeSplice` on concrete finest slots.  The seam-at-finest is not vacuous. -/
theorem pushoutFactorizeVcompSeamFinestReflProbe :
    SaturatedConvOver involutionMonadPushout.toModeSignature crossPairRealPushoutRel
      (RawTwoCellExpr.vcomp
        (gapUpperLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
          (finestLayout monadPushTPath))
        (gapLowerLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
          (finestLayout monadPushTPath)))
      (gapVcompLayout (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode)
        (finestLayout monadPushTPath)) :=
  pushoutFactorizeVcompSeamFinest monadPushTPath
    (SaturatedConvOver.refl _) (SaturatedConvOver.refl _)

/-! ## Honesty markers -/

/-- ★★★ **Honesty marker — the payload zip's aligned TARGET (the seam at the finest common refinement) SHIPS; the
firing-block payload re-slice STAYS the residual; #2043 does NOT close (WP-AMALG-2 r13).**  `= true`.  The r9 vcomp
seam is INSTANTIATED at the finest common refinement (`pushoutFactorizeVcompSeamFinest`, `finalWall = nil`, `pairs =
finestLayout middleOneCell`), legalized by the r12 all-boundary round-trips packaged as
`finestLayoutPresentsAllBoundaries` (`finestLayout G` presents `G` as dom = mid = cod).  The r8 shape's SKELETON
aligns to the finest keys (`finestLayoutAlignsR8Shape`: `s·t·s`'s finest layout presents it on all three boundaries —
the self-attack 5b, isolating the firings as the non-free content), and the seam-at-finest FIRES end-to-end on
`finestLayout t` (`pushoutFactorizeVcompSeamFinestReflProbe`, through `vcompGapInterchangeSplice`).

The genuine payload zip does NOT ship: `finestLayout` is the common refinement of the 1-cell SKELETON but NOT of the
PAYLOADS — its `finestLetterPair` sets identity payloads (`upper := id`, `lower := id`), so `gapUpperLayout nil
(finestLayout G)` is (up to free absorption) the identity on `G`, while a real firing (`mu : t·t ⇒ t` spanning two
letters) is ATOMIC and cannot be re-sliced into per-letter identity slots without destroying it.  The correct common
refinement is a FIRING-BLOCK decomposition (one gap-slot per maximal firing region, walls at per-letter positions),
and proving two arbitrary layouts of the same cell re-slice to it — consuming `finestGapWidthsAux_append` (the `ln`
width merge, r10) at the CELL level to fuse adjacent firing regions across a `composePath` junction cast — is the
named residual (`mergeFrameIntoHead`/`Tail`, the cell-level surgery).  This is a genuine NARROWING (the aligned target
+ the skeleton alignment ship; the atomic-firing re-slice named), NOT a flip.

FLIPPED NO master: `fxAmalg_hasFullSaturatedPushoutDispatch` STAYS `false`, `fxAmalg_hasGeneralPushoutDispatch` STAYS
`false`, `fxAmalg_topFactorizationInductionStaysWalled` STAYS `true`.  #2043 does NOT close.  `= true`. -/
def fxAmalg_hasFinestSeamZipCorollary : Bool := true

end FX1Poly.Polygraph.Amalgam
