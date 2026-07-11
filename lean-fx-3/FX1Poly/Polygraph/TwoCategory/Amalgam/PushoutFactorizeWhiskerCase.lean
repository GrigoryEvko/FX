import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFactorizeGenCase

/-! # Polygraph/TwoCategory/Amalgam/PushoutFactorizeWhiskerCase — the `whisker` cases of the top factorization: the
frame becomes a wall around the body's slot (WP-AMALG-2 r15, Brick B2)

`PushoutFactorizeGenCase.lean` (B1) shipped the `gen` case — a bare firing in a single wall-free slot.  This file
ships the `whisker` cases at the SINGLE-GAP (gen / id body) granularity: `whiskerLeft oneCell cell` and
`whiskerRight oneCell cell` factor as a single gap whose leading (resp. trailing) WALL is the frame `oneCell`.

## The construction — the frame is an inert wall

  * **`whiskerRight oneCell cell`** factors with `finalWall = oneCell`, one `singleGapPair cell` (leading wall `id`).
    The domain layout `composePath id (composePath A oneCell) = composePath A oneCell` matches `whiskerRight`'s domain
    on the NOSE — `composePath` recurses on the first argument, so a trailing frame absorbs definitionally (`rfl`
    boundary casts).  This is the CLEAN direction.
  * **`whiskerLeft oneCell cell`** factors with `finalWall = id`, one `leftFramedGapPair` (leading wall `oneCell`).
    The domain layout `composePath oneCell (composePath A id)` differs from `whiskerLeft`'s domain `composePath
    oneCell A` by the right-unit `composePath_identityPath_right` (threaded through `congrArg (composePath oneCell)`);
    the convertibility pushes the frame past the boundary cast (`whiskerLeftCastBoundaryEq`) and reduces the inner
    `id`-whisker gadget through the whisker unitor + `vcompIdRight` (`framedGapInnerConv`).

Both put the frame `oneCell` as an INERT wall (it carries `id`); the atomic body sits undivided in the single gap.
This is `mergeFrameIntoHead/Tail` at the BASE (single-gap / gen-body) granularity — the frame is recognized as a
wall, not folded into a firing.

## What STAYS WALLED (no flip)

This ships the `whisker` cases for a SINGLE-GAP body (the induction's `gen` / `id` leaves).  The general
head-prepend — `whiskerLeft oneCell body` for an ARBITRARY body factorization, merging the frame into the head slot
of a multi-gap layout across the `whiskerLeftComp` / `whiskerExchange` associativity casts — remains the named
residual (leg (b), `mergeFrameIntoHead/Tail` on a multi-gap layout).  The `s`-bearing frame's downstream wall-shift
(the wire-changing case) is beyond even that.  `fxAmalg_topFactorizationInductionStaysWalled` STAYS `true`; the
masters STAY at their walled values; #2043 does NOT close.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## Cast helpers (local, propext-free `cases; rfl`) -/

/-- **Left-whiskering pushes past a boundary cast** — a local `cases; rfl` copy (avoids the heavy `MonadReseat`
import).  `whiskerLeft oneCell (castBoundary hG hH body) = castBoundary (congrArg (composePath oneCell) hG) …
(whiskerLeft oneCell body)`. -/
theorem whiskerLeftCastBoundaryEq {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    (oneCell : ModalityPath signature.graph sourceMode middleMode)
    {oneCellG oneCellG' oneCellH oneCellH' : ModalityPath signature.graph middleMode targetMode}
    (hG : oneCellG = oneCellG') (hH : oneCellH = oneCellH')
    (body : RawTwoCellExpr signature oneCellG oneCellH) :
    RawTwoCellExpr.whiskerLeft oneCell (RawTwoCellExpr.castBoundary hG hH body)
      = RawTwoCellExpr.castBoundary (congrArg (composePath oneCell) hG) (congrArg (composePath oneCell) hH)
          (RawTwoCellExpr.whiskerLeft oneCell body) := by
  cases hG; cases hH; rfl

/-- **The inner `id`-whisker gadget reduces to the boundary-cast cell** (the shared reduction of both `gen`- and
`whisker`-case single-gap layouts).  `hcomp (cell ⊟ id_B) (id_id) ≈ castBoundary (right-unit) cell`: the trailing
`id`-whisker becomes `whiskerRight id (cell ⊟ id_B)` (`whiskerRight_conv_hcompIdTrailing`), the unitor
`whiskerRightUnit` sends it to the boundary-cast of `cell ⊟ id_B`, and `vcompIdRight` drops the `id_B` payload under
the cast (`castBoundaryCongr`). -/
theorem framedGapInnerConv {signature : ModeSignature} {baseRel : CellRel signature}
    {oneMode : signature.graph.Mode}
    {sourcePath targetPath : ModalityPath signature.graph oneMode oneMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    SaturatedConvOver signature baseRel
      (RawTwoCellExpr.hcomp (RawTwoCellExpr.vcomp cell (RawTwoCellExpr.id targetPath))
        (RawTwoCellExpr.id (ModalityPath.nil oneMode)))
      (RawTwoCellExpr.castBoundary (composePath_identityPath_right sourcePath).symm
        (composePath_identityPath_right targetPath).symm cell) :=
  SaturatedConvOver.trans
    (SaturatedConvOver.symm
      (whiskerRight_conv_hcompIdTrailing (ModalityPath.nil oneMode)
        (RawTwoCellExpr.vcomp cell (RawTwoCellExpr.id targetPath))))
    (SaturatedConvOver.trans
      (SaturatedConvOver.ofFull
        (TwoCellConvFull.whiskerRightUnit (RawTwoCellExpr.vcomp cell (RawTwoCellExpr.id targetPath))))
      (SaturatedConvOver.castBoundaryCongr
        (composePath_identityPath_right sourcePath).symm
        (composePath_identityPath_right targetPath).symm
        (SaturatedConvOver.ofConv (TwoCellConv.ofStep (TwoCellStep.vcompIdRight cell)))))

/-! ## The `whiskerRight` case — the clean direction (trailing frame absorbs, `rfl` casts) -/

/-- ★★★ **THE `whiskerRight` CASE (single-gap body).**  `whiskerRight oneCell cell` factors with `finalWall =
oneCell` and one `singleGapPair cell` (empty leading wall).  The domain layout `composePath A oneCell` matches
`whiskerRight`'s domain on the nose (`rfl` casts), and the convertibility strips the leading `id`-whisker (unitor)
and the trailing `id_oneCell`-whisker (`whiskerRight_conv_hcompIdTrailing`), dropping the `id` lower payload by
`vcompIdRight`.  The frame `oneCell` is the trailing wall; the body sits undivided in the gap. -/
def pushoutFactorizeWhiskerRightGap {signature : ModeSignature} (baseRel : CellRel signature)
    {oneMode : signature.graph.Mode}
    (oneCell : ModalityPath signature.graph oneMode oneMode)
    {sourcePath targetPath : ModalityPath signature.graph oneMode oneMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    PushoutLayoutFactorization baseRel (RawTwoCellExpr.whiskerRight oneCell cell) where
  finalWall := oneCell
  pairs := [singleGapPair cell]
  domEq := rfl
  codEq := rfl
  conv :=
    SaturatedConvOver.symm
      (SaturatedConvOver.trans
        (SaturatedConvOver.trans
          (SaturatedConvOver.symm
            (whiskerLeft_conv_hcompIdLeading (ModalityPath.nil oneMode)
              (RawTwoCellExpr.hcomp (RawTwoCellExpr.vcomp cell (RawTwoCellExpr.id targetPath))
                (RawTwoCellExpr.id oneCell))))
          (SaturatedConvOver.ofFull
            (TwoCellConvFull.whiskerLeftUnit
              (RawTwoCellExpr.hcomp (RawTwoCellExpr.vcomp cell (RawTwoCellExpr.id targetPath))
                (RawTwoCellExpr.id oneCell)))))
        (SaturatedConvOver.trans
          (SaturatedConvOver.symm
            (whiskerRight_conv_hcompIdTrailing oneCell
              (RawTwoCellExpr.vcomp cell (RawTwoCellExpr.id targetPath))))
          (SaturatedConvOver.whiskerRightCongr oneCell
            (SaturatedConvOver.ofConv (TwoCellConv.ofStep (TwoCellStep.vcompIdRight cell))))))

/-! ## The `whiskerLeft` case — leading frame, right-unit cast -/

/-- The **left-framed single-gap block** — `singleGapPair` with the frame `oneCell` as its LEADING wall. -/
def leftFramedGapPair {signature : ModeSignature} {oneMode : signature.graph.Mode}
    (oneCell : ModalityPath signature.graph oneMode oneMode)
    {sourcePath targetPath : ModalityPath signature.graph oneMode oneMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) : VcompGapPair signature oneMode where
  wall := oneCell
  gapDom := sourcePath
  gapMid := targetPath
  gapCod := targetPath
  upper := cell
  lower := RawTwoCellExpr.id targetPath

/-- ★★★ **THE `whiskerLeft` CASE (single-gap body).**  `whiskerLeft oneCell cell` factors with `finalWall = id` and
one `leftFramedGapPair oneCell cell` (leading wall `oneCell`).  The domain layout `composePath oneCell (composePath A
id)` differs from `whiskerLeft`'s domain `composePath oneCell A` by the right-unit `composePath_identityPath_right`
(under `congrArg (composePath oneCell)`); the convertibility strips the leading `id_oneCell`-whisker
(`whiskerLeft_conv_hcompIdLeading`), reduces the inner gadget (`framedGapInnerConv`), and pushes the frame past the
boundary cast (`whiskerLeftCastBoundaryEq`).  The frame `oneCell` is the leading wall; the body sits undivided. -/
def pushoutFactorizeWhiskerLeftGap {signature : ModeSignature} (baseRel : CellRel signature)
    {oneMode : signature.graph.Mode}
    (oneCell : ModalityPath signature.graph oneMode oneMode)
    {sourcePath targetPath : ModalityPath signature.graph oneMode oneMode}
    (cell : RawTwoCellExpr signature sourcePath targetPath) :
    PushoutLayoutFactorization baseRel (RawTwoCellExpr.whiskerLeft oneCell cell) where
  finalWall := ModalityPath.nil oneMode
  pairs := [leftFramedGapPair oneCell cell]
  domEq := congrArg (composePath oneCell) (composePath_identityPath_right sourcePath).symm
  codEq := congrArg (composePath oneCell) (composePath_identityPath_right targetPath).symm
  conv :=
    SaturatedConvOver.symm
      (whiskerLeftCastBoundaryEq oneCell (composePath_identityPath_right sourcePath).symm
          (composePath_identityPath_right targetPath).symm cell ▸
        SaturatedConvOver.trans
          (SaturatedConvOver.symm
            (whiskerLeft_conv_hcompIdLeading oneCell
              (RawTwoCellExpr.hcomp (RawTwoCellExpr.vcomp cell (RawTwoCellExpr.id targetPath))
                (RawTwoCellExpr.id (ModalityPath.nil oneMode)))))
          (SaturatedConvOver.whiskerLeftCongr oneCell (framedGapInnerConv cell)))

/-! ## Concrete pushout witnesses — a gen inside an `s`-frame -/

/-- ★★ **`eta` inside a left `s`-frame factors** — `whiskerLeft s eta : s ⇒ s·t` factors with the `s`-frame as its
leading wall and `eta` in the gap.  The r8-shape building block (the `s` that flanks the `eta` firing). -/
def whiskerLeftSEtaFactorization :
    PushoutLayoutFactorization crossPairRealPushoutRel
      (RawTwoCellExpr.whiskerLeft monadPushSPath pushoutEta) :=
  pushoutFactorizeWhiskerLeftGap crossPairRealPushoutRel monadPushSPath pushoutEta

/-- ★★ **`eta` inside a right `s`-frame factors** — `whiskerRight s eta : s ⇒ t·s` factors with the `s`-frame as its
trailing wall and `eta` in the gap.  The clean (`rfl`-cast) direction. -/
def whiskerRightSEtaFactorization :
    PushoutLayoutFactorization crossPairRealPushoutRel
      (RawTwoCellExpr.whiskerRight monadPushSPath pushoutEta) :=
  pushoutFactorizeWhiskerRightGap crossPairRealPushoutRel monadPushSPath pushoutEta

/-! ## Honesty marker -/

/-- ★★★ **Honesty marker — the `whisker` cases (single-gap body) SHIP; the multi-gap head-prepend STAYS the residual
(WP-AMALG-2 r15, B2).**  `= true`.  `whiskerRight oneCell cell` (`pushoutFactorizeWhiskerRightGap`, `finalWall =
oneCell`, `rfl` casts — the trailing frame absorbs definitionally) and `whiskerLeft oneCell cell`
(`pushoutFactorizeWhiskerLeftGap`, leading wall `oneCell`, right-unit cast pushed past via `whiskerLeftCastBoundaryEq`
+ `framedGapInnerConv`) both factor with the frame as an INERT wall around the single body slot.  Non-vacuous at the
REAL pushout signature: `eta` inside an `s`-frame factors on both sides (`whiskerLeftSEtaFactorization` /
`whiskerRightSEtaFactorization`) — the r8-shape `s`-flank building block.

This is `mergeFrameIntoHead/Tail` at the BASE (single-gap / gen-body) granularity.  It does NOT ship the general
head-prepend: `whiskerLeft oneCell body` for an ARBITRARY multi-gap body factorization, which must merge the frame
into the head slot across the `whiskerLeftComp` / `whiskerExchange` associativity casts (the named residual, leg
(b)); the `s`-bearing frame's downstream wall-shift is beyond even that.  `fxAmalg_topFactorizationInductionStaysWalled`
(`PushoutVcompInterchangeSplice.lean`) STAYS `true`; `fxAmalg_hasFullSaturatedPushoutDispatch` /
`fxAmalg_hasGeneralPushoutDispatch` STAY `false`.  #2043 does NOT close.  No fabricated flip.  `= true`. -/
def fxAmalg_hasWhiskerFrameGapCase : Bool := true

end FX1Poly.Polygraph.Amalgam
