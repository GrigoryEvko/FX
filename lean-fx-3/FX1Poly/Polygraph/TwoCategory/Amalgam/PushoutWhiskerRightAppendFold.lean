import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWhiskerRightAppend
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadWhiskerRightMult

/-! # Polygraph/TwoCategory/Amalgam/PushoutWhiskerRightAppendFold — LEG 1: the `whiskerRight` trailing-frame append
CONS-CASE assembly, folding the frame down the right-nested layout (WP-AMALG-2 r18, Brick B3)

r17 (`PushoutWhiskerRightAppend.lean`) shipped the trailing-append MACHINERY — the hcomp right-push engine
`whiskerRight_conv_hcompRight`, the distribution inductions `gapDomLayoutAppendFinalWall` /
`gapCodLayoutAppendFinalWall`, the base case `whiskerRight_conv_appendFinalWall_nil` — and NAMED the residual: the
`pair :: rest` cons-case assembly of the full `whiskerRight_conv_appendFinalWall`, "a pure cast-plumbing induction
folding the frame down the right-nested layout by iterating `whiskerRight_conv_hcompRight` (shipped),
`hcomp_castBoundaryRight` (reachable), and `castBoundary_trans` (shipped), merging the per-block associator casts into
the single `gapDomLayoutAppendFinalWall` distribution cast by proof irrelevance."  This file AUTHORS that assembly.

## The fold (the frame passes down the whole right-nested layout to the trailing wall)

`gapVcompLayout finalWall (pair :: rest) = hcomp (id pair.wall) (hcomp (vcomp pair.upper pair.lower)
(gapVcompLayout finalWall rest))`.  A `whiskerRight oneCell` frame passes the OUTER `id pair.wall` and the block
payload `vcomp pair.upper pair.lower` by two applications of the shipped push engine `whiskerRight_conv_hcompRight`,
and reaches the tail `gapVcompLayout finalWall rest` where the INDUCTION HYPOTHESIS folds it into
`gapVcompLayout (composePath finalWall oneCell) rest`.  Every block contributes one `composePath_assoc`
re-anchoring cast; the two per-block casts plus the tail cast merge into the single
`gapDomLayoutAppendFinalWall` / `gapCodLayoutAppendFinalWall` distribution cast by `Eq` proof irrelevance.

## The reusable cast-pull helper (the recon-named `hcomp_castBoundaryRight` lifted to the conv)

  * **`hcomp_conv_castBoundaryRight`** — pulls a right-factor boundary cast out of a horizontal composite at the
    saturated-conv level: `hcompCongrRight` threads the body conv, then `hcomp_castBoundaryRight` (a cell equality)
    pulls the cast to the outside.  The clean vehicle the fold iterates per block.

## The DUAL of the shipped `whiskerLeft_conv_mergeFrameIntoHead`

The whiskerLeft MERGE (r17) folds a frame into the HEAD wall via `whiskerLeftComp` (fuse) and does NOT recurse — it
is `n → n`.  The whiskerRight APPEND (this file) folds a frame into the TRAILING wall via `whiskerRight_conv_hcompRight`
(push) and DOES recurse the tail via the IH — it is also `n → n` but genuinely iterates.  Both are cast-plumbing; the
recon's "pure plumbing, all ingredients shipped" claim holds.

## What STAYS WALLED (no flip)

This ships the full cons-case fold — the leg-1 residual is now SHIPPED (`fxAmalg_hasWhiskerRightAppendCell = true`,
upgrading the r17 `…Engine` marker).  It does NOT ship: the general firing-block PRODUCER over arbitrary paths, the
`s`-bearing frame's downstream wall-SHIFT (the wire-changing case, leg 2a''), or the JAM A per-gap descent.
`fxAmalg_topFactorizationInductionStaysWalled` STAYS `true`; the masters STAY at their walled values;
`fxAmalg_sFrameWallShiftStaysWalled` STAYS `true`; #2043 does NOT close.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The reusable right-factor cast-pull at the saturated-conv level -/

/-- ★★ **Pull a right-factor boundary cast out of a horizontal composite (saturated-conv level).**  If `body` is
saturated-convertible to a boundary-cast of `bodyTarget`, then `hcomp cellA body` is convertible to the corresponding
whole-composite cast of `hcomp cellA bodyTarget`.  `hcompCongrRight` threads the conv into the right factor, then the
cell equality `hcomp_castBoundaryRight` pulls the cast to the outside (rewriting the RHS cell only — the LHS `body` is
not a cast, so the rewrite is a fixed-boundary congruence, propext-free).  The conv-level lift of
`RawTwoCellExpr.hcomp_castBoundaryRight`; the vehicle the trailing-append fold iterates. -/
theorem hcomp_conv_castBoundaryRight {signature : ModeSignature} {baseRel : CellRel signature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    {oneCellFDom oneCellFCod : ModalityPath signature.graph sourceMode middleMode}
    {oneCellGDom oneCellGDom' oneCellGCod oneCellGCod' : ModalityPath signature.graph middleMode targetMode}
    (cellA : RawTwoCellExpr signature oneCellFDom oneCellFCod)
    {hdom : oneCellGDom = oneCellGDom'} {hcod : oneCellGCod = oneCellGCod'}
    {body : RawTwoCellExpr signature oneCellGDom' oneCellGCod'}
    {bodyTarget : RawTwoCellExpr signature oneCellGDom oneCellGCod}
    (conv : SaturatedConvOver signature baseRel body
      (RawTwoCellExpr.castBoundary hdom hcod bodyTarget)) :
    SaturatedConvOver signature baseRel (RawTwoCellExpr.hcomp cellA body)
      (RawTwoCellExpr.castBoundary (congrArg (composePath oneCellFDom) hdom)
        (congrArg (composePath oneCellFCod) hcod) (RawTwoCellExpr.hcomp cellA bodyTarget)) := by
  have threaded := SaturatedConvOver.hcompCongrRight cellA conv
  rw [RawTwoCellExpr.hcomp_castBoundaryRight] at threaded
  exact threaded

/-! ## LEG 1 — the full trailing-frame append, cons case folded -/

/-- ★★★ **THE `whiskerRight` TRAILING APPEND — the full fold (r17 leg-1 residual, SHIPPED).**
`whiskerRight oneCell (gapVcompLayout finalWall pairs)` is saturated-convertible to the trailing-thickened layout
`gapVcompLayout (composePath finalWall oneCell) pairs`, up to the `gapDomLayoutAppendFinalWall` /
`gapCodLayoutAppendFinalWall` distribution cast — the frame folds into the trailing wall `finalWall`, keeping the slot
count.

Structural on `pairs`.  `[]` is the shipped base case `whiskerRight_conv_appendFinalWall_nil` (the distribution cast is
reflexive on `[]`, so the boundary-cast collapses definitionally).  `pair :: rest` folds the frame down the
right-nested layout: the shipped push engine `whiskerRight_conv_hcompRight` passes the OUTER `id pair.wall`, then
passes the block payload `vcomp pair.upper pair.lower`, then the IH folds the tail; the two per-block associator casts
plus the IH cast merge into the single distribution cast by `hcomp_conv_castBoundaryRight` (twice) + `castBoundary_trans`
(twice), the residual proofs collapsing by `Eq` proof irrelevance.  Over ANY signature and base relation. -/
theorem whiskerRight_conv_appendFinalWall {signature : ModeSignature} {baseRel : CellRel signature}
    {oneMode : signature.graph.Mode}
    (oneCell finalWall : ModalityPath signature.graph oneMode oneMode) :
    (pairs : List (VcompGapPair signature oneMode)) →
    SaturatedConvOver signature baseRel
      (RawTwoCellExpr.whiskerRight oneCell (gapVcompLayout finalWall pairs))
      (RawTwoCellExpr.castBoundary
        (gapDomLayoutAppendFinalWall oneCell finalWall pairs)
        (gapCodLayoutAppendFinalWall oneCell finalWall pairs)
        (gapVcompLayout (composePath finalWall oneCell) pairs))
  | [] => by exact whiskerRight_conv_appendFinalWall_nil oneCell finalWall
  | pair :: rest => by
      have chain := SaturatedConvOver.trans (baseRel := baseRel)
        (whiskerRight_conv_hcompRight oneCell (RawTwoCellExpr.id pair.wall)
          (RawTwoCellExpr.hcomp (RawTwoCellExpr.vcomp pair.upper pair.lower)
            (gapVcompLayout finalWall rest)))
        (SaturatedConvOver.castBoundaryCongr _ _
          (SaturatedConvOver.hcompCongrRight (RawTwoCellExpr.id pair.wall)
            (SaturatedConvOver.trans
              (whiskerRight_conv_hcompRight oneCell (RawTwoCellExpr.vcomp pair.upper pair.lower)
                (gapVcompLayout finalWall rest))
              (SaturatedConvOver.castBoundaryCongr _ _
                (hcomp_conv_castBoundaryRight (RawTwoCellExpr.vcomp pair.upper pair.lower)
                  (whiskerRight_conv_appendFinalWall oneCell finalWall rest))))))
      rw [RawTwoCellExpr.castBoundary_trans, RawTwoCellExpr.hcomp_castBoundaryRight,
          RawTwoCellExpr.castBoundary_trans] at chain
      exact chain

/-! ## Honesty marker -/

/-- ★★★ **Honesty marker — the `whiskerRight` trailing-append CONS-CASE FOLD SHIPS (WP-AMALG-2 r18, B3 / leg 1).**
`= true`.  `whiskerRight_conv_appendFinalWall` (this file) proves the FULL trailing append — `whiskerRight oneCell
(gapVcompLayout finalWall pairs)` saturated-convertible to `gapVcompLayout (composePath finalWall oneCell) pairs` up to
the `gapDomLayoutAppendFinalWall` / `gapCodLayoutAppendFinalWall` distribution cast — structurally on `pairs`: the `[]`
case the shipped base `whiskerRight_conv_appendFinalWall_nil`, the `pair :: rest` case the recon-named fold iterating
the shipped push engine `whiskerRight_conv_hcompRight` twice (passing the outer `id pair.wall` and the block payload)
and the IH, merging the per-block associator casts into the single distribution cast via the reusable
`hcomp_conv_castBoundaryRight` (the conv-lift of `hcomp_castBoundaryRight`) + `castBoundary_trans`.  This UPGRADES the
r17 residual marker `fxAmalg_hasWhiskerRightAppendEngine` (the machinery) to the SHIPPED fold.

This does NOT ship: the general firing-block PRODUCER over arbitrary paths, the `s`-bearing frame's downstream
wall-SHIFT (the wire-changing case, leg 2a''), or the JAM A per-gap descent.
`fxAmalg_topFactorizationInductionStaysWalled` STAYS `true`; `fxAmalg_sFrameWallShiftStaysWalled` STAYS `true`;
`fxAmalg_hasFullSaturatedPushoutDispatch` / `fxAmalg_hasGeneralPushoutDispatch` STAY `false`.  #2043 does NOT close.
No fabricated flip.  `= true`. -/
def fxAmalg_hasWhiskerRightAppendCell : Bool := true

end FX1Poly.Polygraph.Amalgam
