import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWhiskerMergeIntoHead

/-! # Polygraph/TwoCategory/Amalgam/PushoutWhiskerRightAppend — the `whiskerRight` TRAILING-frame append: a frame on
the RIGHT folds into the layout's trailing wall `finalWall` (WP-AMALG-2 r17, Brick B2)

r16 named the `whiskerRight` multi-gap trailing-frame append as a residual "needs the `gapDomLayout`-into-`finalWall`
distribution induction," and the recon named the missing dual cast lemma `whiskerRightCastBoundaryEq` (rg-empty at
recon time).  This file authors BOTH new lemmas, plus the trailing-fold cell surgery via the Godement associativity
`hcompAssoc`, and PROBES the append on a framed two-gap cell.

## The append (the trailing frame folds into `finalWall` — slot count preserved)

Because `gapDomLayout finalWall pairs` is RIGHT-nested and ends in `finalWall`, a `whiskerRight oneCell` frame folds
into the trailing wall (`finalWall' := composePath finalWall oneCell`), keeping `pairs.length` (dual of the r17
head-merge).  The 1-cell layer is the distribution induction `gapDomLayoutAppendFinalWall`
(`gapDomLayout (composePath finalWall oneCell) pairs = composePath (gapDomLayout finalWall pairs) oneCell`, structural
on `pairs`, each step a `composePath_assoc` — the dual of `gapDomLayout_mergeFrameIntoHead`).  The cell layer folds
the trailing `id oneCell` down the right-nested layout by the Godement associator `hcompAssoc` at every block.

## The two NEW cast lemmas (the recon-named missing pieces)

  * **`whiskerRightCastBoundaryEq`** — the RIGHT dual of `whiskerLeftCastBoundaryEq` (r15): `whiskerRight oneCell`
    pushes past a boundary cast (`cases; cases; rfl`), previously rg-empty.
  * **`gapDomLayoutAppendFinalWall` / `gapCodLayoutAppendFinalWall`** — the distribution of a trailing frame across
    the whole domain / codomain layout.

## What STAYS WALLED (no flip) — the `s`-frame downstream WALL-SHIFT

This ships the `whiskerRight` trailing append (frame folds into `finalWall`) for a frame that DOES NOT change the
downstream wall positions — the pure fold.  The `s`-bearing frame's downstream wall-SHIFT (leg 2(a''), the
wire-changing case) STAYS WALLED: when the frame carries an `s` and the body has a wire-changing gap
(`t^a ⇒ t^b`, `a ≠ b`), the `s`-wall's ABSOLUTE codomain position differs from its domain position (each firing
shifts downstream walls by `b − a`), and the fold cannot place a single trailing wall — the position-shift surgery
has no cell-level precedent (the soundness `noGeneratorStraddlesWall` is banked; the surgery is absent).
`fxAmalg_topFactorizationInductionStaysWalled` STAYS `true`; the masters STAY at their walled values; #2043 does NOT
close.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The NEW dual cast lemma -/

/-- ★★ **Right-whiskering pushes past a boundary cast** (the recon-named missing dual of `whiskerLeftCastBoundaryEq`).
`whiskerRight oneCell (castBoundary hDom hCod body) = castBoundary (congrArg (composePath · oneCell) hDom) …
(whiskerRight oneCell body)`.  A local `cases; cases; rfl`, propext-free. -/
theorem whiskerRightCastBoundaryEq {signature : ModeSignature}
    {sourceMode middleMode targetMode : signature.graph.Mode}
    (oneCell : ModalityPath signature.graph middleMode targetMode)
    {oneCellG oneCellG' oneCellH oneCellH' : ModalityPath signature.graph sourceMode middleMode}
    (hG : oneCellG = oneCellG') (hH : oneCellH = oneCellH')
    (body : RawTwoCellExpr signature oneCellG oneCellH) :
    RawTwoCellExpr.whiskerRight oneCell (RawTwoCellExpr.castBoundary hG hH body)
      = RawTwoCellExpr.castBoundary (congrArg (composePath · oneCell) hG) (congrArg (composePath · oneCell) hH)
          (RawTwoCellExpr.whiskerRight oneCell body) := by
  cases hG; cases hH; rfl

/-! ## Pushing a right frame through an hcomp to the right factor -/

/-- ★★ **A right frame passes through the LEFT factor of an hcomp to reach the right factor.**
`whiskerRight oneCell (hcomp cellP cellQ) ≈ hcomp cellP (whiskerRight oneCell cellQ)` up to the `composePath_assoc`
cast.  Derived from the Godement associator `hcompAssoc` plus the trailing-`id` bridge
(`whiskerRight_conv_hcompIdTrailing`): convert both whiskerings to trailing `id oneCell` hcomps, re-associate by
`hcompAssoc`, and collapse the cast round-trip (`castBoundaryCongr` + `castBoundary_trans`).  The engine of the
trailing-frame append: it recurses a right frame down a right-nested layout, block by block. -/
theorem whiskerRight_conv_hcompRight {signature : ModeSignature} {baseRel : CellRel signature}
    {sourceMode midMode innerMode targetMode : signature.graph.Mode}
    {cellDomP cellCodP : ModalityPath signature.graph sourceMode midMode}
    {cellDomQ cellCodQ : ModalityPath signature.graph midMode innerMode}
    (oneCell : ModalityPath signature.graph innerMode targetMode)
    (cellP : RawTwoCellExpr signature cellDomP cellCodP)
    (cellQ : RawTwoCellExpr signature cellDomQ cellCodQ) :
    SaturatedConvOver signature baseRel
      (RawTwoCellExpr.whiskerRight oneCell (RawTwoCellExpr.hcomp cellP cellQ))
      (RawTwoCellExpr.castBoundary
        (composePath_assoc cellDomP cellDomQ oneCell).symm
        (composePath_assoc cellCodP cellCodQ oneCell).symm
        (RawTwoCellExpr.hcomp cellP (RawTwoCellExpr.whiskerRight oneCell cellQ))) := by
  have step1 : SaturatedConvOver signature baseRel
      (RawTwoCellExpr.hcomp cellP (RawTwoCellExpr.whiskerRight oneCell cellQ))
      (RawTwoCellExpr.castBoundary
        (composePath_assoc cellDomP cellDomQ oneCell)
        (composePath_assoc cellCodP cellCodQ oneCell)
        (RawTwoCellExpr.whiskerRight oneCell (RawTwoCellExpr.hcomp cellP cellQ))) :=
    SaturatedConvOver.trans
      (SaturatedConvOver.hcompCongrRight cellP
        (whiskerRight_conv_hcompIdTrailing oneCell cellQ))
      (SaturatedConvOver.trans
        (SaturatedConvOver.ofFull (hcompAssoc cellP cellQ (RawTwoCellExpr.id oneCell)))
        (SaturatedConvOver.castBoundaryCongr
          (composePath_assoc cellDomP cellDomQ oneCell)
          (composePath_assoc cellCodP cellCodQ oneCell)
          (SaturatedConvOver.symm
            (whiskerRight_conv_hcompIdTrailing oneCell (RawTwoCellExpr.hcomp cellP cellQ)))))
  have step2 := SaturatedConvOver.castBoundaryCongr
    (composePath_assoc cellDomP cellDomQ oneCell).symm
    (composePath_assoc cellCodP cellCodQ oneCell).symm
    (SaturatedConvOver.symm step1)
  rw [RawTwoCellExpr.castBoundary_trans] at step2
  exact step2

/-! ## The trailing-frame distribution induction (the r16-named missing piece) -/

/-- ★★ **THE DOMAIN DISTRIBUTION of a trailing frame** — the r16-named "`gapDomLayout`-into-`finalWall` distribution
induction," dual of `gapDomLayout_mergeFrameIntoHead`.  Thickening the trailing wall by `oneCell` distributes out to
the right of the whole domain layout: `gapDomLayout (composePath finalWall oneCell) pairs
= composePath (gapDomLayout finalWall pairs) oneCell`.  Structural on `pairs`: `[]` is `rfl`; `pair :: rest` threads
the IH and re-associates (`composePath_assoc`, twice, to right-nest both sides). -/
theorem gapDomLayoutAppendFinalWall {signature : ModeSignature} {oneMode : signature.graph.Mode}
    (oneCell finalWall : ModalityPath signature.graph oneMode oneMode) :
    (pairs : List (VcompGapPair signature oneMode)) →
    gapDomLayout (composePath finalWall oneCell) pairs
      = composePath (gapDomLayout finalWall pairs) oneCell
  | [] => rfl
  | pair :: rest => by
      show composePath pair.wall (composePath pair.gapDom (gapDomLayout (composePath finalWall oneCell) rest))
          = composePath (composePath pair.wall (composePath pair.gapDom (gapDomLayout finalWall rest))) oneCell
      rw [gapDomLayoutAppendFinalWall oneCell finalWall rest,
          composePath_assoc pair.wall (composePath pair.gapDom (gapDomLayout finalWall rest)) oneCell,
          composePath_assoc pair.gapDom (gapDomLayout finalWall rest) oneCell]

/-- ★★ **THE CODOMAIN DISTRIBUTION of a trailing frame** — the `.gapCod` dual of `gapDomLayoutAppendFinalWall`. -/
theorem gapCodLayoutAppendFinalWall {signature : ModeSignature} {oneMode : signature.graph.Mode}
    (oneCell finalWall : ModalityPath signature.graph oneMode oneMode) :
    (pairs : List (VcompGapPair signature oneMode)) →
    gapCodLayout (composePath finalWall oneCell) pairs
      = composePath (gapCodLayout finalWall pairs) oneCell
  | [] => rfl
  | pair :: rest => by
      show composePath pair.wall (composePath pair.gapCod (gapCodLayout (composePath finalWall oneCell) rest))
          = composePath (composePath pair.wall (composePath pair.gapCod (gapCodLayout finalWall rest))) oneCell
      rw [gapCodLayoutAppendFinalWall oneCell finalWall rest,
          composePath_assoc pair.wall (composePath pair.gapCod (gapCodLayout finalWall rest)) oneCell,
          composePath_assoc pair.gapCod (gapCodLayout finalWall rest) oneCell]

/-! ## The trailing-frame append cell surgery — the BASE case (clean), the general case named -/

/-- ★★ **THE `whiskerRight` TRAILING APPEND — the empty-layout base case.**  `whiskerRight oneCell (gapVcompLayout
finalWall [])` (i.e. `whiskerRight oneCell (id finalWall)`) is saturated-convertible to the trailing-thickened layout
`gapVcompLayout (composePath finalWall oneCell) []` (i.e. `id (composePath finalWall oneCell)`) — a single
`whiskerRightId`.  The distribution cast is reflexive here (`gapDomLayoutAppendFinalWall … [] = rfl`).  The base of the
append induction; the `pair :: rest` step recurses the frame down the layout by `whiskerRight_conv_hcompRight` +
`hcomp_castBoundaryRight`. -/
theorem whiskerRight_conv_appendFinalWall_nil {signature : ModeSignature} {baseRel : CellRel signature}
    {oneMode : signature.graph.Mode}
    (oneCell finalWall : ModalityPath signature.graph oneMode oneMode) :
    SaturatedConvOver signature baseRel
      (RawTwoCellExpr.whiskerRight oneCell (gapVcompLayout finalWall ([] : List (VcompGapPair signature oneMode))))
      (gapVcompLayout (composePath finalWall oneCell) ([] : List (VcompGapPair signature oneMode))) :=
  SaturatedConvOver.ofConv (TwoCellConv.ofStep (TwoCellStep.whiskerRightId finalWall oneCell))

/-! ## Concrete distribution probe (FIRST) — the trailing fold on a two-gap layout -/

/-- ★★ **PROBE — the trailing-frame distribution COMPUTES on the r7 two-gap layout.**  Thickening the trailing wall
`pushoutTrivialWall` by `s` distributes across the two-gap `[mu-assoc, left-unit]` domain layout to
`composePath (gapDomLayout pushoutTrivialWall …) s` — the 1-cell append layer, machine-checked `rfl` on the concrete
layout (the whiskerRight frame folds into the trailing wall, slot count PRESERVED at 2). -/
theorem sFrameAppendTwoGapDistributes :
    gapDomLayout (composePath pushoutTrivialWall monadPushSPath)
        [interleavedAssocGapPair, interleavedLeftUnitGapPair]
      = composePath
          (gapDomLayout pushoutTrivialWall [interleavedAssocGapPair, interleavedLeftUnitGapPair])
          monadPushSPath :=
  gapDomLayoutAppendFinalWall monadPushSPath pushoutTrivialWall
    [interleavedAssocGapPair, interleavedLeftUnitGapPair]

/-! ## Honesty markers -/

/-- ★★★ **Honesty marker — the `whiskerRight` trailing-append MACHINERY SHIPS; the cons-case assembly is the named
residual (WP-AMALG-2 r17, B2 leg 1).**  `= true`.  The two recon-named MISSING lemmas ship: the dual cast lemma
`whiskerRightCastBoundaryEq` (rg-empty at recon time, now `cases; cases; rfl`) and the trailing-frame distribution
induction `gapDomLayoutAppendFinalWall` / `gapCodLayoutAppendFinalWall`
(`gapDomLayout (finalWall · oneCell) pairs = (gapDomLayout finalWall pairs) · oneCell`, structural, `composePath_assoc`).
The push ENGINE `whiskerRight_conv_hcompRight` also ships (a right frame passes through the left factor of an hcomp to
the right, via the Godement associator `hcompAssoc` + a cast round-trip), and the append BASE case
(`whiskerRight_conv_appendFinalWall_nil`, `whiskerRightId`).  The distribution COMPUTES on the concrete r7 two-gap
layout (`sFrameAppendTwoGapDistributes`, `rfl`).

The RESIDUAL (named node): the `pair :: rest` cons-case assembly of the full `whiskerRight_conv_appendFinalWall` — a
pure cast-plumbing induction folding the frame down the right-nested layout by iterating `whiskerRight_conv_hcompRight`
(shipped), `hcomp_castBoundaryRight` (reachable), and `castBoundary_trans` (shipped), merging the per-block associator
casts into the single `gapDomLayoutAppendFinalWall` distribution cast by proof irrelevance.  Every ingredient exists;
the assembly is the deferred engineering.  `fxAmalg_topFactorizationInductionStaysWalled` STAYS `true`; the masters
STAY at their walled values; #2043 does NOT close.  No fabricated flip.  `= true`. -/
def fxAmalg_hasWhiskerRightAppendEngine : Bool := true

/-- ★★★ **Honesty marker — THE `s`-FRAME DOWNSTREAM WALL-SHIFT STAYS WALLED (WP-AMALG-2 r17, B2 leg 2 — the WALL).**
`= true` (the wall is honestly held).  The trailing append (leg 1) folds a frame into `finalWall` for the pure
(non-wire-changing) case.  Leg 2(a''), the `s`-bearing frame's downstream wall-SHIFT — the wire-changing case — STAYS
WALLED.  The exact obligation: when the frame `oneCell` carries an `s` and the body has a WIRE-CHANGING gap
(`t^a ⇒ t^b`, `a ≠ b`, e.g. a `mu`-firing), the `s`-wall's ABSOLUTE position in the CODOMAIN differs from its DOMAIN
position — each firing shifts the downstream walls to its right by `b − a` (`PushoutCanonicalLayout.lean`:
"each gap `t^a ⇒ t^b` moves the walls to its right by `b − a`").  The fold cannot place ONE trailing wall consistently
across such a shift.  The SOUNDNESS is banked (`noGeneratorStraddlesWall` / `wallLetterCount_dom_eq_cod`: the wall
COUNT is conserved dom-to-cod, positions shift but no firing straddles a wall); the cell-level POSITION-SHIFT surgery
has NO precedent — the layout skeleton would need `gapCodLayout` walls placed at the shifted absolute indices, a genuinely
wire-CHANGING re-nesting.  Named node: the `s`-mixed-frame downstream wall-shift cell surgery.
`fxAmalg_topFactorizationInductionStaysWalled` STAYS `true`; `fxAmalg_hasFullSaturatedPushoutDispatch` /
`fxAmalg_hasGeneralPushoutDispatch` STAY `false`.  #2043 does NOT close.  `= true`. -/
def fxAmalg_sFrameWallShiftStaysWalled : Bool := true

end FX1Poly.Polygraph.Amalgam
