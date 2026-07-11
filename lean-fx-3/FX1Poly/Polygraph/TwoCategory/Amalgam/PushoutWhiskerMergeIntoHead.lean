import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWhiskerHeadPrependMultiGap
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutVcompMultiGapSeam

/-! # Polygraph/TwoCategory/Amalgam/PushoutWhiskerMergeIntoHead — the CELL-LEVEL merge-into-head whisker surgery: a
`whiskerLeft` frame FOLDS into the head slot's leading wall (WP-AMALG-2 r17, Brick B1)

r16 (`PushoutWhiskerHeadPrependMultiGap.lean`) shipped the cast-FREE empty-gap PREPEND
(`whiskerLeft_conv_emptyGapPrepend`, `n → n + 1`) and the merge-into-head boundary assoc tower
(`gapDomLayout_mergeFrameIntoHead` / `gapCodLayout_mergeFrameIntoHead`, each a single `composePath_assoc`), and NAMED
the cell-level merge surgery — relating `whiskerLeft oneCell (gapVcompLayout …)` to `gapVcompLayout …
(mergeFrameIntoHead oneCell …)` — as the r17 canonical-reader residual, "riding `whiskerLeftComp` through the
`composePath`-associativity `castBoundary`."  This file AUTHORS that surgery.

## The merge (the CANONICAL frame fold — the slot count is preserved)

`mergeFrameIntoHead oneCell pairs` folds the frame `oneCell` into the HEAD block's leading wall
(`composePath oneCell pair.wall`) rather than opening a fresh leading slot; so the merged layout keeps the body's
`pairs.length` (the frame does NOT add a firing-block slot — it thickens the leading wall).  The cell-level
convertibility `whiskerLeft_conv_mergeFrameIntoHead` proves `whiskerLeft oneCell (gapVcompLayout finalWall pairs)` is
saturated-convertible to the merged layout `gapVcompLayout finalWall (mergeFrameIntoHead oneCell pairs)`, up to the
merge boundary cast (`gapDomLayout_mergeFrameIntoHead`, the SAME `composePath_assoc` the r16 tower ships).

## Why the cast (NOT cast-free — the sharpened r16 finding)

The `[]` case is free (`whiskerLeftId` collapses `whiskerLeft oneCell (id finalWall)` to `id (oneCell · finalWall)`,
absorbed by `emptyGapLayout_conv_id`).  The `pair :: rest` case is genuinely NOT cast-free: folding `oneCell` into
`pair.wall` re-brackets `oneCell · (pair.wall · rest)` to `(oneCell · pair.wall) · rest`, so the convertibility MUST
ride a `composePath_assoc` `castBoundary` — supplied by the completed convertibility's `whiskerLeftComp` law
(`(f ∘ g) ◁ X ≈ f ◁ (g ◁ X)`, threaded through its built-in cast) plus one cast round-trip
(`castBoundaryCongr` + `castBoundary_trans`, the reflexive-cast collapse by proof irrelevance).  This is exactly the
r16-named "riding `whiskerLeftComp` through the `composePath`-associativity `castBoundary`."

## The truth-probe FIRST (a framed two-gap cell)

`whiskerLeftMergeTwoGapWitness` frames the r7 TWO-gap layout `[mu-assoc, left-unit]` (at the REAL pushout signature)
with an `s`-wall and MERGES: the merged layout has `pairs.length = 2` (`sFrameMergeTwoGapSlotCount`, `rfl`) — the
frame folded into the head wall, slot count PRESERVED — contrast the r16 head-prepend (`slotCount = 3`).  The conv
witness `sFrameMergeTwoGapConv` elaborates: the cell-level merge fires on the concrete framed multi-gap cell.

## What STAYS WALLED (no flip)

This ships the CELL-level merge surgery (the r16-named residual) + the framed-two-gap truth-probe.  It does NOT ship:
the full canonical-reader whiskerLeft case threading the body's own `conv` (B4), the `whiskerRight` trailing append
(B2), the `s`-bearing frame's downstream wall-SHIFT (the wire-changing case, leg 2(a'')).  The merge is canonical for
a pure-`s`/`t` frame folding into a wall; an `s`-frame with a WIRE-CHANGING body gap needs the position-shift surgery.
`fxAmalg_topFactorizationInductionStaysWalled` STAYS `true`; the masters STAY at their walled values; #2043 does NOT
close.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## THE CELL-LEVEL MERGE-INTO-HEAD CONVERTIBILITY -/

/-- ★★★ **THE CELL-LEVEL MERGE-INTO-HEAD SURGERY.**  `whiskerLeft oneCell (gapVcompLayout finalWall pairs)` is
saturated-convertible to the merged layout `gapVcompLayout finalWall (mergeFrameIntoHead oneCell pairs)`, up to the
merge boundary cast (`gapDomLayout_mergeFrameIntoHead` / `gapCodLayout_mergeFrameIntoHead`, the r16 assoc tower).

Structural on `pairs`.  `[]` — the frame opens a single `emptyGapPair oneCell`; `whiskerLeft oneCell (id finalWall)`
reduces by `whiskerLeftId` to `id (oneCell · finalWall)`, absorbed by `emptyGapLayout_conv_id`; the merge cast is
reflexive (proof irrelevance).  `pair :: rest` — strip the inner `id pair.wall`-whisker (`whiskerLeft_conv_hcompIdLeading`
reversed under `whiskerLeftCongr`), fuse the two nested left-whiskers by `whiskerLeftComp oneCell pair.wall`, re-fold
the fused `id (oneCell · pair.wall)`-wall (`whiskerLeft_conv_hcompIdLeading`), and collapse the resulting cast
round-trip (`castBoundaryCongr` + `castBoundary_trans`, the `composePath_assoc` combining to a reflexive cast).  Over
ANY signature and base relation. -/
theorem whiskerLeft_conv_mergeFrameIntoHead {signature : ModeSignature} {baseRel : CellRel signature}
    {oneMode : signature.graph.Mode}
    (finalWall oneCell : ModalityPath signature.graph oneMode oneMode) :
    (pairs : List (VcompGapPair signature oneMode)) →
    SaturatedConvOver signature baseRel
      (RawTwoCellExpr.whiskerLeft oneCell (gapVcompLayout finalWall pairs))
      (RawTwoCellExpr.castBoundary
        (gapDomLayout_mergeFrameIntoHead finalWall oneCell pairs)
        (gapCodLayout_mergeFrameIntoHead finalWall oneCell pairs)
        (gapVcompLayout finalWall (mergeFrameIntoHead oneCell pairs)))
  | [] =>
      SaturatedConvOver.trans
        (SaturatedConvOver.ofConv (TwoCellConv.ofStep (TwoCellStep.whiskerLeftId oneCell finalWall)))
        (SaturatedConvOver.symm (emptyGapLayout_conv_id oneCell finalWall))
  | pair :: rest => by
      refine SaturatedConvOver.trans
        (SaturatedConvOver.whiskerLeftCongr oneCell
          (SaturatedConvOver.symm (whiskerLeft_conv_hcompIdLeading pair.wall
            (RawTwoCellExpr.hcomp (RawTwoCellExpr.vcomp pair.upper pair.lower)
              (gapVcompLayout finalWall rest))))) ?_
      have fused : SaturatedConvOver signature baseRel
          (RawTwoCellExpr.castBoundary
            (composePath_assoc oneCell pair.wall
              (composePath pair.gapDom (gapDomLayout finalWall rest))).symm
            (composePath_assoc oneCell pair.wall
              (composePath pair.gapCod (gapCodLayout finalWall rest))).symm
            (RawTwoCellExpr.whiskerLeft oneCell
              (RawTwoCellExpr.whiskerLeft pair.wall
                (RawTwoCellExpr.hcomp (RawTwoCellExpr.vcomp pair.upper pair.lower)
                  (gapVcompLayout finalWall rest)))))
          (RawTwoCellExpr.hcomp (RawTwoCellExpr.id (composePath oneCell pair.wall))
            (RawTwoCellExpr.hcomp (RawTwoCellExpr.vcomp pair.upper pair.lower)
              (gapVcompLayout finalWall rest))) :=
        SaturatedConvOver.trans
          (SaturatedConvOver.symm
            (SaturatedConvOver.ofFull
              (TwoCellConvFull.whiskerLeftComp oneCell pair.wall
                (RawTwoCellExpr.hcomp (RawTwoCellExpr.vcomp pair.upper pair.lower)
                  (gapVcompLayout finalWall rest)))))
          (whiskerLeft_conv_hcompIdLeading (composePath oneCell pair.wall)
            (RawTwoCellExpr.hcomp (RawTwoCellExpr.vcomp pair.upper pair.lower)
              (gapVcompLayout finalWall rest)))
      have rotated := SaturatedConvOver.castBoundaryCongr
        (composePath_assoc oneCell pair.wall
          (composePath pair.gapDom (gapDomLayout finalWall rest)))
        (composePath_assoc oneCell pair.wall
          (composePath pair.gapCod (gapCodLayout finalWall rest))) fused
      rw [RawTwoCellExpr.castBoundary_trans] at rotated
      exact rotated

/-! ## The reflexive layout factorization, MERGED (the reader's whiskerLeft-merge vehicle) -/

/-- ★★ **THE `whiskerLeft` MERGE ARM on a layout body.**  Framing a layout `gapVcompLayout finalWall pairs` with
`whiskerLeft oneCell` factors by MERGING the frame into the head block's leading wall
(`mergeFrameIntoHead oneCell pairs`), keeping the slot count.  Boundary casts are the merge tower
(`gapDomLayout_mergeFrameIntoHead`); the convertibility is `whiskerLeft_conv_mergeFrameIntoHead`.  This is the
canonical (slot-count-preserving) alternative to r16's `pushoutFactorizeWhiskerLeftMultiGap` head-prepend
(`n → n + 1`); here `n → n`.  It consumes a REFLEXIVE layout factorization (the layout as its own factorization), so
it stays in-lane for the truth-probe — the general body threading is the B4 reader. -/
def pushoutFactorizeWhiskerLeftMergeLayout {signature : ModeSignature} (baseRel : CellRel signature)
    {oneMode : signature.graph.Mode}
    (oneCell finalWall : ModalityPath signature.graph oneMode oneMode)
    (pairs : List (VcompGapPair signature oneMode)) :
    PushoutLayoutFactorization baseRel
      (RawTwoCellExpr.whiskerLeft oneCell (gapVcompLayout finalWall pairs)) where
  finalWall := finalWall
  pairs := mergeFrameIntoHead oneCell pairs
  domEq := (gapDomLayout_mergeFrameIntoHead finalWall oneCell pairs).symm
  codEq := (gapCodLayout_mergeFrameIntoHead finalWall oneCell pairs).symm
  conv := by
    have base := SaturatedConvOver.castBoundaryCongr
      (baseRel := baseRel)
      (gapDomLayout_mergeFrameIntoHead finalWall oneCell pairs).symm
      (gapCodLayout_mergeFrameIntoHead finalWall oneCell pairs).symm
      (whiskerLeft_conv_mergeFrameIntoHead finalWall oneCell pairs)
    rw [RawTwoCellExpr.castBoundary_trans] at base
    exact base

/-! ## The truth-probe — a framed TWO-gap cell (FIRST) -/

/-- ★★★ **THE FRAMED TWO-GAP MERGE WITNESS.**  `whiskerLeft s` of the r7 TWO-gap layout `[mu-assoc, left-unit]` (a
`mu`-associativity `t³ ⇒ t` in gap 1, a left-unit `t ⇒ t` in gap 2, at the REAL pushout signature) factors, via the
CELL-level merge, into a TWO-slot layout — the `s`-frame folded into the head block's wall, the slot count PRESERVED
(contrast the r16 head-prepend, which opened a fresh slot to `3`). -/
def whiskerLeftMergeTwoGapWitness :
    PushoutLayoutFactorization crossPairRealPushoutRel
      (RawTwoCellExpr.whiskerLeft monadPushSPath
        (gapVcompLayout pushoutTrivialWall [interleavedAssocGapPair, interleavedLeftUnitGapPair])) :=
  pushoutFactorizeWhiskerLeftMergeLayout crossPairRealPushoutRel monadPushSPath pushoutTrivialWall
    [interleavedAssocGapPair, interleavedLeftUnitGapPair]

/-- ★★★ **PROBE (merged slotCount — PRESERVED).**  The framed two-gap merge witness has `pairs.length = 2` (`rfl`) —
the `s`-frame folded into the head block's leading wall, NOT opening a fresh slot.  This is the canonical
firing-block behaviour: a wall frame thickens the head wall, the slot count is the body's (2).  Contrast r16's
`whiskerLeftMultiGapSlotCount` (`= 3`, the head-prepend). -/
theorem sFrameMergeTwoGapSlotCount : whiskerLeftMergeTwoGapWitness.pairs.length = 2 := rfl

/-- ★★ **PROBE (the merge conv elaborates).**  The cell-level merge convertibility fires on the concrete framed
two-gap cell — `whiskerLeft s [mu-assoc, left-unit]` is saturated-convertible to the merged head-wall layout, at the
REAL pushout signature.  The `whiskerLeft_conv_mergeFrameIntoHead` surgery, machine-witnessed non-vacuously. -/
def sFrameMergeTwoGapConv :
    SaturatedConvOver involutionMonadPushout.toModeSignature crossPairRealPushoutRel
      (RawTwoCellExpr.whiskerLeft monadPushSPath
        (gapVcompLayout pushoutTrivialWall [interleavedAssocGapPair, interleavedLeftUnitGapPair]))
      (RawTwoCellExpr.castBoundary
        (gapDomLayout_mergeFrameIntoHead pushoutTrivialWall monadPushSPath
          [interleavedAssocGapPair, interleavedLeftUnitGapPair])
        (gapCodLayout_mergeFrameIntoHead pushoutTrivialWall monadPushSPath
          [interleavedAssocGapPair, interleavedLeftUnitGapPair])
        (gapVcompLayout pushoutTrivialWall
          (mergeFrameIntoHead monadPushSPath [interleavedAssocGapPair, interleavedLeftUnitGapPair]))) :=
  whiskerLeft_conv_mergeFrameIntoHead pushoutTrivialWall monadPushSPath
    [interleavedAssocGapPair, interleavedLeftUnitGapPair]

/-! ## Observability -/

-- The merged two-gap layout slot count (expect `2`: the `s`-frame folded into the head wall, slot count preserved).
#eval whiskerLeftMergeTwoGapWitness.pairs.length

/-! ## Honesty marker -/

/-- ★★★ **Honesty marker — the CELL-LEVEL merge-into-head whisker surgery SHIPS (WP-AMALG-2 r17, B1).**  `= true`.
`whiskerLeft_conv_mergeFrameIntoHead` proves `whiskerLeft oneCell (gapVcompLayout finalWall pairs)` saturated-convertible
to the merged layout `gapVcompLayout finalWall (mergeFrameIntoHead oneCell pairs)` (up to the r16 merge boundary cast),
structurally on `pairs`: the `[]` case free (`whiskerLeftId` + `emptyGapLayout_conv_id`), the `pair :: rest` case
riding the `composePath_assoc` cast via the completed convertibility's `whiskerLeftComp` law plus one cast round-trip
(`castBoundaryCongr` + `castBoundary_trans`).  This is the r16-named canonical-reader residual — the CELL-level merge
surgery — now authored.  The `whiskerLeft` merge arm on a layout body (`pushoutFactorizeWhiskerLeftMergeLayout`) keeps
the slot count (`n → n`, canonical, contrast r16's head-prepend `n → n + 1`).  Non-vacuous at the REAL pushout
signature: `whiskerLeftMergeTwoGapWitness` frames the r7 two-gap `[mu-assoc, left-unit]` body with an `s`-wall and
MERGES to a TWO-slot layout (`sFrameMergeTwoGapSlotCount`, `= 2` by `rfl`; the conv `sFrameMergeTwoGapConv`
elaborates).

This does NOT ship the full canonical-reader whiskerLeft case threading the body's own `conv` (B4), the `whiskerRight`
trailing append (B2), or the `s`-bearing frame's downstream wall-SHIFT (the wire-changing case, leg 2(a'')).
`fxAmalg_topFactorizationInductionStaysWalled` STAYS `true`; `fxAmalg_hasFullSaturatedPushoutDispatch` /
`fxAmalg_hasGeneralPushoutDispatch` STAY `false`.  #2043 does NOT close.  No fabricated flip.  `= true`. -/
def fxAmalg_hasWhiskerMergeIntoHeadCell : Bool := true

end FX1Poly.Polygraph.Amalgam
