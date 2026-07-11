import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWhiskerRightAppendFold
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFactorizeTotalAssembly
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWallShiftOffset

/-! # Polygraph/TwoCategory/Amalgam/PushoutFactorizeCanonicalWhiskerRight — the CANONICAL `whiskerRight` merge-layout
arm (`n → n`, off leg 1), the wild-cell slot-count probes, and the JAM A re-audit (WP-AMALG-2 r18, Brick B4)

r18 leg 1 (`PushoutWhiskerRightAppendFold.lean`) shipped the full trailing append `whiskerRight_conv_appendFinalWall`.
This file wires it into the CANONICAL `whiskerRight` factorization arm — the exact DUAL of the shipped whiskerLeft merge
arm `pushoutFactorizeWhiskerLeftMergeLayout` — and probes the reader's slot counts on the historical wild cells and a
fresh wire-changing composite.

## The canonical `whiskerRight` arm (`n → n`, slot count preserved)

`pushoutFactorizeWhiskerRightMergeLayout` factors `whiskerRight oneCell (gapVcompLayout finalWall pairs)` by folding the
frame into the TRAILING wall (`finalWall' := composePath finalWall oneCell`), keeping the body's `pairs.length` — the
canonical (slot-count-preserving) alternative to the r15 single-gap `pushoutFactorizeWhiskerRightGap`.  The conv rides
leg 1 (`whiskerRight_conv_appendFinalWall`) through the round-trip cast collapse (`castBoundaryCongr` +
`castBoundary_trans`), exactly as the shipped whiskerLeft merge arm rides `whiskerLeft_conv_mergeFrameIntoHead`.

## The wild-cell probes

  * `whiskerRightMergeTwoGapWitness` — the r7 two-gap layout `[mu-assoc, left-unit]` framed on the RIGHT by an `s`-wall,
    the DUAL of `whiskerLeftMergeTwoGapWitness`: the frame folds into the trailing wall, slot count PRESERVED (`= 2`).
  * `muBlockRightFrameWitness` — a FRESH wire-changing composite: the `mu`-firing block `muWallShiftBlock` (`t·t ⇒ t`)
    framed on the RIGHT by an `s`-wall, slot count PRESERVED (`= 1`).
  * `genMeetsCanonicalSlotSpec` — the shallow total reader's `gen` arm MEETS the finest slot-count spec on the wall-free
    `mu` boundary (`slotCount = 1 = wallCount + 1`), and the canonical `id nil` meets it too (`= 1`).

## The JAM A re-audit — NO descent overclaim

The r18 canonical whiskerRight arm STRENGTHENS the whisker coverage but supplies NONE of the JAM A per-gap DESCENT: the
convex-block projection the wire-creating `eta`/`mu` violate stays the residual (`fxAmalg_hasSaturatedDispatchTheorem =
false`).  The TOTAL canonical reader (threading each body's own factorization conv through the merge/append arms, and
the general firing-block producer for `s`-frames) stays GATED — the merge/append arms keep the body's slot count `n`,
which equals `wallCount + 1` only for WALL-FREE frames; an `s`-frame needs the interior-ordinal producer (B2's named
node).  So the masters STAY: `fxAmalg_hasFullSaturatedPushoutDispatch` / `fxAmalg_hasGeneralPushoutDispatch` `false`,
`fxAmalg_topFactorizationInductionStaysWalled` `true`.  #2043 does NOT close.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The canonical `whiskerRight` merge-layout arm (`n → n`) -/

/-- ★★★ **THE CANONICAL `whiskerRight` MERGE ARM on a layout body.**  Framing a layout `gapVcompLayout finalWall pairs`
with `whiskerRight oneCell` factors by folding the frame into the TRAILING wall (`composePath finalWall oneCell`),
keeping the slot count `pairs.length`.  Boundary casts are the leg-1 distribution
(`gapDomLayoutAppendFinalWall` / `gapCodLayoutAppendFinalWall`); the convertibility is leg 1
(`whiskerRight_conv_appendFinalWall`) collapsed through the cast round-trip.  The exact DUAL of the shipped whiskerLeft
merge arm `pushoutFactorizeWhiskerLeftMergeLayout` — the canonical (`n → n`) alternative to r15's single-gap
`pushoutFactorizeWhiskerRightGap`.  Over ANY signature and base relation. -/
def pushoutFactorizeWhiskerRightMergeLayout {signature : ModeSignature} (baseRel : CellRel signature)
    {oneMode : signature.graph.Mode}
    (oneCell finalWall : ModalityPath signature.graph oneMode oneMode)
    (pairs : List (VcompGapPair signature oneMode)) :
    PushoutLayoutFactorization baseRel
      (RawTwoCellExpr.whiskerRight oneCell (gapVcompLayout finalWall pairs)) where
  finalWall := composePath finalWall oneCell
  pairs := pairs
  domEq := (gapDomLayoutAppendFinalWall oneCell finalWall pairs).symm
  codEq := (gapCodLayoutAppendFinalWall oneCell finalWall pairs).symm
  conv := by
    have base := SaturatedConvOver.castBoundaryCongr
      (baseRel := baseRel)
      (gapDomLayoutAppendFinalWall oneCell finalWall pairs).symm
      (gapCodLayoutAppendFinalWall oneCell finalWall pairs).symm
      (whiskerRight_conv_appendFinalWall oneCell finalWall pairs)
    rw [RawTwoCellExpr.castBoundary_trans] at base
    exact base

/-! ## The wild-cell probes -/

/-- ★★★ **THE FRAMED TWO-GAP RIGHT-MERGE WITNESS (the DUAL of `whiskerLeftMergeTwoGapWitness`).**  `whiskerRight s` of
the r7 TWO-gap layout `[mu-assoc, left-unit]` (at the REAL pushout signature) factors, via the CANONICAL whiskerRight
arm, into a TWO-slot layout — the `s`-frame folded into the trailing wall, slot count PRESERVED. -/
def whiskerRightMergeTwoGapWitness :
    PushoutLayoutFactorization crossPairRealPushoutRel
      (RawTwoCellExpr.whiskerRight monadPushSPath
        (gapVcompLayout pushoutTrivialWall [interleavedAssocGapPair, interleavedLeftUnitGapPair])) :=
  pushoutFactorizeWhiskerRightMergeLayout crossPairRealPushoutRel monadPushSPath pushoutTrivialWall
    [interleavedAssocGapPair, interleavedLeftUnitGapPair]

/-- ★★★ **PROBE (right-merged slotCount — PRESERVED).**  The framed two-gap right-merge witness has `pairs.length = 2`
(`rfl`) — the `s`-frame folded into the trailing wall, the slot count the body's `2`.  The DUAL of
`sFrameMergeTwoGapSlotCount`. -/
theorem whiskerRightMergeTwoGapSlotCount : whiskerRightMergeTwoGapWitness.pairs.length = 2 := rfl

/-- ★★★ **A FRESH WIRE-CHANGING COMPOSITE through the canonical whiskerRight arm.**  `whiskerRight s` of the
single-block layout whose gap is the `mu`-firing wire-changing block `muWallShiftBlock` (`t·t ⇒ t`) factors, via the
canonical arm, folding the `s`-frame into the trailing wall.  The frame sits at the trailing ordinal
(placed by `gapCodLayoutAppendFinalWall` unconditionally), so the fold fires DESPITE the wire-changing body. -/
def muBlockRightFrameWitness :
    PushoutLayoutFactorization crossPairRealPushoutRel
      (RawTwoCellExpr.whiskerRight monadPushSPath
        (gapVcompLayout pushoutTrivialWall [muWallShiftBlock])) :=
  pushoutFactorizeWhiskerRightMergeLayout crossPairRealPushoutRel monadPushSPath pushoutTrivialWall
    [muWallShiftBlock]

/-- ★★★ **PROBE (the wire-changing composite's slotCount — PRESERVED).**  The fresh wire-changing composite factors
with `pairs.length = 1` (`rfl`) — the trailing `s`-frame folded into the wall, the slot count preserved even through
the `mu` firing. -/
theorem muBlockRightFrameSlotCount : muBlockRightFrameWitness.pairs.length = 1 := rfl

/-- ★★★ **PROBE (the wall-free arms MEET the finest slot-count spec).**  The shallow total reader's `gen` arm on the
`mu` firing produces `1` slot, exactly the finest spec `(finestGapWidths (pushoutPathTags (t·t))).length = wallCount + 1
= 0 + 1 = 1`; and the canonical `id nil` factorization meets the spec too (`= 1`).  On WALL-FREE boundaries the shallow
/ canonical readers ALREADY meet the canonical slot-count spec — `rfl`. -/
theorem genMeetsCanonicalSlotSpec :
    (pushoutFactorizeTotal (RawTwoCellExpr.gen pushoutMonadMult)).pairs.length
        = (finestGapWidths (pushoutPathTags (composePath monadPushTPath monadPushTPath))).length
      ∧ (pushoutFactorizeIdCanonicalNil (signature := involutionMonadPushout.toModeSignature)
          crossPairRealPushoutRel (oneMode := monadPushMode)).pairs.length
        = (finestGapWidths (pushoutPathTags
            (ModalityPath.nil (graph := involutionMonadPushout.toModeGraph) monadPushMode))).length :=
  ⟨rfl, rfl⟩

/-! ## Observability -/

-- The canonical whiskerRight arm slot counts (expect `2` two-gap, `1` wire-changing) — the frame preserves the count.
#eval whiskerRightMergeTwoGapWitness.pairs.length
#eval muBlockRightFrameWitness.pairs.length

/-! ## The JAM A re-audit + the master pin -/

/-- ★★★ **The masters STAY at their walled values with the canonical whiskerRight arm shipped (`rfl`).**  The r18
canonical whiskerRight arm is additive; the master flips are gated on the JAM A per-gap descent (masters i/ii) and the
JAM B producer + wall-shift (master iii), NONE of which this arm supplies.  So
`fxAmalg_hasFullSaturatedPushoutDispatch = false`, `fxAmalg_hasGeneralPushoutDispatch = false`,
`fxAmalg_topFactorizationInductionStaysWalled = true`. -/
theorem canonicalWhiskerRightArmNoMasterFlips :
    fxAmalg_hasFullSaturatedPushoutDispatch = false
      ∧ fxAmalg_hasGeneralPushoutDispatch = false
      ∧ fxAmalg_topFactorizationInductionStaysWalled = true :=
  ⟨rfl, rfl, rfl⟩

/-- ★★★ **JAM A per-gap DESCENT stays OPEN with the canonical whiskerRight arm (`rfl`).**  The arm strengthens whisker
coverage but supplies NONE of the descent: `fxAmalg_hasSaturatedDispatchTheorem = false`. -/
theorem canonicalWhiskerRightArmJamAOpen : fxAmalg_hasSaturatedDispatchTheorem = false := rfl

/-! ## Honesty markers -/

/-- ★★★ **Honesty marker — the CANONICAL `whiskerRight` merge-layout ARM SHIPS (WP-AMALG-2 r18, B4).**  `= true`.
`pushoutFactorizeWhiskerRightMergeLayout` factors `whiskerRight oneCell (gapVcompLayout finalWall pairs)` by folding the
frame into the trailing wall (`composePath finalWall oneCell`), keeping the slot count (`n → n`) — the exact DUAL of the
shipped whiskerLeft merge arm, riding r18 leg 1 (`whiskerRight_conv_appendFinalWall`) through the cast round-trip.
Non-vacuous at the REAL pushout signature: `whiskerRightMergeTwoGapWitness` (the r7 two-gap body framed on the right,
`slotCount = 2` by `rfl`) and `muBlockRightFrameWitness` (a FRESH wire-changing `mu` composite, `slotCount = 1`).  The
wall-free arms MEET the finest slot-count spec (`genMeetsCanonicalSlotSpec`: gen `= 1 = wallCount + 1`, id-nil `= 1`).
`= true`. -/
def fxAmalg_hasCanonicalWhiskerRightArm : Bool := true

/-- ★★★ **JAM A RE-AUDIT with the canonical whiskerRight arm (STRENGTHENED coverage; per-gap descent STILL the
residual) — WP-AMALG-2 r18, B4.**  `= true` (the honest re-audit, no descent overclaim).  The r18 leg 1 + this
canonical whiskerRight arm complete the whisker fold coverage at the LAYOUT-body granularity (`n → n`, both sides), and
B1/B2 narrow the wall-shift to the extreme-ordinal folds.  But NONE of it supplies the JAM A per-gap DESCENT:
"conv-of-images ⟹ per-gap-conv" (the convex-block projection sound only for word-preserving presentations, which the
wire-creating `eta` : `t^0 ⇒ t` / `mu` : `t^2 ⇒ t` VIOLATE, changing gap WIDTHS `0 → 1` / `2 → 1` exactly where the
precondition fails) STAYS the residual: `fxAmalg_hasSaturatedDispatchTheorem` STAYS `false`
(`canonicalWhiskerRightArmJamAOpen`).  So the r18 whisker machinery does NOT supply the descent.  The masters STAY
(`canonicalWhiskerRightArmNoMasterFlips`): `fxAmalg_hasFullSaturatedPushoutDispatch` /
`fxAmalg_hasGeneralPushoutDispatch` `false`, `fxAmalg_topFactorizationInductionStaysWalled` `true`.  Named node: the
per-gap descent (the signature-specific soundness lemma), coupled to the interior-ordinal wall-shift producer (B2) and
the WalkingMonad reconstruction iso (fib-3, READ-ONLY).  #2043 does NOT close.  No descent overclaim.  `= true`. -/
def fxAmalg_canonicalReaderJamAReAuditR18 : Bool := true

/-- ★★★ **Honesty marker — the TOTAL CANONICAL reader STAYS GATED (WP-AMALG-2 r18, B4).**  `= true` (the wall is
honestly held).  The r18 canonical whisker arms (leg-1 append + this merge arm) factor a whisker of a LAYOUT body
canonically (`n → n`), but a genuinely TOTAL CANONICAL `pushoutFactorizeCanonical` over ARBITRARY cells stays GATED on
two unbuilt pieces: (1) THREADING each body's own factorization conv through the merge/append arms in the recursive
whisker cases (the r15-named "general head-prepend threading the body's own conv"); and (2) the general firing-block
PRODUCER for `s`-frames — the merge/append arms keep the body's slot count `n`, which equals the finest spec
`wallCount + 1` only for WALL-FREE (pure-`t`) frames (`genMeetsCanonicalSlotSpec`), so an `s`-carrying frame needs the
interior-ordinal producer (B2's `fxAmalg_ordinalAnchorNarrowsWallShift` named node).  The shipped SHALLOW total reader
`pushoutFactorizeTotal` (r15) remains the total EXISTENCE reader; the total CANONICAL reader is not this round.
`fxAmalg_topFactorizationInductionStaysWalled` STAYS `true`; #2043 does NOT close.  No fabricated flip.  `= true`. -/
def fxAmalg_totalCanonicalReaderStaysGated : Bool := true

end FX1Poly.Polygraph.Amalgam
