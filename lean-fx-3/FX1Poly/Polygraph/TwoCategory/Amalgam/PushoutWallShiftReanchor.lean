import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWallShiftOffset
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWhiskerMergeIntoHead

/-! # Polygraph/TwoCategory/Amalgam/PushoutWallShiftReanchor — the ORDINAL-0 re-anchoring (definitional, empty prefix)
+ the S-frame MERGE through a WIRE-CHANGING body, and the wall-shift NARROWING (WP-AMALG-2 r18, Brick B2)

The r18 recon's headline adjudication: the wall-SHIFT the leg-2 wall fears is a corollary of the shipped ordinal
representation, NOT a surgery — because both whisker frames sit at EXTREME ordinals (head = 0, tail = n+1) where the
prefix / suffix offset sum (`wallOffsetDom` / `wallOffsetCod`, B1) is EMPTY, so the re-anchoring is DEFINITIONAL.  This
file makes that precise and probes the S-frame MERGE on a genuinely WIRE-CHANGING body.

## The ordinal-0 re-anchoring is definitional (empty prefix)

At ordinal 0 the prefix block list is `[]`, so `wallOffsetDom [] = wallOffsetCod [] = 0` by `rfl` — the head frame's
dom and cod offsets AGREE regardless of any downstream wire-changing gap.  The CONTRAST: after a wire-changing block,
the trailing wall's offsets DIFFER (`wallOffsetDom [muWallShiftBlock] = 3 ≠ 2 = wallOffsetCod [muWallShiftBlock]`) — so
the head frame does NOT shift while a downstream wall does.  The whiskerLeft MERGE (r17,
`whiskerLeft_conv_mergeFrameIntoHead`) puts the frame at ordinal 0; the whiskerRight APPEND (r18 leg 1,
`whiskerRight_conv_appendFinalWall`) puts it at the trailing ordinal where `gapCodLayoutAppendFinalWall` already places
it at the shifted position UNCONDITIONALLY.  Both extreme-ordinal folds are cast-only — the wall-shift never becomes a
cell surgery for them.

## The S-frame MERGE through a WIRE-CHANGING body (the truth-probe)

`muWireChangeMergeWitness` merges an `s`-frame into the head of a layout whose ONLY block is the `mu`-firing
wire-changing gap `muWallShiftBlock` (`t·t ⇒ t`), at the REAL pushout signature.  The merge PRESERVES the slot count
(`= 1`, `muWireChangeMergeSlotCount`, `rfl`) — the `s`-frame folds into the head wall `s·s` even though the body gap is
wire-changing, because the frame sits at ordinal 0 (offset 0 on both boundaries).  The downstream wire-change shifts
ordinal-`≥ 1` walls, never the ordinal-0 frame.

## What STAYS WALLED — NO FLIP

The ordinal anchoring NARROWS the wall-shift ("impossible position-shift surgery" → "automatic in the shipped
`gapCodLayout` representation, both frame folds touch only extreme ordinals"), but it does NOT MEET the leg-2 verbatim
demand of `fxAmalg_sFrameWallShiftStaysWalled` — whose obligation is the general PRODUCER placing walls at shifted
absolute indices OFF AN ARBITRARY CELL (a cell with INTERIOR walls, ordinal ≥ 1, where the prefix sum is NON-empty).
That interior-ordinal producer is unbuilt.  So `fxAmalg_sFrameWallShiftStaysWalled` STAYS `true`; a NARROWING marker is
added instead.  The masters STAY at their walled values; #2043 does NOT close.

Raw Lean 4 + Init.  `rfl` / `decide` / shipped-merge reuse.  Per-declaration `#assert_no_axioms` gated in the audit
twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The ordinal-0 re-anchoring is definitional -/

/-- ★★★ **THE ORDINAL-0 RE-ANCHORING IS DEFINITIONAL.**  At ordinal 0 the prefix block list is empty, so the head
frame's domain and codomain offsets both vanish: `wallOffsetDom [] = 0` and `wallOffsetCod [] = 0` — the frame
re-anchors at offset `0` on BOTH boundaries, by `rfl`, regardless of what wire-changing gaps follow.  This is why the
whiskerLeft merge (ordinal 0) is cast-only: the frame never shifts. -/
theorem ordinalZeroReanchorDefinitional {signature : ModeSignature} {oneMode : signature.graph.Mode} :
    wallOffsetDom ([] : List (VcompGapPair signature oneMode)) = 0
      ∧ wallOffsetCod ([] : List (VcompGapPair signature oneMode)) = 0 :=
  ⟨rfl, rfl⟩

/-- ★★★ **ORDINAL-0 DOES NOT SHIFT, THE TRAILING ORDINAL DOES (the extreme-ordinal contrast).**  The ordinal-0 head
offsets AGREE (both `0`), but after the wire-changing `mu` block the trailing offsets DIFFER (`3 ≠ 2`) — the head frame
is shift-free while a downstream wall moves.  This is the recon's "both frame folds touch only extreme ordinals" point:
ordinal 0 is definitionally shift-free; the wire-change lives at ordinal `≥ 1`. -/
theorem ordinalZeroShiftFreeTrailingShifts :
    wallOffsetDom ([] : List (VcompGapPair involutionMonadPushout.toModeSignature monadPushMode))
        = wallOffsetCod ([] : List (VcompGapPair involutionMonadPushout.toModeSignature monadPushMode))
      ∧ wallOffsetDom [muWallShiftBlock] ≠ wallOffsetCod [muWallShiftBlock] :=
  ⟨rfl, by decide⟩

/-! ## The S-frame MERGE through a WIRE-CHANGING body (the truth-probe) -/

/-- ★★★ **THE S-FRAME MERGE THROUGH A WIRE-CHANGING BODY.**  `whiskerLeft s` of the single-block layout whose gap is the
`mu`-firing wire-changing block `muWallShiftBlock` (`t·t ⇒ t`, at the REAL pushout signature) factors — via the shipped
CELL-level merge `pushoutFactorizeWhiskerLeftMergeLayout` — by folding the `s`-frame into the head wall.  The frame
sits at ordinal 0 (offset 0 on both boundaries), so the merge fires cast-only DESPITE the wire-changing body. -/
def muWireChangeMergeWitness :
    PushoutLayoutFactorization crossPairRealPushoutRel
      (RawTwoCellExpr.whiskerLeft monadPushSPath
        (gapVcompLayout pushoutTrivialWall [muWallShiftBlock])) :=
  pushoutFactorizeWhiskerLeftMergeLayout crossPairRealPushoutRel monadPushSPath pushoutTrivialWall
    [muWallShiftBlock]

/-- ★★★ **PROBE (the merged slot count is PRESERVED through the wire-change).**  The S-frame merge through the
wire-changing `mu` body has `pairs.length = 1` (`rfl`) — the frame folded into the head wall `s·s`, the slot count
preserved even though the body gap is wire-changing.  The ordinal-0 frame does not shift; the wire-change is downstream. -/
theorem muWireChangeMergeSlotCount : muWireChangeMergeWitness.pairs.length = 1 := rfl

/-! ## Observability -/

-- The ordinal-0 head offset (both `0`, no shift) and the trailing offsets after the `mu` block (`3` vs `2`, shifted).
#eval (wallOffsetDom ([] : List (VcompGapPair involutionMonadPushout.toModeSignature monadPushMode)),
       wallOffsetCod ([] : List (VcompGapPair involutionMonadPushout.toModeSignature monadPushMode)))
#eval (wallOffsetDom [muWallShiftBlock], wallOffsetCod [muWallShiftBlock])
-- The merged slot count through the wire-changing body (expect `1`, preserved).
#eval muWireChangeMergeWitness.pairs.length

/-! ## Honesty markers -/

/-- ★★★ **Honesty marker — the ORDINAL-0 re-anchoring is DEFINITIONAL + the S-frame merge fires through a WIRE-CHANGING
body (WP-AMALG-2 r18, B2).**  `= true`.  `ordinalZeroReanchorDefinitional` (`wallOffsetDom [] = wallOffsetCod [] = 0`,
`rfl`) makes the recon's "ordinal-0 suffices" precise: the head frame re-anchors at offset `0` on both boundaries,
regardless of downstream wire-changing gaps.  `ordinalZeroShiftFreeTrailingShifts` shows the extreme-ordinal contrast
(ordinal 0 shift-free, the trailing wall after the `mu` block shifts `3 ≠ 2`).  `muWireChangeMergeWitness` /
`muWireChangeMergeSlotCount` probe the shipped whiskerLeft MERGE on the WIRE-CHANGING `mu` body (`t·t ⇒ t`): the merge
preserves the slot count (`= 1`) — the ordinal-0 frame folds cast-only despite the wire-change.  Together with r18 leg 1
(`whiskerRight_conv_appendFinalWall`, the trailing frame at ordinal n+1 placed by `gapCodLayoutAppendFinalWall`
unconditionally), both frame folds are shown to touch only EXTREME ordinals.  `= true`. -/
def fxAmalg_ordinalZeroReanchorDefinitional : Bool := true

/-- ★★★ **Honesty marker — the ordinal anchoring NARROWS the wall-shift, but does NOT FLIP the leg-2 wall
(WP-AMALG-2 r18, B2).**  `= true` (the wall is honestly held).  The r18 ordinal-offset machinery (B1) + this file's
ordinal-0 re-anchoring RECLASSIFY the leg-2 wall-shift from the r17 "impossible cell-level position-shift surgery with
no precedent" to "AUTOMATIC in the shipped `gapCodLayout` / `gapDomLayout` representation": the two whisker frames touch
only EXTREME ordinals (head = 0, empty prefix, `rfl`; tail = n+1, placed by the shipped `gapCodLayoutAppendFinalWall`
distribution), so neither frame fold needs a position-shift SURGERY.  This is a genuine NARROWING over the r17 hedge.

But it does NOT MEET the verbatim demand of `fxAmalg_sFrameWallShiftStaysWalled`: the general PRODUCER placing
`gapCodLayout` walls at the shifted ABSOLUTE indices OFF AN ARBITRARY CELL — a cell with INTERIOR walls (ordinal ≥ 1,
where the prefix offset sum is NON-empty and the shift genuinely re-nests the layout skeleton).  That interior-ordinal
producer is the JAM B producer residual (`fxAmalg_firingBlockProducerStaysWalled`), unbuilt this round.  Per the leg-2
docstring, the flip requires meeting the demand at the shipped generality (the producer) — which the extreme-ordinal
anchoring does not supply.  So `fxAmalg_sFrameWallShiftStaysWalled` STAYS `true` (NO fabricated flip); the masters STAY
at their walled values; #2043 does NOT close.  Named node: the interior-ordinal wall-shift producer.  `= true`. -/
def fxAmalg_ordinalAnchorNarrowsWallShift : Bool := true

end FX1Poly.Polygraph.Amalgam
