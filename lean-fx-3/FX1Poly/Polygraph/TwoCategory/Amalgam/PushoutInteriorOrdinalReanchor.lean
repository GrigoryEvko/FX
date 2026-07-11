import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWallShiftOffset
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWhiskerRightAppend

/-! # Polygraph/TwoCategory/Amalgam/PushoutInteriorOrdinalReanchor — the PER-ORDINAL wall-shift law and the
DEFINITIONAL interior-ordinal placement, re-anchoring the r18 whole-list carrier to every interior ordinal
(WP-AMALG-2 r19, Brick B1)

r18 (`PushoutWallShiftOffset.lean`) shipped the WHOLE-LIST shift-composition law `pushoutWallShiftComposes`
(`wallOffsetDom pairs + gapCodLenSum pairs = wallOffsetCod pairs + gapDomLenSum pairs`) and the ordinal-0 /
ordinal-(n+1) extreme re-anchorings (`PushoutWallShiftReanchor.lean`).  The r18 leg-2 wall
(`fxAmalg_sFrameWallShiftStaysWalled`) fears the INTERIOR-ordinal case (ordinal ≥ 1, non-empty prefix): placing
`gapCodLayout` walls at the shifted ABSOLUTE indices off an arbitrary cell with interior walls, feared to be a
"genuinely wire-CHANGING re-nesting".  This file DISSOLVES that fear at the arithmetic layer: the placement is
DEFINITIONAL in the shipped `gapDomLayout` / `gapCodLayout`, and the shift-composition law re-anchors to EVERY
interior ordinal as a corollary of the shipped whole-list law — zero new induction.

## The per-ordinal offsets (prefix folds, `List.take` — never `List.getD`)

`wallOffsetDomAt ordinal pairs := wallOffsetDom (pairs.take ordinal)` (and the `.gapCod` / gap-sum duals) read the
offset of the ordinal-`ordinal` wall — the cumulative dom / cod length of the blocks BELOW it.  `List.take` is a
structural cons-fold (propext-free); `List.getD` stays BANNED.

## The per-ordinal shift-composition law (a corollary, zero new induction)

`wallShiftComposesAt ordinal pairs : wallOffsetDomAt ordinal pairs + cumGapCodBelow ordinal pairs
= wallOffsetCodAt ordinal pairs + cumGapDomBelow ordinal pairs` is the shipped whole-list law
`pushoutWallShiftComposes` applied to the PREFIX `pairs.take ordinal` — VERBATIM, one line.  This is the per-ordinal
paired-`Nat` law the leg-2 wall's PLACEMENT needs, and it is propext-free by inheritance (no `Int`, no `Nat.sub`).

## The placement is DEFINITIONAL (the fear dissolved)

`wallOffsetAt_gapDomLayout` specialises the shipped `gapDomLayout_length`: the ordinal-`ordinal` wall's absolute
dom index is `wallOffsetDomAt ordinal pairs` DEFINITIONALLY (it is the layout prefix length).  The dom / cod indices
differ by the cumulative gap-shift (`wallShiftComposesAt`), yet BOTH are placed by `gapDomLayout` / `gapCodLayout`
on the nose — NO surgery, NO wire-changing re-nesting.  Truth-probed FIRST on the DEEP wire-changing nest
`[muWallShiftBlock, muWallShiftBlock]` (two `mu`-firing `s`-wall blocks): the interior-ordinal (ordinal 1) wall
sits at dom offset `3` ≠ cod offset `2`, yet the placement fires by `rfl` and the per-ordinal law holds at every
ordinal.

## What STAYS WALLED (no flip)

This ships the per-ordinal ARITHMETIC + the definitional-placement witness — the honest NARROWING that the
wall-shift PLACEMENT is definitional at every interior ordinal.  It does NOT deliver the arbitrary-CELL interior-
ordinal PRODUCER the leg-2 wall's verbatim demand requires (turning an arbitrary body cell into its canonical
layout is the total canonical reader, JOB 3).  `fxAmalg_sFrameWallShiftStaysWalled` STAYS `true`; the residual is
now COLLAPSED into `fxAmalg_totalCanonicalReaderStaysGated`.  The masters STAY at their walled values; #2043 does
NOT close.  No fabricated flip.

Raw Lean 4 + Init.  `List.take` structural cons-fold; the law inherits propext-freedom from `pushoutWallShiftComposes`.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The per-ordinal wall offsets (structural prefix folds via `List.take`, never `getD`) -/

/-- The **domain-side wall offset AT an ordinal** — the cumulative dom length of the blocks strictly below ordinal
`ordinal`, `wallOffsetDom (pairs.take ordinal)`.  The absolute dom index at which the ordinal-`ordinal` wall sits.
`List.take` is a structural cons-fold (propext-free); `List.getD` stays banned. -/
def wallOffsetDomAt {signature : ModeSignature} {oneMode : signature.graph.Mode}
    (ordinal : Nat) (pairs : List (VcompGapPair signature oneMode)) : Nat :=
  wallOffsetDom (pairs.take ordinal)

/-- The **codomain-side wall offset AT an ordinal** — the cumulative cod length of the blocks below ordinal
`ordinal`, `wallOffsetCod (pairs.take ordinal)`.  The absolute cod index at which the ordinal-`ordinal` wall sits;
it differs from `wallOffsetDomAt` by the cumulative gap-shift (`wallShiftComposesAt`). -/
def wallOffsetCodAt {signature : ModeSignature} {oneMode : signature.graph.Mode}
    (ordinal : Nat) (pairs : List (VcompGapPair signature oneMode)) : Nat :=
  wallOffsetCod (pairs.take ordinal)

/-- The **cumulative gap-DOMAIN length below an ordinal** — `gapDomLenSum (pairs.take ordinal)`. -/
def cumGapDomBelow {signature : ModeSignature} {oneMode : signature.graph.Mode}
    (ordinal : Nat) (pairs : List (VcompGapPair signature oneMode)) : Nat :=
  gapDomLenSum (pairs.take ordinal)

/-- The **cumulative gap-CODOMAIN length below an ordinal** — `gapCodLenSum (pairs.take ordinal)`. -/
def cumGapCodBelow {signature : ModeSignature} {oneMode : signature.graph.Mode}
    (ordinal : Nat) (pairs : List (VcompGapPair signature oneMode)) : Nat :=
  gapCodLenSum (pairs.take ordinal)

/-! ## The per-ordinal shift-composition law (a corollary of the shipped whole-list law) -/

/-- ★★★ **THE PER-ORDINAL SHIFT-COMPOSITION LAW.**  At EVERY ordinal `ordinal`, the prefix paired-`Nat` sums agree:
`wallOffsetDomAt ordinal pairs + cumGapCodBelow ordinal pairs = wallOffsetCodAt ordinal pairs + cumGapDomBelow
ordinal pairs`.  This is the shipped whole-list law `pushoutWallShiftComposes` applied to the prefix `pairs.take
ordinal` — VERBATIM, ONE line, zero new induction.  The honest carrier of "the ordinal-`ordinal` wall moves by the
cumulative gap-shift" that never computes the (possibly negative) shift: both sides sums of `Nat`s, propext-free by
inheritance (no `Int`, no `Nat.sub`).  This is the per-ordinal paired-`Nat` law the leg-2 wall's PLACEMENT needs. -/
theorem wallShiftComposesAt {signature : ModeSignature} {oneMode : signature.graph.Mode}
    (ordinal : Nat) (pairs : List (VcompGapPair signature oneMode)) :
    wallOffsetDomAt ordinal pairs + cumGapCodBelow ordinal pairs
      = wallOffsetCodAt ordinal pairs + cumGapDomBelow ordinal pairs :=
  pushoutWallShiftComposes (pairs.take ordinal)

/-! ## The placement is DEFINITIONAL (the fear dissolved) -/

/-- ★★★ **THE INTERIOR-ORDINAL PLACEMENT IS DEFINITIONAL.**  The ordinal-`ordinal` wall's absolute domain index is
`wallOffsetDomAt ordinal pairs` on the nose: `(gapDomLayout finalWall (pairs.take ordinal)).length = wallOffsetDomAt
ordinal pairs + finalWall.length`.  A specialisation of the shipped `gapDomLayout_length` to the prefix — the
placement is a COROLLARY of the shipped `gapDomLayout` definition, NOT a wire-changing re-nesting.  The dom and cod
indices differ by the cumulative gap-shift (`wallShiftComposesAt`), yet both are placed definitionally. -/
theorem wallOffsetAt_gapDomLayout {signature : ModeSignature} {oneMode : signature.graph.Mode}
    (finalWall : ModalityPath signature.graph oneMode oneMode)
    (ordinal : Nat) (pairs : List (VcompGapPair signature oneMode)) :
    (gapDomLayout finalWall (pairs.take ordinal)).length
      = wallOffsetDomAt ordinal pairs + finalWall.length :=
  gapDomLayout_length finalWall (pairs.take ordinal)

/-- ★★ **THE INTERIOR-ORDINAL CODOMAIN PLACEMENT IS DEFINITIONAL** — the `.gapCod` dual of `wallOffsetAt_gapDomLayout`,
placing the ordinal-`ordinal` wall at the SHIFTED absolute cod index `wallOffsetCodAt ordinal pairs`. -/
theorem wallOffsetAt_gapCodLayout {signature : ModeSignature} {oneMode : signature.graph.Mode}
    (finalWall : ModalityPath signature.graph oneMode oneMode)
    (ordinal : Nat) (pairs : List (VcompGapPair signature oneMode)) :
    (gapCodLayout finalWall (pairs.take ordinal)).length
      = wallOffsetCodAt ordinal pairs + finalWall.length :=
  gapCodLayout_length finalWall (pairs.take ordinal)

/-! ## The truth-probe on the DEEP wire-changing nest (FIRST) -/

/-- A **deep wire-changing nest** — a two-block body whose BOTH blocks are the `mu`-firing wire-changing gap
`muWallShiftBlock` (`t·t ⇒ t`, an `s`-wall each), at the REAL pushout signature.  The interior ordinal (ordinal 1)
sits AFTER a wire-changing block, so its dom / cod absolute indices genuinely differ — the deepest case the leg-2
wall's PRODUCER fears. -/
def muNestBody : List (VcompGapPair involutionMonadPushout.toModeSignature monadPushMode) :=
  [muWallShiftBlock, muWallShiftBlock]

/-- ★★★ **PROBE (FIRST) — THE INTERIOR-ORDINAL WALL SITS AT A SHIFTED INDEX.**  In the deep wire-changing nest, the
ordinal-1 wall's DOMAIN offset `3` differs from its CODOMAIN offset `2` (`wallOffsetDomAt 1 muNestBody ≠
wallOffsetCodAt 1 muNestBody`, `decide`) — the interior wall genuinely sits at shifted absolute indices after the
first `mu`-firing block, exactly the case the leg-2 wall names. -/
theorem muNest_interiorOrdinalShifts :
    wallOffsetDomAt 1 muNestBody ≠ wallOffsetCodAt 1 muNestBody := by decide

/-- ★★★ **PROBE — THE PER-ORDINAL LAW FIRES AT THE INTERIOR ORDINAL.**  At the shifted interior ordinal 1 of the
deep wire-changing nest, the paired-`Nat` shift-composition law holds (`3 + 1 = 2 + 2`, both `4`) — a
`wallShiftComposesAt` instance, never computing the negative shift. -/
theorem muNest_wallShiftComposesInterior :
    wallOffsetDomAt 1 muNestBody + cumGapCodBelow 1 muNestBody
      = wallOffsetCodAt 1 muNestBody + cumGapDomBelow 1 muNestBody :=
  wallShiftComposesAt 1 muNestBody

/-- ★★★ **PROBE — THE PER-ORDINAL LAW FIRES AT THE TRAILING ORDINAL.**  At ordinal 2 (the whole nest), the law holds
(`6 + 2 = 4 + 4`, both `8`) — the two stacked `mu`-firings compose their shifts, still purely in `Nat`. -/
theorem muNest_wallShiftComposesTrailing :
    wallOffsetDomAt 2 muNestBody + cumGapCodBelow 2 muNestBody
      = wallOffsetCodAt 2 muNestBody + cumGapDomBelow 2 muNestBody :=
  wallShiftComposesAt 2 muNestBody

/-- ★★★ **PROBE — THE INTERIOR-ORDINAL PLACEMENT IS DEFINITIONAL ON THE DEEP NEST.**  With a trailing `s`-wall, the
ordinal-1 prefix `[muWallShiftBlock]`'s domain layout length equals `wallOffsetDomAt 1 muNestBody + 1` on the nose —
the shifted interior wall is placed by `gapDomLayout` DEFINITIONALLY, no re-nesting.  A `wallOffsetAt_gapDomLayout`
instance. -/
theorem muNest_placementDefinitional :
    (gapDomLayout monadPushSPath (muNestBody.take 1)).length
      = wallOffsetDomAt 1 muNestBody + monadPushSPath.length :=
  wallOffsetAt_gapDomLayout monadPushSPath 1 muNestBody

/-! ## Observability -/

-- The interior-ordinal (ordinal 1) dom vs cod offsets on the deep nest (expect `3` vs `2` — shifted).
#eval (wallOffsetDomAt 1 muNestBody, wallOffsetCodAt 1 muNestBody)
-- The trailing-ordinal (ordinal 2) dom vs cod offsets (expect `6` vs `4` — the two shifts compose).
#eval (wallOffsetDomAt 2 muNestBody, wallOffsetCodAt 2 muNestBody)

/-! ## Honesty markers -/

/-- ★★★ **Honesty marker — the PER-ORDINAL wall-shift law + the DEFINITIONAL interior-ordinal placement SHIP; the
leg-2 wall is NARROWED, NOT flipped (WP-AMALG-2 r19, B1).**  `= true`.  The per-ordinal offsets `wallOffsetDomAt` /
`wallOffsetCodAt` / `cumGapDomBelow` / `cumGapCodBelow` read the ordinal-`ordinal` wall's absolute index off the
shipped layout via the prefix `pairs.take ordinal` (structural `List.take`, never `getD`), and the per-ordinal law
`wallShiftComposesAt` (`wallOffsetDomAt + cumGapCodBelow = wallOffsetCodAt + cumGapDomBelow`) is the shipped
whole-list `pushoutWallShiftComposes` on that prefix — VERBATIM, zero new induction, propext-free by inheritance.
The placement is DEFINITIONAL (`wallOffsetAt_gapDomLayout` / `wallOffsetAt_gapCodLayout`, specialising
`gapDomLayout_length` / `gapCodLayout_length`): the interior wall's shifted dom / cod indices are placed by
`gapDomLayout` / `gapCodLayout` on the nose, NOT a wire-changing re-nesting.  Truth-probed FIRST on the DEEP
wire-changing nest `[muWallShiftBlock, muWallShiftBlock]` (`muNest_interiorOrdinalShifts`: ordinal-1 dom `3` ≠ cod
`2`; `muNest_wallShiftComposesInterior` / `_Trailing`: the law fires at ordinals 1 and 2; `muNest_placementDefinitional`:
the placement is `rfl`).

This DISSOLVES the r17/r18 "position-shift SURGERY / wire-CHANGING re-nesting" fear at the arithmetic layer, but does
NOT deliver the arbitrary-CELL interior-ordinal PRODUCER (turning an arbitrary body cell into its canonical layout is
the total canonical reader).  So `fxAmalg_sFrameWallShiftStaysWalled` STAYS `true`; the genuine residual COLLAPSES
into `fxAmalg_totalCanonicalReaderStaysGated`.  A genuine NARROWING over the r18 hedge, no fabricated flip.  `= true`. -/
def fxAmalg_interiorOrdinalPlacementDefinitional : Bool := true

/-- ★★★ **The leg-2 wall STAYS `true` — no flip at B1 (`rfl`).**  The per-ordinal law + the definitional placement
are the ARITHMETIC carrier; the verbatim demand of `fxAmalg_sFrameWallShiftStaysWalled` (the arbitrary-cell
interior-ordinal PRODUCER) is unmet, so the wall stays walled.  `fxAmalg_sFrameWallShiftStaysWalled = true`,
machine-checked. -/
theorem interiorOrdinalReanchorNoWallFlip :
    fxAmalg_sFrameWallShiftStaysWalled = true := rfl

end FX1Poly.Polygraph.Amalgam
