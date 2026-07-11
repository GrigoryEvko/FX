import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutCanonicalFiringBlockReader
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWallFreeCellInvert

/-! # Polygraph/TwoCategory/Amalgam/PushoutWallShiftOffset — the per-ordinal WALL-OFFSET function and the
propext-safe Nat SHIFT-COMPOSITION law (WP-AMALG-2 r18, Brick B1)

The r17 leg-2 wall names the wire-changing wall-SHIFT: when a gap `t^a ⇒ t^b` sits in a layout, "each firing shifts
the downstream walls to its right by `b − a`."  Over `Nat` the difference `b − a` may underflow (a `mu` gap `t·t ⇒ t`
has `b − a = −1`), so `Int` (which leaks `propext` per the memory kit) and `Nat.sub` (underflow truncation) are BOTH
forbidden.  This file authors the honest carrier: the per-ordinal wall OFFSET (a structural cons-fold over the layout
blocks, never `List.getD`) and the shift-composition law in the paired-`Nat` form
`domOffset + Σ len(gapCod) = codOffset + Σ len(gapDom)` — both sides sums of `Nat`s, proved by `Nat.add_add_add_comm`
/ `Nat.add_right_comm`, NEVER computing `b − a`.

## The offset (read off the shipped `gapDomLayout` / `gapCodLayout`)

`wallOffsetDom pairs` is the domain-side letter offset of the ordinal immediately AFTER the block list `pairs`:
`Σ_i (len wall_i + len gapDom_i)`.  `wallOffsetCod` is the codomain-side offset `Σ_i (len wall_i + len gapCod_i)`.
Both are structural cons-folds; `gapDomLayout_length` / `gapCodLayout_length` connect them to the shipped layout 1-cell
lengths (`(gapDomLayout finalWall pairs).length = wallOffsetDom pairs + finalWall.length`), so the offset is a COROLLARY
of the shipped `gapDomLayout` definition — not a new obligation.

## The shift-composition law (the wall moves by `b − a`, without ever computing it)

`pushoutWallShiftComposes` proves `wallOffsetDom pairs + gapCodLenSum pairs = wallOffsetCod pairs + gapDomLenSum pairs`.
This is the honest carrier of "the wall moves by `gapCod − gapDom`": rearranging it says `wallOffsetCod − wallOffsetDom =
Σ(len gapCod − len gapDom)`, but the equation itself stays entirely in `Nat` (both sides sums), so it survives the
`mu`-firing SHRINKING case (`t·t ⇒ t`, `b − a = −1`) where `Int` / `Nat.sub` would be needed.  The proof is the shape of
`pushoutPathWallCount_composePath` — `Nat.add_add_add_comm` + `Nat.add_right_comm`, propext-free.

## The truth-probe on a concrete WIRE-CHANGING path (FIRST)

`muWallShiftBlock` is an `s`-wall block whose gap is the `mu` firing `t·t ⇒ t` (`gapDom = t·t`, `gapCod = t`) — a
genuinely wire-changing gap at the REAL pushout signature.  Its trailing-ordinal offset shifts from `3` (domain) to `2`
(codomain) — the wall moved LEFT by one (`b − a = 1 − 2 = −1`), machine-checked by `rfl` (`muWallShiftBlock_domOffset` /
`muWallShiftBlock_codOffset`) — yet the shift-composition law fires (`muWallShiftComposes`, both `4`), and the whole
layout `s·(t·t)·s ⇒ s·t·s` shrinks length `4 → 3` (`muWallShiftBlock_domLayoutLength` / `_codLayoutLength`) while the
wall COUNT stays `2`.

## What STAYS WALLED (no flip)

This ships the offset arithmetic — the honest carrier of the wall-shift, NOT the cell-level position-shift SURGERY the
leg-2 wall demands.  `fxAmalg_sFrameWallShiftStaysWalled` STAYS `true`; the masters STAY at their walled values;
#2043 does NOT close.

Raw Lean 4 + Init.  STRUCTURAL cons-folds; `Nat.add_add_add_comm` / `Nat.add_right_comm` (propext-free).
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The per-ordinal wall offset (structural cons-fold, never `getD`) -/

/-- The **domain-side wall offset** of the ordinal immediately after a block list — the cumulative letter length of
each block's leading wall plus its gap DOMAIN, `Σ_i (len wall_i + len gapDom_i)`.  Structural cons-recursion over the
list (never `List.getD`). -/
def wallOffsetDom {signature : ModeSignature} {oneMode : signature.graph.Mode} :
    List (VcompGapPair signature oneMode) → Nat
  | [] => 0
  | pair :: rest => pair.wall.length + pair.gapDom.length + wallOffsetDom rest

/-- The **codomain-side wall offset** — the cumulative wall plus gap CODOMAIN lengths, `Σ_i (len wall_i + len
gapCod_i)`.  The walls sit at these shifted absolute positions on the codomain side (each gap `t^a ⇒ t^b` moves the
downstream walls by `b − a`). -/
def wallOffsetCod {signature : ModeSignature} {oneMode : signature.graph.Mode} :
    List (VcompGapPair signature oneMode) → Nat
  | [] => 0
  | pair :: rest => pair.wall.length + pair.gapCod.length + wallOffsetCod rest

/-- The cumulative gap-DOMAIN letter length of a block list, `Σ_i len gapDom_i`. -/
def gapDomLenSum {signature : ModeSignature} {oneMode : signature.graph.Mode} :
    List (VcompGapPair signature oneMode) → Nat
  | [] => 0
  | pair :: rest => pair.gapDom.length + gapDomLenSum rest

/-- The cumulative gap-CODOMAIN letter length of a block list, `Σ_i len gapCod_i`. -/
def gapCodLenSum {signature : ModeSignature} {oneMode : signature.graph.Mode} :
    List (VcompGapPair signature oneMode) → Nat
  | [] => 0
  | pair :: rest => pair.gapCod.length + gapCodLenSum rest

/-! ## The offset reads off the shipped layout length -/

/-- ★★ **THE DOMAIN OFFSET IS THE LAYOUT PREFIX LENGTH.**  `(gapDomLayout finalWall pairs).length = wallOffsetDom pairs
+ finalWall.length` — the offset of the trailing wall (`finalWall`) is exactly the cumulative dom-side length of the
blocks before it.  Structural on `pairs` via the length homomorphism `ModalityPath.length_composePath`; the offset is a
COROLLARY of the shipped `gapDomLayout`, not a new fold. -/
theorem gapDomLayout_length {signature : ModeSignature} {oneMode : signature.graph.Mode}
    (finalWall : ModalityPath signature.graph oneMode oneMode) :
    (pairs : List (VcompGapPair signature oneMode)) →
    (gapDomLayout finalWall pairs).length = wallOffsetDom pairs + finalWall.length
  | [] => (Nat.zero_add finalWall.length).symm
  | pair :: rest => by
      show (composePath pair.wall (composePath pair.gapDom (gapDomLayout finalWall rest))).length
          = pair.wall.length + pair.gapDom.length + wallOffsetDom rest + finalWall.length
      rw [ModalityPath.length_composePath, ModalityPath.length_composePath,
          gapDomLayout_length finalWall rest, Nat.add_assoc, Nat.add_assoc]

/-- ★★ **THE CODOMAIN OFFSET IS THE LAYOUT PREFIX LENGTH** — the `.gapCod` dual of `gapDomLayout_length`. -/
theorem gapCodLayout_length {signature : ModeSignature} {oneMode : signature.graph.Mode}
    (finalWall : ModalityPath signature.graph oneMode oneMode) :
    (pairs : List (VcompGapPair signature oneMode)) →
    (gapCodLayout finalWall pairs).length = wallOffsetCod pairs + finalWall.length
  | [] => (Nat.zero_add finalWall.length).symm
  | pair :: rest => by
      show (composePath pair.wall (composePath pair.gapCod (gapCodLayout finalWall rest))).length
          = pair.wall.length + pair.gapCod.length + wallOffsetCod rest + finalWall.length
      rw [ModalityPath.length_composePath, ModalityPath.length_composePath,
          gapCodLayout_length finalWall rest, Nat.add_assoc, Nat.add_assoc]

/-! ## The shift-composition law (paired-Nat form, propext-safe) -/

/-- The pure-`Nat` block-step rearrangement of the shift-composition law: given the tail identity `wd + gc = wc + gd`,
the head letters `w` (wall), `d` (gapDom), `c` (gapCod) rearrange so the whole-list paired sums agree.  `Nat.add_add_add_comm`
collects the tail sums, the tail identity substitutes, and `Nat.add_right_comm` swaps `d`/`c` in the head — all
propext-free. -/
theorem shiftPairing (w d c wd wc gd gc : Nat) (h : wd + gc = wc + gd) :
    (w + d + wd) + (c + gc) = (w + c + wc) + (d + gd) := by
  rw [Nat.add_add_add_comm (w + d) wd c gc, h, Nat.add_add_add_comm (w + c) wc d gd,
      Nat.add_right_comm w d c]

/-- ★★★ **THE SHIFT-COMPOSITION LAW (paired-`Nat` form).**  For any block list,
`wallOffsetDom pairs + gapCodLenSum pairs = wallOffsetCod pairs + gapDomLenSum pairs` — the honest carrier of "each gap
`t^a ⇒ t^b` moves the downstream walls by `b − a`" that never computes `b − a`: both sides are sums of `Nat`s, so the
`mu`-firing SHRINKING case (`gapCod < gapDom`) is fine where `Int` (`propext`-leaking) / `Nat.sub` (underflow) would be
needed.  Structural on `pairs`: `[]` is `rfl`; the cons step is `shiftPairing` on the tail identity (the IH).  The shape
of `pushoutPathWallCount_composePath` — `Nat.add_add_add_comm` + `Nat.add_right_comm`, propext-free. -/
theorem pushoutWallShiftComposes {signature : ModeSignature} {oneMode : signature.graph.Mode} :
    (pairs : List (VcompGapPair signature oneMode)) →
    wallOffsetDom pairs + gapCodLenSum pairs = wallOffsetCod pairs + gapDomLenSum pairs
  | [] => rfl
  | pair :: rest =>
      shiftPairing pair.wall.length pair.gapDom.length pair.gapCod.length
        (wallOffsetDom rest) (wallOffsetCod rest) (gapDomLenSum rest) (gapCodLenSum rest)
        (pushoutWallShiftComposes rest)

/-! ## The truth-probe on a concrete WIRE-CHANGING path (FIRST) -/

/-- A **wire-changing wall block** at the REAL pushout signature — an `s`-wall whose gap is the `mu` firing
`t·t ⇒ t` (`gapDom = t·t`, `gapCod = t`), idle (`id t`) on the lower cell.  The genuinely wire-changing block whose
downstream wall SHIFTS (`b − a = 1 − 2 = −1`). -/
def muWallShiftBlock : VcompGapPair involutionMonadPushout.toModeSignature monadPushMode where
  wall := monadPushSPath
  gapDom := composePath monadPushTPath monadPushTPath
  gapMid := monadPushTPath
  gapCod := monadPushTPath
  upper := RawTwoCellExpr.gen pushoutMonadMult
  lower := RawTwoCellExpr.id (signature := involutionMonadPushout.toModeSignature) monadPushTPath

/-- ★★★ **PROBE (the domain-side wall offset).**  `wallOffsetDom [muWallShiftBlock] = 3` (`s·t·t` = 1 + 2) — the
trailing wall's domain offset, machine-checked `rfl`. -/
theorem muWallShiftBlock_domOffset : wallOffsetDom [muWallShiftBlock] = 3 := rfl

/-- ★★★ **PROBE (the codomain-side wall offset — SHIFTED LEFT).**  `wallOffsetCod [muWallShiftBlock] = 2` (`s·t` = 1 +
1) — the SAME wall's codomain offset is `2`, ONE less than its domain offset `3`: the `mu`-firing shrank the gap
`t·t ⇒ t`, so the downstream wall moved LEFT by `b − a = 1 − 2 = −1`.  `rfl`. -/
theorem muWallShiftBlock_codOffset : wallOffsetCod [muWallShiftBlock] = 2 := rfl

/-- ★★★ **PROBE (the shift-composition law FIRES on the `mu` firing).**  `wallOffsetDom + gapCodLenSum = wallOffsetCod +
gapDomLenSum` on `[muWallShiftBlock]` — `3 + 1 = 2 + 2` (both `4`) — the paired-`Nat` law holds for the SHRINKING
wire-changing gap, never computing the negative `b − a`.  A `pushoutWallShiftComposes` instance. -/
theorem muWallShiftComposes :
    wallOffsetDom [muWallShiftBlock] + gapCodLenSum [muWallShiftBlock]
      = wallOffsetCod [muWallShiftBlock] + gapDomLenSum [muWallShiftBlock] :=
  pushoutWallShiftComposes [muWallShiftBlock]

/-- ★★ **PROBE (the whole layout shrinks, wall count conserved).**  With a trailing `s`-wall, the `mu` block's domain
layout `s·(t·t)·s` has length `4` — machine-checked `rfl` via `gapDomLayout_length`-style computation. -/
theorem muWallShiftBlock_domLayoutLength :
    (gapDomLayout monadPushSPath [muWallShiftBlock]).length = 4 := rfl

/-- ★★ **PROBE (the codomain layout).**  The `mu` block's codomain layout `s·t·s` has length `3` — the whole layout
shrank `4 → 3` (the trailing wall moved LEFT), yet BOTH boundaries carry TWO `s`-walls (the count is conserved,
`wallLetterCount_dom_eq_cod`). -/
theorem muWallShiftBlock_codLayoutLength :
    (gapCodLayout monadPushSPath [muWallShiftBlock]).length = 3 := rfl

/-! ## Observability -/

-- The `mu` block's domain wall offset (expect `3`) and codomain wall offset (expect `2`) — the wall shifts LEFT by 1.
#eval wallOffsetDom [muWallShiftBlock]
#eval wallOffsetCod [muWallShiftBlock]
-- The whole layout lengths with a trailing `s`-wall (expect `4` dom, `3` cod) — the layout shrinks, wall count stays 2.
#eval (gapDomLayout monadPushSPath [muWallShiftBlock]).length
#eval (gapCodLayout monadPushSPath [muWallShiftBlock]).length

/-! ## Honesty marker -/

/-- ★★★ **Honesty marker — the wall-OFFSET function + the propext-safe SHIFT-COMPOSITION law SHIP (WP-AMALG-2 r18,
B1).**  `= true`.  `wallOffsetDom` / `wallOffsetCod` (structural cons-folds, never `getD`) read the per-ordinal wall
offset off the shipped layout (`gapDomLayout_length` / `gapCodLayout_length`: `(gapDomLayout finalWall pairs).length =
wallOffsetDom pairs + finalWall.length`, via `ModalityPath.length_composePath`).  The shift-composition law
`pushoutWallShiftComposes` (`wallOffsetDom + gapCodLenSum = wallOffsetCod + gapDomLenSum`) is the propext-safe paired-`Nat`
carrier of "the wall moves by `b − a`" that NEVER computes the (possibly negative) `b − a`: no `Int` (`propext`-leaking),
no `Nat.sub` (underflow) — only `Nat.add_add_add_comm` + `Nat.add_right_comm`.  Truth-probed FIRST on the concrete
WIRE-CHANGING `mu` firing `t·t ⇒ t` (`muWallShiftBlock`): the wall shifts LEFT `3 → 2` (`muWallShiftBlock_domOffset` /
`_codOffset`), the paired law fires (`muWallShiftComposes`, both `4`), and the layout shrinks `4 → 3` with the wall
count conserved.

This is the honest ARITHMETIC carrier of the wall-shift, NOT the cell-level position-shift SURGERY the leg-2 wall
demands.  `fxAmalg_sFrameWallShiftStaysWalled` STAYS `true`; the masters STAY at their walled values; #2043 does NOT
close.  No fabricated flip.  `= true`. -/
def fxAmalg_hasWallShiftOffset : Bool := true

end FX1Poly.Polygraph.Amalgam
