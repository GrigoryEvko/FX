import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutLayoutFactorization

/-! # Polygraph/TwoCategory/Amalgam/PushoutFinestLayout — the FINEST decomposition + the empty-gap admission, and
the empty-gap re-expression as a FREE leg (WP-AMALG-2 r9, B1/B2 — the midPath seam foundation)

r8 (`PushoutWallBlockScaffold.lean`) REFUTED the recon's wall-BLOCK alignment: the ordered `s`-block list is NOT a
dom-to-cod invariant (`unitSplitsWallCell : s·s ==> s·t·s` has domain blocks `[[s, s]]` but codomain blocks
`[[s], [s]]`).  Only the wall COUNT is conserved (`wallLetterCount_dom_eq_cod`).  r9 RE-KEYS the residual off the
refuted wall-block skeleton onto the wall-COUNT-invariant FINEST decomposition, and machine-confirms the sharpened
residual's "empty-gap admission": an `s·s` domain and an `s·t·s` codomain read as the SAME number of gap slots —
the `t`-gap merely widens from `0` to `1`.

## The finest decomposition (the wall-count-keyed shape)

The finest layout of a boundary word reads it left-to-right: every `s` is a SINGLE wall, every maximal `t`-run is a
gap.  In the `VcompGapPair` wall-first form `wall₀ · gap₀ · … · gapₙ · finalWall`, the gap widths are what vary; the
NUMBER of slots is a function of the wall count, which is conserved.  `finestGapWidths` reads the boolean tag
sequence (`true = s`-wall, `false = t`-gap) into the list of gap widths, one per slot (leading, inter-wall,
trailing).  Its length is `wallCount + 1` — the wall-count invariant made a slot count.

## The truth-probe on the r8 counterexample word (FIRST)

The r8 refuting cell's two boundaries `s·s` (`unitSplitsWallDom`) and `s·t·s` (`unitSplitsWallCod`) have finest gap
widths `[0, 0, 0]` and `[0, 1, 0]` — SAME length (3 slots = 2 walls + 1), the MIDDLE gap widening `0 → 1`.  That is
the empty-gap admission the sharpened residual demands, now machine-checked: the two boundaries key to the SAME slot
skeleton, differing only in one gap WIDTH.  The wall-block list splits (r8); the wall-count slot skeleton does not.

## What ships (each zero-axiom, STRUCTURAL / `rfl` / `decide`, ASCII-only)

  * **`finestGapWidthsAux` / `finestGapWidths`** — the finest gap-width shape of a boolean tag sequence
    (structural on the list, full-enum `Bool` head — propext-free).
  * **`pushoutPathTags`** — the boolean tag sequence of a pushout boundary path (via `pushoutPathWord` +
    `letterTag`).
  * **`unitSplitsWall_dom_finestGapWidths` / `unitSplitsWall_cod_finestGapWidths`** — the r8 counterexample's two
    boundaries read `[0, 0, 0]` / `[0, 1, 0]`.
  * **`unitSplitsWall_finestSlotCount_domCod_eq`** — the empty-gap admission: SAME slot count (both `3`), the gap
    widens in one slot only.
  * **`emptyGapPair` / `emptyGapLayout_conv_id`** — the empty-gap re-expression leg as a FREE saturated conv: a
    `nil`-gap pair with identity payload collapses to the identity on the merged wall (the `composePath nil`
    absorption made a convertibility, over ANY signature).

## What STAYS WALLED (no flip)

This ships the finest-decomposition SHAPE + the empty-gap admission + the empty-gap FREE leg — NOT the total
`pushoutFactorize` (the recon's whisker-frame `t`-run merge is a separate arc).  The re-expression is FREE only for
CANONICAL (pure-`s`-wall) layouts; the "every layout re-expresses" reading is refuted (an adversarial `s·t·s` wall
hides a real firing).  `fxAmalg_hasFullSaturatedPushoutDispatch` (`DispatchSaturated.lean`) STAYS `false`; #2043
does NOT close.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The finest gap-width shape of a tag sequence -/

/-- The **finest gap-width accumulator** — reads a boolean tag sequence (`true = s`-wall, `false = t`-gap) into the
list of gap widths, carrying the width of the currently-open gap.  On a wall (`true`) it CLOSES the current gap
(emits its accumulated width) and reopens an empty one; on a gap letter (`false`) it WIDENS the current gap; at the
end it emits the final gap.  Full-enum on the `Bool` head (propext-free); structural on the list. -/
def finestGapWidthsAux (currentGap : Nat) : List Bool → List Nat
  | [] => [currentGap]
  | true :: rest => currentGap :: finestGapWidthsAux 0 rest
  | false :: rest => finestGapWidthsAux (currentGap + 1) rest

/-- The **finest gap-width shape** of a boolean tag sequence — the list of gap widths, one per slot (a leading slot,
one inter-wall slot per wall, a trailing slot).  Its length is `wallCount + 1`: the wall-count invariant made a slot
count.  The gap widths are what vary between two words with the same wall count. -/
def finestGapWidths (tags : List Bool) : List Nat := finestGapWidthsAux 0 tags

/-- The **boolean tag sequence of a pushout boundary path** — each letter tagged `true` (component-1 `s`-wall) or
`false` (component-2 `t`-gap) through `letterTag involutionMonadSplit`, read off the boundary word by
`pushoutPathWord`. -/
def pushoutPathTags {sourceMode targetMode : Fin involutionMonadPushout.modeCount}
    (path : ModalityPath involutionMonadPushout.toModeGraph sourceMode targetMode) : List Bool :=
  (pushoutPathWord path).map (letterTag involutionMonadSplit)

/-! ## The finest shape computes (pure, on the tag sequences) -/

/-- The finest shape of the pure two-wall tag sequence `[s, s]` is three empty slots `[0, 0, 0]` — two walls, one
empty middle gap (`rfl`, pure `Bool`/`Nat`). -/
theorem finestGapWidths_wallWall : finestGapWidths [true, true] = [0, 0, 0] := rfl

/-- The finest shape of the wall-gap-wall tag sequence `[s, t, s]` is `[0, 1, 0]` — two walls, one middle gap of
width `1` (`rfl`). -/
theorem finestGapWidths_wallGapWall : finestGapWidths [true, false, true] = [0, 1, 0] := rfl

/-! ## The truth-probe on the r8 counterexample word (FIRST) -/

-- The r8 refuting cell's domain `s·s` tags — expect `[true, true]`.
#eval pushoutPathTags unitSplitsWallDom
-- The r8 refuting cell's codomain `s·t·s` tags — expect `[true, false, true]`.
#eval pushoutPathTags unitSplitsWallCod
-- The domain's finest gap widths — expect `[0, 0, 0]`.
#eval finestGapWidths (pushoutPathTags unitSplitsWallDom)
-- The codomain's finest gap widths — expect `[0, 1, 0]`.
#eval finestGapWidths (pushoutPathTags unitSplitsWallCod)

/-- The r8 refuting cell's DOMAIN `s·s` has tag sequence `[s, s]` (`decide`, mirroring
`SPrefixRefutation.lean`'s `letterTag … = false := by decide`). -/
theorem unitSplitsWall_dom_tags : pushoutPathTags unitSplitsWallDom = [true, true] := by decide

/-- The r8 refuting cell's CODOMAIN `s·t·s` has tag sequence `[s, t, s]` (`decide`). -/
theorem unitSplitsWall_cod_tags : pushoutPathTags unitSplitsWallCod = [true, false, true] := by decide

/-- ★★ **The r8 domain `s·s` reads finest gap widths `[0, 0, 0]`** — two walls, one EMPTY middle gap. -/
theorem unitSplitsWall_dom_finestGapWidths :
    finestGapWidths (pushoutPathTags unitSplitsWallDom) = [0, 0, 0] := by
  rw [unitSplitsWall_dom_tags]; exact finestGapWidths_wallWall

/-- ★★ **The r8 codomain `s·t·s` reads finest gap widths `[0, 1, 0]`** — two walls, one middle gap of width `1`.
Contrast `unitSplitsWall_dom_finestGapWidths`: SAME cell's two boundaries, SAME slot skeleton, one gap WIDTH
differs. -/
theorem unitSplitsWall_cod_finestGapWidths :
    finestGapWidths (pushoutPathTags unitSplitsWallCod) = [0, 1, 0] := by
  rw [unitSplitsWall_cod_tags]; exact finestGapWidths_wallGapWall

/-- ★★★ **THE EMPTY-GAP ADMISSION (the sharpened residual, machine-checked).**  The r8 refuting cell's domain `s·s`
and codomain `s·t·s` read the SAME number of finest gap slots (both `3` = 2 walls + 1) — so the wire-creating `eta`
(`t^0 ==> t`) that r8 showed SPLITS the wall-block list does NOT change the finest slot SKELETON: it merely widens
the middle gap from `0` to `1`.  This is the empty-gap admission the sharpened residual demanded (an `s·s` domain
and an `s·t·s` codomain read as the SAME number of gap slots), and it re-keys the vcomp seam off the refuted
wall-block skeleton onto the wall-COUNT-invariant slot skeleton.  Proved through the two finest-shape reads
(`rfl` after the `decide` tag reads). -/
theorem unitSplitsWall_finestSlotCount_domCod_eq :
    (finestGapWidths (pushoutPathTags unitSplitsWallDom)).length
      = (finestGapWidths (pushoutPathTags unitSplitsWallCod)).length := by
  rw [unitSplitsWall_dom_finestGapWidths, unitSplitsWall_cod_finestGapWidths]; rfl

/-! ## The empty-gap re-expression as a FREE leg -/

/-- An **empty-gap wall/gap block** — a `VcompGapPair` whose gap is the empty 1-cell `nil` (domain, middle, and
codomain all `nil`) with identity payloads (`id nil` upper and lower).  Its boundary contribution is just the wall
`wall` (the empty gap is absorbed by `composePath nil`).  This is the "empty `t`-gap" of the sharpened residual: the
slot exists, the gap is width `0`. -/
def emptyGapPair {signature : ModeSignature} {oneMode : signature.graph.Mode}
    (wall : ModalityPath signature.graph oneMode oneMode) : VcompGapPair signature oneMode where
  wall := wall
  gapDom := ModalityPath.nil (graph := signature.graph) oneMode
  gapMid := ModalityPath.nil (graph := signature.graph) oneMode
  gapCod := ModalityPath.nil (graph := signature.graph) oneMode
  upper := RawTwoCellExpr.id (ModalityPath.nil (graph := signature.graph) oneMode)
  lower := RawTwoCellExpr.id (ModalityPath.nil (graph := signature.graph) oneMode)

/-- ★★ **THE EMPTY-GAP RE-EXPRESSION LEG — inserting an empty gap is FREE.**  A single-block layout whose only block
is an `emptyGapPair wall` (a `nil` gap with identity payload) is saturated-convertible to the identity on the merged
wall `composePath wall finalWall`: `gapVcompLayout finalWall [emptyGapPair wall] ≈ id (wall · finalWall)`.  Free
chain — the per-gap vertical composite `vcomp (id nil) (id nil)` collapses (`vcompIdLeft`), the empty gap's `id nil`
horizontally absorbs into the trailing wall (`hcompId_conv_idComposite` at `nil`), and the leading wall's `id wall`
absorbs into the merged identity (`hcompId_conv_idComposite` at `wall`).  This is the empty-gap insertion leg of the
finest re-expression: over CANONICAL layouts, widening a slot from a `nil` gap to a real `t`-gap (or vice versa) is
mediated by FREE identity absorption — no firing is created.  Over ANY signature and base relation. -/
theorem emptyGapLayout_conv_id {signature : ModeSignature} {baseRel : CellRel signature}
    {oneMode : signature.graph.Mode}
    (wall finalWall : ModalityPath signature.graph oneMode oneMode) :
    SaturatedConvOver signature baseRel
      (gapVcompLayout finalWall [emptyGapPair wall])
      (RawTwoCellExpr.id (composePath wall finalWall)) :=
  SaturatedConvOver.trans
    (SaturatedConvOver.hcompCongrRight (RawTwoCellExpr.id wall)
      (SaturatedConvOver.trans
        (SaturatedConvOver.hcompCongrLeft
          (SaturatedConvOver.ofConv (TwoCellConv.ofStep (TwoCellStep.vcompIdLeft
            (RawTwoCellExpr.id (ModalityPath.nil (graph := signature.graph) oneMode)))))
          (RawTwoCellExpr.id finalWall))
        (hcompId_conv_idComposite (ModalityPath.nil (graph := signature.graph) oneMode) finalWall)))
    (hcompId_conv_idComposite wall finalWall)

/-! ## Honesty markers -/

/-- ★★★ **Honesty marker — the FINEST decomposition + the empty-gap admission SHIP (WP-AMALG-2 r9, B1).**  `= true`:
`finestGapWidths` reads a boundary's tag sequence into its finest gap-width shape (one width per slot, length =
`wallCount + 1`), and the r8 counterexample word probe confirms the empty-gap admission — the domain `s·s`
(`[0, 0, 0]`) and the codomain `s·t·s` (`[0, 1, 0]`) have the SAME slot count (`unitSplitsWall_finestSlotCount_domCod_eq`,
both `3`), the middle gap merely widening `0 → 1`.  This RE-KEYS the residual off the r8-refuted wall-BLOCK skeleton
(not a dom-to-cod invariant) onto the wall-COUNT-invariant slot skeleton (a dom-to-cod invariant): the wire-creating
`eta` that splits the wall-block list does NOT change the finest slot skeleton.  No marker flips.  `= true`. -/
def fxAmalg_hasFinestDecompositionAdmission : Bool := true

/-- ★★ **Honesty marker — the empty-gap re-expression is a FREE leg over CANONICAL layouts; "every layout" is
REFUTED (WP-AMALG-2 r9, B2).**  `= true`: `emptyGapLayout_conv_id` proves a `nil`-gap pair with identity payload
collapses to `id (wall · finalWall)` by FREE identity absorption (`vcompIdLeft` + `hcompId_conv_idComposite`), over
any signature — so widening a slot from an empty gap to a real gap, along a CANONICAL (pure-`s`-wall) layout, creates
NO firing.  The stronger "every `VcompGapPair` layout re-expresses through the finest" reading is FALSE: `VcompGapPair.wall`
is an arbitrary word, so an adversarial `s·t·s` "wall" hides a real `t`-firing whose re-slicing is NOT free.  The
honest re-expression is CANONICAL-restricted (pure-`s` walls, pure-`t` gaps), matching the finest producer.  This is
the B2 leg of the midPath seam, not the total `pushoutFactorize`; #2043 does NOT close.  `= true`. -/
def fxAmalg_hasEmptyGapFreeLeg : Bool := true

end FX1Poly.Polygraph.Amalgam
