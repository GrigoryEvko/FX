import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutShiftedGapSplice

/-! # Polygraph/TwoCategory/Amalgam/PushoutCanonicalLayout — the GENERAL canonical wall/gap layout: per-gap
leading walls, a trailing wall, arbitrary wall words, and a vertically-split (upper/lower) gap payload
(WP-AMALG-2 r7, B2/B3 — the general canonical-layout type)

`PushoutShiftedGapSplice.lean` (r6) shipped `shiftedGapSourceCell` / `shiftedGapTargetCell` — a wall/gap layout
that assumes a SINGLE `s`-wall repeated before every gap and a word that STARTS with a wall.  The full-cell
factorization (`PushoutWireChangeLedger.lean`'s named node (i)) needs a strictly MORE general layout: the walls
between consecutive gaps can DIFFER (`wall₀, wall₁, …`), a wall can be a multi-letter word (`s·s`), a word can
START with a gap (a leading wall `= id`), and a word can END with a wall (the trailing wall).  This file ships that
general layout type, plus the VERTICALLY-SPLIT payload the vcomp case of the factorization induction consumes.

## The layout shape (right-nested, wall-then-gap, with a trailing wall)

A layout is a `finalWall` (the trailing wall word) together with a list of `VcompGapPair`s.  Each pair carries its
own LEADING wall (the wall word immediately to its left), a gap DOMAIN / MIDDLE / CODOMAIN 1-cell, and a
vertically-split gap payload `upper : gapDom ⇒ gapMid`, `lower : gapMid ⇒ gapCod`.  The layout boundary is the
right-nested horizontal composite

  `wall₀ · gap₀ · wall₁ · gap₁ · … · gapₙ · finalWall`

exactly the `w₀ ⊠ g₀ ⊠ w₁ ⊠ g₁ ⊠ … ⊠ wₙ` skeleton the factorization design (`PushoutWireChangeLedger.lean`) keys
to `blockDecompose`.  Because `composePath (nil) p = p` DEFINITIONALLY, a leading wall `= id` collapses (a
gap-first word), and `finalWall = id` recovers a word that ends with a gap — so this ONE type covers every
alternating wall/gap shape, refuting the r6-ledger overclaim caveat ("the shifted layout is single-`s`-wall /
wall-first only").

## What ships (each zero-axiom, STRUCTURAL on the gap list, ASCII-only)

  * **`VcompGapPair`** — a wall/gap block with a vertically-split (upper/lower) payload: `wall`, `gapDom`,
    `gapMid`, `gapCod`, `upper : gapDom ⇒ gapMid`, `lower : gapMid ⇒ gapCod`.
  * **`gapDomLayout` / `gapMidLayout` / `gapCodLayout`** — the three boundary 1-cell layouts (domain / middle /
    codomain), each the right-nested composite of the walls with the corresponding gap boundary.
  * **`gapUpperLayout` / `gapLowerLayout` / `gapVcompLayout`** — the three CELL layouts: the upper cells stacked
    (`gapDomLayout ⇒ gapMidLayout`), the lower cells stacked (`gapMidLayout ⇒ gapCodLayout`), and the per-gap
    VERTICAL composites stacked (`gapDomLayout ⇒ gapCodLayout`).  These are the domain of the r7 crux splice
    `vcompGapInterchangeSplice` (`PushoutVcompInterchangeSplice.lean`).

No `castBoundary` bookkeeping: every layout boundary is built with matching `composePath` nesting, so the walls
line up definitionally (the same absorption the r6 shifted splice found).  Over ANY signature.  This is a
DEFINITION-ONLY file (no proof obligation beyond the structural recursions).

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Amalgam

open FX1Poly.Polygraph

/-! ## The vertically-split wall/gap block -/

/-- A **wall/gap block with a vertically-split payload** — one alternating unit of a canonical layout: a LEADING
wall word `wall` (the wall immediately to the block's left, possibly `id` for a gap-first word or multi-letter for
an `s·s` wall), a gap DOMAIN `gapDom`, a gap MIDDLE `gapMid`, a gap CODOMAIN `gapCod`, and the gap's vertically
split payload — an `upper` 2-cell `gapDom ⇒ gapMid` and a `lower` 2-cell `gapMid ⇒ gapCod`.  All boundaries are
endo-1-cells at the single mode `oneMode` (matching the involution+monad pushout, `modeCount = 1`), so a list of
blocks composes horizontally.  The vertical split is what the vcomp case of the factorization induction carries:
`upper` from the top cell of a vertical composite, `lower` from the bottom, sharing the middle boundary. -/
structure VcompGapPair (signature : ModeSignature) (oneMode : signature.graph.Mode) : Type where
  /-- The block's leading wall word (`id` for a gap-first word, multi-letter for an `s·s` wall). -/
  wall : ModalityPath signature.graph oneMode oneMode
  /-- The gap's domain 1-cell (`t^a`). -/
  gapDom : ModalityPath signature.graph oneMode oneMode
  /-- The gap's middle 1-cell (`t^m`) — the shared boundary of the vertical split. -/
  gapMid : ModalityPath signature.graph oneMode oneMode
  /-- The gap's codomain 1-cell (`t^b`). -/
  gapCod : ModalityPath signature.graph oneMode oneMode
  /-- The upper gap cell (the top of a vertical composite). -/
  upper : RawTwoCellExpr signature gapDom gapMid
  /-- The lower gap cell (the bottom of a vertical composite). -/
  lower : RawTwoCellExpr signature gapMid gapCod

/-! ## The three boundary 1-cell layouts -/

/-- The **domain boundary layout** of a wall/gap block list — the right-nested horizontal composite
`wall₀ · gap₀.dom · wall₁ · gap₁.dom · … · finalWall` (a leading wall before each gap, the trailing wall at the
end).  Structural on the list; the empty list is the trailing wall itself. -/
def gapDomLayout {signature : ModeSignature} {oneMode : signature.graph.Mode}
    (finalWall : ModalityPath signature.graph oneMode oneMode) :
    List (VcompGapPair signature oneMode) → ModalityPath signature.graph oneMode oneMode
  | [] => finalWall
  | pair :: rest => composePath pair.wall (composePath pair.gapDom (gapDomLayout finalWall rest))

/-- The **middle boundary layout** — the same right-nested composite with each gap's MIDDLE 1-cell.  The shared
boundary between the upper and lower cell layouts. -/
def gapMidLayout {signature : ModeSignature} {oneMode : signature.graph.Mode}
    (finalWall : ModalityPath signature.graph oneMode oneMode) :
    List (VcompGapPair signature oneMode) → ModalityPath signature.graph oneMode oneMode
  | [] => finalWall
  | pair :: rest => composePath pair.wall (composePath pair.gapMid (gapMidLayout finalWall rest))

/-- The **codomain boundary layout** — the same right-nested composite with each gap's CODOMAIN 1-cell.  The walls
sit at the shifted absolute positions (each gap `t^a ⇒ t^b` moves the walls to its right by `b − a`). -/
def gapCodLayout {signature : ModeSignature} {oneMode : signature.graph.Mode}
    (finalWall : ModalityPath signature.graph oneMode oneMode) :
    List (VcompGapPair signature oneMode) → ModalityPath signature.graph oneMode oneMode
  | [] => finalWall
  | pair :: rest => composePath pair.wall (composePath pair.gapCod (gapCodLayout finalWall rest))

/-! ## The three cell layouts -/

/-- The **upper cell layout** — the presented wall/gap cell built from each block's UPPER payload: each inert wall
`id wall` horizontally composed with each gap's `upper`.  Its boundary is `gapDomLayout ⇒ gapMidLayout`.
Structural on the list; the empty list is the identity on the trailing wall. -/
def gapUpperLayout {signature : ModeSignature} {oneMode : signature.graph.Mode}
    (finalWall : ModalityPath signature.graph oneMode oneMode) :
    (pairs : List (VcompGapPair signature oneMode)) →
    RawTwoCellExpr signature (gapDomLayout finalWall pairs) (gapMidLayout finalWall pairs)
  | [] => RawTwoCellExpr.id finalWall
  | pair :: rest =>
      RawTwoCellExpr.hcomp (RawTwoCellExpr.id pair.wall)
        (RawTwoCellExpr.hcomp pair.upper (gapUpperLayout finalWall rest))

/-- The **lower cell layout** — the wall/gap cell built from each block's LOWER payload: each `id wall`
horizontally composed with each gap's `lower`.  Its boundary is `gapMidLayout ⇒ gapCodLayout`. -/
def gapLowerLayout {signature : ModeSignature} {oneMode : signature.graph.Mode}
    (finalWall : ModalityPath signature.graph oneMode oneMode) :
    (pairs : List (VcompGapPair signature oneMode)) →
    RawTwoCellExpr signature (gapMidLayout finalWall pairs) (gapCodLayout finalWall pairs)
  | [] => RawTwoCellExpr.id finalWall
  | pair :: rest =>
      RawTwoCellExpr.hcomp (RawTwoCellExpr.id pair.wall)
        (RawTwoCellExpr.hcomp pair.lower (gapLowerLayout finalWall rest))

/-- The **vcomp cell layout** — the wall/gap cell whose gaps are the per-gap VERTICAL composites `vcomp upper
lower`: each `id wall` horizontally composed with each gap's `vcomp pair.upper pair.lower`.  Its boundary is
`gapDomLayout ⇒ gapCodLayout` — the single canonical layout the two stacked layouts collapse to (the target of the
r7 crux splice `vcompGapInterchangeSplice`). -/
def gapVcompLayout {signature : ModeSignature} {oneMode : signature.graph.Mode}
    (finalWall : ModalityPath signature.graph oneMode oneMode) :
    (pairs : List (VcompGapPair signature oneMode)) →
    RawTwoCellExpr signature (gapDomLayout finalWall pairs) (gapCodLayout finalWall pairs)
  | [] => RawTwoCellExpr.id finalWall
  | pair :: rest =>
      RawTwoCellExpr.hcomp (RawTwoCellExpr.id pair.wall)
        (RawTwoCellExpr.hcomp (RawTwoCellExpr.vcomp pair.upper pair.lower) (gapVcompLayout finalWall rest))

/-! ## Honesty marker -/

/-- ★★ **Honesty marker — the GENERAL canonical wall/gap layout type SHIPS (WP-AMALG-2 r7, B2/B3).**  `= true`:
`VcompGapPair` carries a per-block LEADING wall (arbitrary wall word, `id` for gap-first, `s·s` for multi-letter
walls), a vertically-split gap payload (`upper` / `lower` sharing `gapMid`), and the layout functions
`gapDomLayout` / `gapMidLayout` / `gapCodLayout` (boundaries) + `gapUpperLayout` / `gapLowerLayout` /
`gapVcompLayout` (cells) build the right-nested composite `wall₀ · gap₀ · … · gapₙ · finalWall` with a trailing
wall.  This is STRICTLY more general than the r6 `shiftedGap*` layout — it captures differing inter-gap walls,
multi-letter walls, gap-first words, and wall-ending words in ONE type, refuting the r6-ledger overclaim caveat.
No `castBoundary` survives (matching `composePath` nesting).  Definition-only.  `= true`. -/
def fxAmalg_hasCanonicalGapLayout : Bool := true

end FX1Poly.Polygraph.Amalgam
