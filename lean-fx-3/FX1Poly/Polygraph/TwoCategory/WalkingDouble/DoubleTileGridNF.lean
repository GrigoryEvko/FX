import FX1Poly.Polygraph.TwoCategory.WalkingDouble.DoubleTileDimension

/-! # WalkingDouble/DoubleTileGridNF — the grid normal form DECIDES the UNIT-FREE well-formed tile word problem

WP-DOUBLE brick 2.  Brick 1 (`DoubleTileSeed` + `DoubleTileDimension`) shipped the walking-square double-category
signature, the `(tileWidth, tileHeight)` folds, the tile-pasting convertibility `DoubleTileConv`, and the two
SOUNDNESS theorems (`tileWidth_congr_of_conv` / `tileHeight_congr_of_conv`: convertible tiles have equal width and
equal height — the whole NO-half of a decider, for ARBITRARY tiles).  This file adds COMPLETENESS and a TOTAL
DECIDER on the honest UNIT-FREE well-formed fragment: two unit-free well-formed tiles are `DoubleTileConv` exactly
when they have the same `(tileWidth, tileHeight)`.

## Why the well-formedness hypothesis (a `Nat` equation, never a carrier index)

The folds silently assume matching boundaries: `tileHeight (hcomp a b) = tileHeight a` reads the LEFT child and
assumes the right matches; `tileWidth (vcomp a b) = tileWidth a` likewise.  A genuine grid tile is exactly one
where every `hcomp` pastes two tiles of EQUAL height (they share a vertical boundary) and every `vcomp` pastes two
tiles of EQUAL width (they share a horizontal boundary).  We record this honestly as the inductive `IsUnitFreeGrid`
whose `hcomp` / `vcomp` constructors carry those two `Nat` equations `tileHeight a = tileHeight b` /
`tileWidth a = tileWidth b` — a `Nat`-equation side condition, NOT a `(width, height)`-indexed carrier (the carrier
stays un-indexed, so `DoubleTileConv` stays homogeneous — the `DoubleTileSeed` lesson).  The boundary-matching guard
is LOAD-BEARING at exactly the reconstruction's `hcomp` node (see `conv_toGridNF`).

## The completeness engine — a dimension-indexed canonical grid + the interchange star

`gridNF wPred hPred` is the canonical `(wPred+1) x (hPred+1)` grid — `hPred+1` stacked rows (`vcomp`), each row
`hRow wPred` a horizontal paste of `wPred+1` squares (`hcomp`).  Both indices are PREDECESSORS (the unit-free
fragment has `m, n >= 1`, so the canonical form is total and junk-free on the whole `Nat x Nat` quadrant).  The
reconstruction chain (all structural, all zero-axiom):

* `hRowMerge` : `hcomp (hRow w1) (hRow w2) ~ hRow (...)` — horizontal associativity peels the leading square (the
  base `hRow 0 = square` is `refl`; NO unit law is discharged — this is the unit-free brick);
* `vMerge` : `vcomp (gridNF w na) (gridNF w nb) ~ gridNF w (...)` — vertical associativity peels the top row;
* `hMerge` : `hcomp (gridNF w1 n) (gridNF w2 n) ~ gridNF (...) n` — THE STAR: induction on the height, each step is
  `DoubleTileConv.interchange` (used `.symm`) peeling one row, then `hRowMerge` on the peeled rows — the algebraic
  content of a double category;
* `conv_toGridNF` : every unit-free well-formed tile is convertible to the canonical grid of its `(width, height)`.
  At the `hcomp` node the guard `tileHeight a = tileHeight b` makes both IH grids share a height, so `hMerge`
  (which demands equal heights) applies — this is the load-bearing boundary condition threaded as a `Nat` equation.

Then `doubleTileConv_of_sameShape_of_wf` routes two same-shape tiles through the shared canonical grid, and
`decideDoubleTileConv` compares the `(tileWidth, tileHeight)` pairs via `Nat.decEq` (soundness rejects distinct
shapes, completeness accepts equal ones).

## Honesty boundary — the UNIT-FREE fragment (the marker), the unit-bearing extension (the named wall)

This is the FULL decision of the unit-free well-formed fragment — the genuinely two-dimensional content is entirely
present (`hMerge`/interchange, `vMerge`, `hRowMerge`, the reconstruction, the biconditional, the decider), and all
of the seed's star samples are covered: `doubleGridInterchange{Left,Right}` (shape `(2,2)`) decide `true`;
`hcomp square square` (shape `(2,1)`) vs `vcomp square square` (shape `(1,2)`) decides `false`.  The residual (WP-DOUBLE
brick 3) is the UNIT-BEARING well-formed fragment: `hUnit`/`vUnit` in the well-formedness predicate, the degenerate
zero-height / zero-width strips, and discharging the seed's guarded unit laws — pure degenerate-strip bookkeeping,
no new two-dimensional idea, hence a clean honest wall (`fxDouble_hasUnitBearingGridDecided := false`).  The seed's
`fxDouble_hasWordProblemDecided` flag is NOT flipped by this brick (it names the full unit-bearing decision).

Raw Lean 4 + Init; the well-formedness / convertibility are inductive `Prop`s; the canonical form and merges are
plain `Nat` structural recursions (never `WellFounded.fix`); the decider is `Nat.decEq` on the pair (no
`decidable_of_iff` / `propext` route).  Free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`,
`omega`; per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## The unit-free well-formedness predicate -/

/-- ★ The **unit-free well-formed grid** predicate.  A tile is a genuine unit-free grid when it is built only from
`square` (never `hUnit` / `vUnit`), and every horizontal paste `hcomp a b` shares a vertical boundary
(`tileHeight a = tileHeight b`) while every vertical paste `vcomp a b` shares a horizontal boundary
(`tileWidth a = tileWidth b`).  The boundary conditions are carried as plain `Nat` equations on the constructors —
NOT as a `(width, height)` carrier index — exactly the seed's guard discipline, so the underlying `DoubleTile`
stays un-indexed and `DoubleTileConv` stays homogeneous. -/
inductive IsUnitFreeGrid : DoubleTile → Prop where
  /-- The generating square is a `(1,1)` unit-free grid. -/
  | square : IsUnitFreeGrid DoubleTile.square
  /-- A horizontal paste of two unit-free grids of EQUAL height is a unit-free grid. -/
  | hcomp (a b : DoubleTile) :
      IsUnitFreeGrid a → IsUnitFreeGrid b → tileHeight a = tileHeight b →
      IsUnitFreeGrid (DoubleTile.hcomp a b)
  /-- A vertical paste of two unit-free grids of EQUAL width is a unit-free grid. -/
  | vcomp (a b : DoubleTile) :
      IsUnitFreeGrid a → IsUnitFreeGrid b → tileWidth a = tileWidth b →
      IsUnitFreeGrid (DoubleTile.vcomp a b)

/-! ## The canonical horizontal row and the canonical grid (predecessor-indexed) -/

/-- ★ The **canonical horizontal row** `hRow wPred` — a left-nested horizontal paste of `wPred + 1` squares.  Plain
`Nat` structural recursion (`hRow (wPred+1) = hcomp square (hRow wPred)`), so its defining equations reduce
DEFINITIONALLY.  The base `hRow 0 = square` is the single square — NO horizontal unit is used (this is the unit-free
brick). -/
def hRow : Nat → DoubleTile
  | 0 => DoubleTile.square
  | wPred + 1 => DoubleTile.hcomp DoubleTile.square (hRow wPred)

/-- ★ The **canonical grid** `gridNF wPred hPred` — `hPred + 1` copies of the row `hRow wPred` stacked vertically
(`gridNF wPred (hPred+1) = vcomp (hRow wPred) (gridNF wPred hPred)`).  Plain `Nat` structural recursion on the
height index, junk-free on the whole `Nat x Nat` quadrant because the unit-free fragment has width and height at
least one.  Shape `(wPred+1, hPred+1)`. -/
def gridNF (wPred : Nat) : Nat → DoubleTile
  | 0 => hRow wPred
  | hPred + 1 => DoubleTile.vcomp (hRow wPred) (gridNF wPred hPred)

/-- ★ The **direct-count canonical grid** `canonicalGrid width height` — the canonical `width x height` grid indexed
by the DIRECT counts (junk `square` off the positive quadrant, never reached under `IsUnitFreeGrid`).  Wrapping
`gridNF` by direct counts is what lets COMPLETENESS route two same-shape tiles through the shared
`canonicalGrid (tileWidth t) (tileHeight t)` and rewrite by their `(width, height)` equalities. -/
def canonicalGrid : Nat → Nat → DoubleTile
  | 0, _ => DoubleTile.square
  | _ + 1, 0 => DoubleTile.square
  | wPred + 1, hPred + 1 => gridNF wPred hPred

/-! ## Shape smokes — the canonical grid has the intended `(width, height)` -/

/-- Smoke: the canonical row `hRow wPred` has width `wPred + 1`. -/
theorem tileWidth_hRow (wPred : Nat) : tileWidth (hRow wPred) = wPred + 1 := by
  induction wPred with
  | zero => rfl
  | succ wPredPrev ih =>
      show tileWidth (DoubleTile.hcomp DoubleTile.square (hRow wPredPrev)) = (wPredPrev + 1) + 1
      rw [tileWidth_hcomp, tileWidth_square, ih, Nat.add_comm 1 (wPredPrev + 1)]

/-- Smoke: the canonical row `hRow wPred` has height 1 (a single row of squares). -/
theorem tileHeight_hRow (wPred : Nat) : tileHeight (hRow wPred) = 1 := by
  cases wPred with
  | zero => rfl
  | succ _ => rfl

/-- Smoke: the canonical grid `gridNF wPred hPred` has width `wPred + 1`. -/
theorem tileWidth_gridNF (wPred hPred : Nat) : tileWidth (gridNF wPred hPred) = wPred + 1 := by
  cases hPred with
  | zero => exact tileWidth_hRow wPred
  | succ hPredPrev =>
      show tileWidth (DoubleTile.vcomp (hRow wPred) (gridNF wPred hPredPrev)) = wPred + 1
      rw [tileWidth_vcomp, tileWidth_hRow]

/-- Smoke: the canonical grid `gridNF wPred hPred` has height `hPred + 1`. -/
theorem tileHeight_gridNF (wPred hPred : Nat) : tileHeight (gridNF wPred hPred) = hPred + 1 := by
  induction hPred with
  | zero => exact tileHeight_hRow wPred
  | succ hPredPrev ih =>
      show tileHeight (DoubleTile.vcomp (hRow wPred) (gridNF wPred hPredPrev)) = (hPredPrev + 1) + 1
      rw [tileHeight_vcomp, tileHeight_hRow, ih, Nat.add_comm 1 (hPredPrev + 1)]

/-! ## Positivity — a unit-free grid has width and height at least one -/

/-- Every unit-free grid has a POSITIVE width — `tileWidth t = wPred + 1` for some predecessor `wPred`.  By
induction: `square` is `0 + 1`; `hcomp` adds (the left predecessor plus the right width, off by one via
`Nat.add_right_comm`); `vcomp` reads the left width.  The predecessor is exactly the `gridNF` width index the
reconstruction needs. -/
theorem isUnitFreeGrid_width_succ {t : DoubleTile} (h : IsUnitFreeGrid t) :
    ∃ wPred, tileWidth t = wPred + 1 := by
  induction h with
  | square => exact ⟨0, rfl⟩
  | hcomp _a b _ha _hb _guard iha _ihb =>
      obtain ⟨wap, pa⟩ := iha
      refine ⟨wap + tileWidth b, ?_⟩
      rw [tileWidth_hcomp, pa, Nat.add_right_comm wap 1 (tileWidth b)]
  | vcomp _a _b _ha _hb _guard iha _ihb => exact iha

/-- Every unit-free grid has a POSITIVE height — `tileHeight t = hPred + 1` for some predecessor `hPred`.  The
transpose of `isUnitFreeGrid_width_succ`: `hcomp` reads the left height, `vcomp` adds. -/
theorem isUnitFreeGrid_height_succ {t : DoubleTile} (h : IsUnitFreeGrid t) :
    ∃ hPred, tileHeight t = hPred + 1 := by
  induction h with
  | square => exact ⟨0, rfl⟩
  | hcomp _a _b _ha _hb _guard iha _ihb => exact iha
  | vcomp _a b _ha _hb _guard iha _ihb =>
      obtain ⟨hap, pa⟩ := iha
      refine ⟨hap + tileHeight b, ?_⟩
      rw [tileHeight_vcomp, pa, Nat.add_right_comm hap 1 (tileHeight b)]

/-! ## The merges — the reconstruction's algebra -/

/-- The **horizontal row merge**: `hcomp (hRow w1p) (hRow w2p)` is convertible to the single wider row.  Induction
on `w1p`: the base peels to `refl`; each step fires horizontal associativity (`hAssoc`) to expose the leading square
and recurses via `hcompCongr`.  NO unit law is used — the base `hRow 0 = square` closes definitionally. -/
theorem hRowMerge (w1p w2p : Nat) :
    DoubleTileConv (DoubleTile.hcomp (hRow w1p) (hRow w2p)) (hRow (w2p + w1p + 1)) := by
  induction w1p with
  | zero => exact DoubleTileConv.refl _
  | succ w1pPrev ih =>
      exact DoubleTileConv.trans
        (DoubleTileConv.hAssoc DoubleTile.square (hRow w1pPrev) (hRow w2p))
        (DoubleTileConv.hcompCongr (DoubleTileConv.refl DoubleTile.square) ih)

/-- ★ The **horizontal grid merge — THE STAR**: two grids of equal height paste horizontally into one wider grid,
`hcomp (gridNF w1p n) (gridNF w2p n) ~ gridNF (w2p + w1p + 1) n`.  Induction on the height `n`; the base is
`hRowMerge`; each step applies the INTERCHANGE law (`DoubleTileConv.interchange`, used `.symm`) to swap a
horizontal-of-verticals into a vertical-of-horizontals, peeling the top row, then reconciles the peeled rows by
`hRowMerge` and the rest by the inductive hypothesis (`vcompCongr`).  This is the genuinely two-dimensional
coherence — the whole algebraic point of a double category. -/
theorem hMerge (w1p w2p n : Nat) :
    DoubleTileConv (DoubleTile.hcomp (gridNF w1p n) (gridNF w2p n)) (gridNF (w2p + w1p + 1) n) := by
  induction n with
  | zero => exact hRowMerge w1p w2p
  | succ nPrev ih =>
      exact DoubleTileConv.trans
        (DoubleTileConv.symm
          (DoubleTileConv.interchange (hRow w1p) (hRow w2p) (gridNF w1p nPrev) (gridNF w2p nPrev)))
        (DoubleTileConv.vcompCongr (hRowMerge w1p w2p) ih)

/-- The **vertical grid merge**: two grids of equal width stack vertically into one taller grid,
`vcomp (gridNF wp na) (gridNF wp nb) ~ gridNF wp (nb + na + 1)`.  Induction on `na`: the base is `refl`; each step
fires vertical associativity (`vAssoc`) to expose the top row and recurses via `vcompCongr`. -/
theorem vMerge (wp na nb : Nat) :
    DoubleTileConv (DoubleTile.vcomp (gridNF wp na) (gridNF wp nb)) (gridNF wp (nb + na + 1)) := by
  induction na with
  | zero => exact DoubleTileConv.refl _
  | succ naPrev ih =>
      exact DoubleTileConv.trans
        (DoubleTileConv.vAssoc (hRow wp) (gridNF wp naPrev) (gridNF wp nb))
        (DoubleTileConv.vcompCongr (DoubleTileConv.refl (hRow wp)) ih)

/-! ## The direct-count merges — bridging to `canonicalGrid` -/

/-- The horizontal merge at DIRECT-count canonical grids: `hcomp` of two equal-height grids is the wider grid.  The
`canonicalGrid (·+1) (·+1)` calls reduce to `gridNF`; the width index reassociates to `hMerge`'s form. -/
theorem canonicalHMerge (w1p w2p np : Nat) :
    DoubleTileConv
      (DoubleTile.hcomp (canonicalGrid (w1p + 1) (np + 1)) (canonicalGrid (w2p + 1) (np + 1)))
      (canonicalGrid ((w1p + 1) + (w2p + 1)) (np + 1)) := by
  show DoubleTileConv (DoubleTile.hcomp (gridNF w1p np) (gridNF w2p np)) (gridNF ((w1p + 1) + w2p) np)
  rw [Nat.add_right_comm w1p 1 w2p, Nat.add_comm w1p w2p]
  exact hMerge w1p w2p np

/-- The vertical merge at DIRECT-count canonical grids: `vcomp` of two equal-width grids is the taller grid. -/
theorem canonicalVMerge (wp na nb : Nat) :
    DoubleTileConv
      (DoubleTile.vcomp (canonicalGrid (wp + 1) (na + 1)) (canonicalGrid (wp + 1) (nb + 1)))
      (canonicalGrid (wp + 1) ((na + 1) + (nb + 1))) := by
  show DoubleTileConv (DoubleTile.vcomp (gridNF wp na) (gridNF wp nb)) (gridNF wp ((na + 1) + nb))
  rw [Nat.add_right_comm na 1 nb, Nat.add_comm na nb]
  exact vMerge wp na nb

/-! ## COMPLETENESS: every unit-free grid reduces to its canonical grid -/

/-- ★ **The reconstruction**: every unit-free well-formed tile is convertible to the canonical grid of its
`(tileWidth, tileHeight)`.  By induction on the well-formedness derivation.  The `square` node is the `(1,1)` grid
(`refl`).  At the `hcomp` node the guard `tileHeight a = tileHeight b` is LOAD-BEARING: it makes both inductive
grids share a height, so the star merge `canonicalHMerge` (which demands equal heights) applies.  At the `vcomp`
node the guard `tileWidth a = tileWidth b` plays the transposed role via `canonicalVMerge`.  This is the
YES-direction of the decision. -/
theorem conv_toGridNF {t : DoubleTile} (h : IsUnitFreeGrid t) :
    DoubleTileConv t (canonicalGrid (tileWidth t) (tileHeight t)) := by
  induction h with
  | square => exact DoubleTileConv.refl _
  | hcomp a b ha hb guard iha ihb =>
      obtain ⟨wap, pa⟩ := isUnitFreeGrid_width_succ ha
      obtain ⟨wbp, pb⟩ := isUnitFreeGrid_width_succ hb
      obtain ⟨hap, pah⟩ := isUnitFreeGrid_height_succ ha
      have pbh : tileHeight b = hap + 1 := by rw [← guard]; exact pah
      have ihaGrid : DoubleTileConv a (canonicalGrid (wap + 1) (hap + 1)) := by
        rw [← pa, ← pah]; exact iha
      have ihbGrid : DoubleTileConv b (canonicalGrid (wbp + 1) (hap + 1)) := by
        rw [← pb, ← pbh]; exact ihb
      rw [tileWidth_hcomp, tileHeight_hcomp, pa, pb, pah]
      exact DoubleTileConv.trans (DoubleTileConv.hcompCongr ihaGrid ihbGrid)
        (canonicalHMerge wap wbp hap)
  | vcomp a b ha hb guard iha ihb =>
      obtain ⟨wap, pa⟩ := isUnitFreeGrid_width_succ ha
      obtain ⟨hap, pah⟩ := isUnitFreeGrid_height_succ ha
      obtain ⟨hbp, pbh⟩ := isUnitFreeGrid_height_succ hb
      have pbw : tileWidth b = wap + 1 := by rw [← guard]; exact pa
      have ihaGrid : DoubleTileConv a (canonicalGrid (wap + 1) (hap + 1)) := by
        rw [← pa, ← pah]; exact iha
      have ihbGrid : DoubleTileConv b (canonicalGrid (wap + 1) (hbp + 1)) := by
        rw [← pbw, ← pbh]; exact ihb
      rw [tileWidth_vcomp, tileHeight_vcomp, pa, pah, pbh]
      exact DoubleTileConv.trans (DoubleTileConv.vcompCongr ihaGrid ihbGrid)
        (canonicalVMerge wap hap hbp)

/-- ★ **Completeness on the unit-free fragment**: two unit-free well-formed tiles of EQUAL width and EQUAL height are
convertible.  Route both through the shared canonical grid:
`t1 ~ canonicalGrid (width t1) (height t1) = canonicalGrid (width t2) (height t2) ~ t2` (rewriting by the two
equalities).  This is the completeness half of the decision. -/
theorem doubleTileConv_of_sameShape_of_wf
    {t1 t2 : DoubleTile} (h1 : IsUnitFreeGrid t1) (h2 : IsUnitFreeGrid t2)
    (widthsEqual : tileWidth t1 = tileWidth t2)
    (heightsEqual : tileHeight t1 = tileHeight t2) :
    DoubleTileConv t1 t2 := by
  have reductionOne : DoubleTileConv t1 (canonicalGrid (tileWidth t2) (tileHeight t2)) := by
    rw [← widthsEqual, ← heightsEqual]; exact conv_toGridNF h1
  exact DoubleTileConv.trans reductionOne (DoubleTileConv.symm (conv_toGridNF h2))

/-! ## The TOTAL decision on the unit-free fragment -/

/-- ★ **Decide walking-square tile convertibility on the unit-free fragment** — TOTAL.  Compare the two tiles'
`(tileWidth, tileHeight)` pairs with `Nat.decEq`: equal pair ⟹ `isTrue` (completeness
`doubleTileConv_of_sameShape_of_wf`); distinct width ⟹ `isFalse` (width soundness
`tileWidth_congr_of_conv` would force them equal); distinct height ⟹ `isFalse` (height soundness).  Both branches
discharged — the unit-free word problem is genuinely decided.  The decider carries the unit-free well-formedness
witnesses (`h1`, `h2`) because completeness needs them; the NO branches ignore them (soundness needs none). -/
def decideDoubleTileConv {t1 t2 : DoubleTile}
    (h1 : IsUnitFreeGrid t1) (h2 : IsUnitFreeGrid t2) :
    Decidable (DoubleTileConv t1 t2) :=
  match Nat.decEq (tileWidth t1) (tileWidth t2) with
  | isFalse widthsDiffer =>
      isFalse (fun conv => widthsDiffer (tileWidth_congr_of_conv conv))
  | isTrue widthsEqual =>
      match Nat.decEq (tileHeight t1) (tileHeight t2) with
      | isFalse heightsDiffer =>
          isFalse (fun conv => heightsDiffer (tileHeight_congr_of_conv conv))
      | isTrue heightsEqual =>
          isTrue (doubleTileConv_of_sameShape_of_wf h1 h2 widthsEqual heightsEqual)

/-! ## Unit-free well-formedness witnesses for the samples -/

/-- The generating square is a unit-free grid. -/
def wfSquare : IsUnitFreeGrid DoubleTile.square := IsUnitFreeGrid.square

/-- `hcomp square square` (shape `(2,1)`) is a unit-free grid — both squares have equal height. -/
def wfHcompSquareSquare :
    IsUnitFreeGrid (DoubleTile.hcomp DoubleTile.square DoubleTile.square) :=
  IsUnitFreeGrid.hcomp DoubleTile.square DoubleTile.square
    IsUnitFreeGrid.square IsUnitFreeGrid.square rfl

/-- `vcomp square square` (shape `(1,2)`) is a unit-free grid — both squares have equal width. -/
def wfVcompSquareSquare :
    IsUnitFreeGrid (DoubleTile.vcomp DoubleTile.square DoubleTile.square) :=
  IsUnitFreeGrid.vcomp DoubleTile.square DoubleTile.square
    IsUnitFreeGrid.square IsUnitFreeGrid.square rfl

/-- The interchange law's left tile (the `2x2` grid, vertical-of-horizontals) is a unit-free grid. -/
def wfGridInterchangeLeft : IsUnitFreeGrid doubleGridInterchangeLeft :=
  IsUnitFreeGrid.vcomp
    (DoubleTile.hcomp DoubleTile.square DoubleTile.square)
    (DoubleTile.hcomp DoubleTile.square DoubleTile.square)
    wfHcompSquareSquare wfHcompSquareSquare rfl

/-- The interchange law's right tile (the `2x2` grid, horizontal-of-verticals) is a unit-free grid. -/
def wfGridInterchangeRight : IsUnitFreeGrid doubleGridInterchangeRight :=
  IsUnitFreeGrid.hcomp
    (DoubleTile.vcomp DoubleTile.square DoubleTile.square)
    (DoubleTile.vcomp DoubleTile.square DoubleTile.square)
    wfVcompSquareSquare wfVcompSquareSquare rfl

/-! ## Non-vacuity — completeness fires, the decider genuinely discriminates -/

/-- ★ Positive witness by COMPLETENESS: the two `2x2` interchange tiles (both shape `(2,2)`) are convertible — proved
by the NEW completeness machinery `doubleTileConv_of_sameShape_of_wf` (both shapes `rfl`-equal), INDEPENDENTLY of the
seed's `interchange` generator.  This exercises the whole reconstruction. -/
theorem doubleConv_gridInterchange_viaCompleteness :
    DoubleTileConv doubleGridInterchangeLeft doubleGridInterchangeRight :=
  doubleTileConv_of_sameShape_of_wf wfGridInterchangeLeft wfGridInterchangeRight rfl rfl

/-- Smoke: `hcomp square square` reconstructs to its canonical `2x1` grid (`conv_toGridNF` on a concrete tile). -/
theorem conv_hcompSquareSquare_toGrid :
    DoubleTileConv (DoubleTile.hcomp DoubleTile.square DoubleTile.square) (canonicalGrid 2 1) :=
  conv_toGridNF wfHcompSquareSquare

/-- ★ Non-vacuity by the DECIDER (positive): the decider ACCEPTS the convertible `2x2` interchange pair. -/
theorem doubleDecide_true_on_gridInterchange :
    @decide (DoubleTileConv doubleGridInterchangeLeft doubleGridInterchangeRight)
      (decideDoubleTileConv wfGridInterchangeLeft wfGridInterchangeRight) = true := rfl

/-- ★ Non-vacuity by the DECIDER (negative, the genuinely TWO-DIMENSIONAL separation): the decider REJECTS
`hcomp square square` (shape `(2,1)`) vs `vcomp square square` (shape `(1,2)`) — separated by width.  A single
square-count would miss this; the `(width, height)` pair catches it. -/
theorem doubleDecide_false_on_hcomp_vcomp :
    @decide (DoubleTileConv (DoubleTile.hcomp DoubleTile.square DoubleTile.square)
        (DoubleTile.vcomp DoubleTile.square DoubleTile.square))
      (decideDoubleTileConv wfHcompSquareSquare wfVcompSquareSquare) = false := rfl

/-- ★ Non-vacuity by the DECIDER (negative, width-only): the decider REJECTS `square` (shape `(1,1)`) vs
`hcomp square square` (shape `(2,1)`). -/
theorem doubleDecide_false_on_square_hcomp :
    @decide (DoubleTileConv DoubleTile.square
        (DoubleTile.hcomp DoubleTile.square DoubleTile.square))
      (decideDoubleTileConv wfSquare wfHcompSquareSquare) = false := rfl

/-! ## Markers -/

/-- **ESTABLISHED.**  The walking-square double category's tile word problem is DECIDED on the honest UNIT-FREE
well-formed fragment, zero-axiom and non-vacuously.  The `(tileWidth, tileHeight)` invariant is SOUND (the seed's
`tileWidth_congr_of_conv` / `tileHeight_congr_of_conv`, for ALL tiles) and COMPLETE on unit-free well-formed tiles
(`doubleTileConv_of_sameShape_of_wf`, via the canonical-grid reconstruction `conv_toGridNF` whose star step is the
interchange-driven `hMerge`), and the total `decideDoubleTileConv` accepts the convertible `2x2` interchange pair
(`doubleDecide_true_on_gridInterchange`) and rejects the shape-separated pairs
(`doubleDecide_false_on_hcomp_vcomp`, `doubleDecide_false_on_square_hcomp`).  The genuinely two-dimensional content
(interchange, both associativities, the reconstruction) is entirely present; no unit law is discharged.  `= true`. -/
def fxDouble_hasUnitFreeGridDecision : Bool := true

/-- **NOT ESTABLISHED (the named wall — WP-DOUBLE brick 3).**  The UNIT-BEARING well-formed fragment is NOT decided
here.  Extending to `hUnit` / `vUnit` in `IsUnitFreeGrid` requires: the degenerate zero-height / zero-width strips
(`wCol` from `vUnit`, `hUnit`-columns), a column merge, discharging the seed's guarded unit laws (all firings are at
width / height one, so the guards hold, but they must be threaded), and handling that the `(0,0)` shape is
uninhabited.  This is pure degenerate-strip bookkeeping — no new two-dimensional idea — hence a clean honest wall.
This brick does NOT flip the seed's `fxDouble_hasWordProblemDecided`, which names the full unit-bearing decision.
`= false`. -/
def fxDouble_hasUnitBearingGridDecided : Bool := false

end FX1Poly.Polygraph
