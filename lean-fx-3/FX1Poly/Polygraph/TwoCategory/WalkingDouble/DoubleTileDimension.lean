import FX1Poly.Polygraph.TwoCategory.WalkingDouble.DoubleTileSeed

/-! # WalkingDouble/DoubleTileDimension — the `(width, height)` SOUNDNESS + non-vacuity + markers

The soundness half of the walking-square double category.  The invariant folds `tileWidth` / `tileHeight` are
defined in `DoubleTileSeed` (they must precede the relation, because the unit laws' guards mention them); this file
ships the two SOUNDNESS theorems — tile-pasting-convertible tiles have EQUAL width AND EQUAL height — plus the
sample-tile fold smokes, the non-vacuity witnesses (a law fires; non-convertible pairs separate), and the markers.

## The soundness — pure `Nat` arithmetic

Because `DoubleTile` is UN-INDEXED (see `DoubleTileSeed`), preservation of each fold under each law is definitional
or elementary `Nat`:

* **interchange** preserves BOTH dimensions by `rfl` (`tileWidth` LHS = `tileWidth` RHS = `wa + wb`; `tileHeight`
  LHS = `tileHeight` RHS = `ha + hc`) — cleaner than `OperadTree`'s associativity;
* **horizontal associativity** preserves width by `Nat.add_assoc`, height by `rfl`;
* **vertical associativity** preserves height by `Nat.add_assoc`, width by `rfl`;
* the **guarded unit laws** close by `Nat.zero_add` / `rfl` on the adding-or-passthrough dimension and by
  `guard.symm` on the identity-square dimension (the guard is LOAD-BEARING there — `hcomp hUnit a` has height
  `1`, which equals `tileHeight a` exactly by the guard);
* the two **congruences** rewrite the children by their IHs;
* `refl` / `symm` / `trans` are the equivalence closure.

## ★ Honesty boundary — SOUNDNESS ONLY (see the markers)

Brick 1 ships the SOUNDNESS direction plus non-vacuity (a law fires; a non-convertible pair separates by width, by
height, or by BOTH).  The full DECISION (a word-problem decider) is deferred to BRICK 2 (the `m×n`-grid normal
form).  The nuance mirrors `OperadTreeArity`'s: for THIS tiny single-square walker `(width, height)` is likely
secretly COMPLETE (every well-formed `(m, n)`-tile reduces to the canonical `m×n` grid via interchange coherence —
a cyclic-3-like situation), but completeness / a decider is NOT built here.  For the GENERATOR-generic free double
category (≥ 2 square generators of the same shape) `(width, height)` is genuinely INCOMPLETE (braid-like).  Either
way this rung does NOT enter the decided ledger.

The genuinely two-dimensional separation `hcomp square square` (shape `(2,1)`) vs `vcomp square square` (shape
`(1,2)`) is the argument for the PAIR invariant: a single square-count gives BOTH value 2 and would MISS it; the
pair separates them by BOTH width and height.

## Propext-cleanliness

The soundness inductions use only `Nat.add_assoc` / `Nat.zero_add` / `rfl` / `rw` / `Eq.symm` / `Eq.trans` (all
propext-clean and audited elsewhere in this repo); the negatives route through soundness + `Nat.noConfusion`; the
unit guards are `Nat` equalities (no transport).  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph

/-! ## Sample-tile fold smokes — interchange preserves BOTH dimensions -/

/-- Smoke: the interchange law's left tile (the 2×2 grid, vertical-of-horizontals) has width 2. -/
theorem tileWidth_gridInterchangeLeft : tileWidth doubleGridInterchangeLeft = 2 := rfl

/-- Smoke: the interchange law's right tile (the 2×2 grid, horizontal-of-verticals) has width 2 — the SAME as the
left tile (interchange preserves width DEFINITIONALLY). -/
theorem tileWidth_gridInterchangeRight : tileWidth doubleGridInterchangeRight = 2 := rfl

/-- Smoke: the interchange law's left tile has height 2. -/
theorem tileHeight_gridInterchangeLeft : tileHeight doubleGridInterchangeLeft = 2 := rfl

/-- Smoke: the interchange law's right tile has height 2 — the SAME as the left tile (interchange preserves height
DEFINITIONALLY). -/
theorem tileHeight_gridInterchangeRight : tileHeight doubleGridInterchangeRight = 2 := rfl

/-- Smoke: the horizontal-associativity tiles both have width 3 (three squares pasted horizontally). -/
theorem tileWidth_hAssocLeft : tileWidth doubleHAssocLeft = 3 := rfl

/-- Smoke: the vertical-associativity tiles both have height 3 (three squares pasted vertically). -/
theorem tileHeight_vAssocLeft : tileHeight doubleVAssocLeft = 3 := rfl

/-! ## SOUNDNESS: convertible tiles have equal width AND equal height -/

/-- ★ **Soundness of the width invariant**: tile-pasting-convertible tiles have EQUAL width.  By induction on the
convertibility: interchange is `rfl`, horizontal associativity is `Nat.add_assoc`, vertical associativity is
`rfl`, the horizontal-left unit is `Nat.zero_add`, the vertical-left unit is `guard.symm` (the guard is
load-bearing — `vcomp vUnit a` has width `1`, which equals `tileWidth a` exactly by the guard), the remaining unit
laws are `rfl`, `hcompCongr` rewrites both children (width sums), `vcompCongr` reads the left child, and
`refl` / `symm` / `trans` are the equivalence closure.  This is the NO-direction of the (undecided-here) word
problem: distinct width ⟹ not convertible.  Mirrors `arityOf_congr_of_conv`. -/
theorem tileWidth_congr_of_conv
    {tile1 tile2 : DoubleTile} (conv : DoubleTileConv tile1 tile2) :
    tileWidth tile1 = tileWidth tile2 := by
  induction conv with
  | interchange _ _ _ _ => rfl
  | hAssoc a b c => exact Nat.add_assoc (tileWidth a) (tileWidth b) (tileWidth c)
  | vAssoc _ _ _ => rfl
  | hUnitLeft a _guard => exact Nat.zero_add (tileWidth a)
  | hUnitRight _ _ => rfl
  | vUnitLeft _ guard => exact guard.symm
  | vUnitRight _ _ => rfl
  | hcompCongr _ _ ihA ihB => rw [tileWidth_hcomp, tileWidth_hcomp, ihA, ihB]
  | vcompCongr _ _ ihA _ => exact ihA
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- ★ **Soundness of the height invariant**: tile-pasting-convertible tiles have EQUAL height.  The transpose of
`tileWidth_congr_of_conv`: interchange is `rfl`, vertical associativity is `Nat.add_assoc`, horizontal
associativity is `rfl`, the horizontal-left unit is `guard.symm` (the guard is load-bearing — `hcomp hUnit a` has
height `1`, which equals `tileHeight a` exactly by the guard), the vertical-left unit is `Nat.zero_add`, the
remaining unit laws are `rfl`, `vcompCongr` rewrites both children (height sums), `hcompCongr` reads the left
child, and `refl` / `symm` / `trans` are the equivalence closure. -/
theorem tileHeight_congr_of_conv
    {tile1 tile2 : DoubleTile} (conv : DoubleTileConv tile1 tile2) :
    tileHeight tile1 = tileHeight tile2 := by
  induction conv with
  | interchange _ _ _ _ => rfl
  | hAssoc _ _ _ => rfl
  | vAssoc a b c => exact Nat.add_assoc (tileHeight a) (tileHeight b) (tileHeight c)
  | hUnitLeft _ guard => exact guard.symm
  | hUnitRight _ _ => rfl
  | vUnitLeft a _guard => exact Nat.zero_add (tileHeight a)
  | vUnitRight _ _ => rfl
  | hcompCongr _ _ ihA _ => exact ihA
  | vcompCongr _ _ ihA ihB => rw [tileHeight_vcomp, tileHeight_vcomp, ihA, ihB]
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ## Non-vacuity — the invariant genuinely discriminates -/

/-- Positive witness: the 2×2 grid interchange pair is convertible (the star witness). -/
theorem doubleConv_gridInterchange :
    DoubleTileConv doubleGridInterchangeLeft doubleGridInterchangeRight :=
  doubleGridInterchangeHolds

/-- Positive witness: soundness applied to the horizontal-left-unit law — `tileWidth (hcomp hUnit square) =
tileWidth square` — via `tileWidth_congr_of_conv doubleHUnitLeftHolds` (the width IS preserved by a genuine
guarded-law firing). -/
theorem tileWidth_hUnitLeftTile_eq_square_via_soundness :
    tileWidth doubleHUnitLeftTile = tileWidth DoubleTile.square :=
  tileWidth_congr_of_conv doubleHUnitLeftHolds

/-- Positive witness: soundness applied to the vertical-left-unit law — `tileHeight (vcomp vUnit square) =
tileHeight square` — via `tileHeight_congr_of_conv doubleVUnitLeftHolds` (the height IS preserved by a genuine
guarded-law firing). -/
theorem tileHeight_vUnitLeftTile_eq_square_via_soundness :
    tileHeight doubleVUnitLeftTile = tileHeight DoubleTile.square :=
  tileHeight_congr_of_conv doubleVUnitLeftHolds

/-- Negative witness (separated by WIDTH): `square` (shape `(1,1)`) is NOT convertible to `hcomp square square`
(shape `(2,1)`) — via width soundness, since `1 = 2` is impossible (`Nat.noConfusion`). -/
theorem doubleNotConv_square_hcompSquareSquare :
    ¬ DoubleTileConv DoubleTile.square (DoubleTile.hcomp DoubleTile.square DoubleTile.square) := by
  intro conv
  have widthsEqual :
      tileWidth DoubleTile.square
        = tileWidth (DoubleTile.hcomp DoubleTile.square DoubleTile.square) :=
    tileWidth_congr_of_conv conv
  have oneEqualsTwo : (1 : Nat) = 2 := widthsEqual
  exact Nat.noConfusion oneEqualsTwo (fun zeroEqualsOne => Nat.noConfusion zeroEqualsOne)

/-- Negative witness (separated by HEIGHT): `square` (shape `(1,1)`) is NOT convertible to `vcomp square square`
(shape `(1,2)`) — via height soundness, since `1 = 2` is impossible (`Nat.noConfusion`). -/
theorem doubleNotConv_square_vcompSquareSquare :
    ¬ DoubleTileConv DoubleTile.square (DoubleTile.vcomp DoubleTile.square DoubleTile.square) := by
  intro conv
  have heightsEqual :
      tileHeight DoubleTile.square
        = tileHeight (DoubleTile.vcomp DoubleTile.square DoubleTile.square) :=
    tileHeight_congr_of_conv conv
  have oneEqualsTwo : (1 : Nat) = 2 := heightsEqual
  exact Nat.noConfusion oneEqualsTwo (fun zeroEqualsOne => Nat.noConfusion zeroEqualsOne)

/-- ★ Negative witness (the genuinely TWO-DIMENSIONAL separation): `hcomp square square` (shape `(2,1)`) is NOT
convertible to `vcomp square square` (shape `(1,2)`) — separated by width (`2 ≠ 1`) via width soundness.  A single
square-count would give BOTH tiles the value 2 and MISS this — the argument for the `(width, height)` PAIR
invariant. -/
theorem doubleNotConv_hcompSquareSquare_vcompSquareSquare :
    ¬ DoubleTileConv (DoubleTile.hcomp DoubleTile.square DoubleTile.square)
        (DoubleTile.vcomp DoubleTile.square DoubleTile.square) := by
  intro conv
  have widthsEqual :
      tileWidth (DoubleTile.hcomp DoubleTile.square DoubleTile.square)
        = tileWidth (DoubleTile.vcomp DoubleTile.square DoubleTile.square) :=
    tileWidth_congr_of_conv conv
  have twoEqualsOne : (2 : Nat) = 1 := widthsEqual
  exact Nat.noConfusion twoEqualsOne (fun oneEqualsZero => Nat.noConfusion oneEqualsZero)

/-! ## Markers -/

/-- **ESTABLISHED.**  The free strict double category on the walking square (one object, one horizontal / vertical
1-cell generator, one generating `(1,1)`-square, relations interchange + horizontal / vertical associativity +
guarded horizontal / vertical unit laws) has its SIGNATURE and a `(tileWidth, tileHeight)` tile invariant with
SOUNDNESS (`tileWidth_congr_of_conv` / `tileHeight_congr_of_conv`: convertible tiles have equal width and equal
height), zero-axiom and non-vacuously (positive `doubleGridInterchangeHolds` / `doubleHAssocHolds` /
`doubleVAssocHolds` / `doubleHUnitLeftHolds` / `doubleVUnitLeftHolds`; negatives
`doubleNotConv_square_hcompSquareSquare`, `doubleNotConv_square_vcompSquareSquare`,
`doubleNotConv_hcompSquareSquare_vcompSquareSquare`).  `= true`. -/
def fxDouble_hasSignatureAndTileInvariant : Bool := true

/-- Alias of `fxDouble_hasSignatureAndTileInvariant` naming the soundness content: brick 1 ships the double-cat
signature (fixed walking-square generators + the interchange / associativity / guarded-unit tile-pasting conv
generators), the `(width, height)` folds, and the two soundness theorems.  `= true`. -/
def fxDouble_hasSignatureAndTileSoundness : Bool := true

/-- **NOT ESTABLISHED (brick boundary).**  The double-category WORD PROBLEM is NOT decided here.  For this tiny
single-square walker `(width, height)` is likely secretly COMPLETE, but the DECISION (the `m×n`-grid normal form /
a decider) is not BUILT — that is WP-DOUBLE BRICK 2.  For the GENERATOR-generic free double category the pair is
genuinely incomplete.  Either way this rung does NOT enter the "decided" enumeration.  `= false`. -/
def fxDouble_hasWordProblemDecided : Bool := false

end FX1Poly.Polygraph
