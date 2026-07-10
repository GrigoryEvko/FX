import FX1Poly.Polygraph.Omega.Steiner.LinearizeFull

/-! # Polygraph/Omega/Steiner/WhiskerFix — THE ACCEPTANCE TEST (OMEGA-2.5 r1, B3)

★ **The lossy-whisker obstruction DISSOLVED at chain granularity.**  OMEGA-2's single vector satisfies
`linearize (whiskerLeft w b) = linearize b` (`linearize_whiskerLeft`): the whiskering 1-cell `w` is
FORGOTTEN, so two cells `whiskerLeft w1 b` and `whiskerLeft w2 b` built from DISTINCT whiskerings collapse
to the SAME single-vector table — the single vector cannot separate them (`Reconstruct.lean:18-21`, the
first of the two named completeness obstructions).

This file exhibits the EXACT conflated pair on a concrete faithful valuation and machine-checks that
`linearizeFull` SEPARATES it: the top-adjacent SOURCE pole of `whiskerLeft w b` is
`linearize (boundarySource (whiskerLeft w b)) = linearize (vcomp w (boundarySource b))
  = ⟨addCoordinates (linearize w) (linearize (boundarySource b))⟩`, which DEPENDS on `linearize w`.  With
`linearize w1 ≠ linearize w2` (a faithful valuation delivers this), the pole rows differ, so
`linearizeFull (whiskerLeft w1 b) ≠ linearizeFull (whiskerLeft w2 b)` while
`linearize (whiskerLeft w1 b) = linearize (whiskerLeft w2 b)`.

**This lands in the SOUND / refutation direction** — no new congruence constructor, `recInto` stays a
map-out (the SoundnessFull fold, B4).  The chain-level refuter is strictly stronger than the single-vector
one: `not_conv_of_linearizeFull_ne` (B4) refutes exactly this pair, which `not_conv_of_linearize_ne`
cannot.

## The concrete witness

  * `whiskerDemoComputad` — one object, a `Bool`-labelled generator family (two distinct generators at
    each dimension).
  * `whiskerDemoValuation` — length-1 ambient, `genValue _ label = ⟨[if label then 1 else 0]⟩` (faithful:
    the two generators separate), identities → `[0]`.
  * `whiskeringGen true` / `whiskeringGen false` — the distinct whiskering 1-cells (`linearize` = `[1]` /
    `[0]`).
  * `whiskerMainCell` — a fixed dim-2 generator `b`.
  * `whiskeredCell true` / `whiskeredCell false` — `whiskerLeft (whiskeringGen ·) b`, the conflated pair.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

open FX1Poly.Polygraph.Steiner

/-! ## The concrete faithful demo -/

/-- A one-object computad whose generators at each dimension are labelled by `Bool` — enough to carry two
DISTINCT whiskering cells. -/
def whiskerDemoComputad : OmegaComputad where
  modeCarrier := Unit
  genLabel := fun _ => Bool

/-- A faithful length-1 valuation: the `true` generator linearizes to `[1]`, the `false` generator to
`[0]`, identities to `[0]`.  Faithful in the sense that the two generators have DISTINCT tables. -/
def whiskerDemoValuation : ComputadValuation whiskerDemoComputad where
  ambientDim := 1
  modeValue := fun _ => ⟨[0]⟩
  genValue := fun _dim (label : Bool) => ⟨[cond label 1 0]⟩
  modeValueLength := fun _ => rfl
  genValueLength := fun _ _ => rfl

/-- The two DISTINCT whiskering 1-cells: `whiskeringGen true` linearizes to `[1]`, `whiskeringGen false` to
`[0]`. -/
def whiskeringGen (label : Bool) : CellExpr whiskerDemoComputad 1 :=
  CellExpr.gen label (CellExpr.ofMode ()) (CellExpr.ofMode ())

/-- The fixed dim-2 main cell `b` whiskered on the left. -/
def whiskerMainCell : CellExpr whiskerDemoComputad 2 :=
  CellExpr.gen true (CellExpr.id (CellExpr.ofMode ())) (CellExpr.id (CellExpr.ofMode ()))

/-- ★ **The conflated pair.**  `whiskeredCell true` and `whiskeredCell false` differ ONLY in the
(forgotten-by-`linearize`) whiskering cell. -/
def whiskeredCell (label : Bool) : CellExpr whiskerDemoComputad 2 :=
  CellExpr.whiskerLeft (whiskeringGen label) whiskerMainCell

/-! ## The single vector CONFLATES the pair (the OMEGA-2 lossiness) -/

/-- The two distinct whiskerings have DISTINCT single-vector tables — the valuation is faithful. -/
theorem whiskerFix_whiskering_distinct :
    linearize whiskerDemoValuation (whiskeringGen true)
      ≠ linearize whiskerDemoValuation (whiskeringGen false) := by decide

/-- ★ **THE CONFLATION.**  `linearize` maps the two whiskered cells to the SAME single vector `[1]` — the
whiskering `w` is forgotten (`linearize (whiskerLeft w b) = linearize b`).  The single vector cannot
refute this pair.  `rfl`. -/
theorem whiskerFix_linearize_conflates :
    linearize whiskerDemoValuation (whiskeredCell true)
      = linearize whiskerDemoValuation (whiskeredCell false) := rfl

/-! ## The chain table DISTINGUISHES the pair (the fix) -/

/-- ★★ **THE ACCEPTANCE TEST.**  `linearizeFull` SEPARATES the exact pair the single vector conflated:
the top-adjacent source pole records `addCoordinates (linearize w) (linearize (boundarySource b))`, which
differs (`[1]` vs `[0]`) between the two whiskerings.  Decided by the structural `DecidableEq
SteinerChainCell`.  This is the round's headline: the lossy-whisker obstruction dissolves at chain
granularity. -/
theorem whiskerFix_linearizeFull_distinguishes :
    linearizeFull whiskerDemoValuation (whiskeredCell true)
      ≠ linearizeFull whiskerDemoValuation (whiskeredCell false) := by decide

/-! ## The transparent pole witnesses (the fix is non-vacuous and readable) -/

/-- The `true`-whiskered chain table: the level-1 pole is `([1], [1])` (the whiskering shows up). -/
example : linearizeFull whiskerDemoValuation (whiskeredCell true)
    = ⟨[([1], [1]), ([0], [0])], [1]⟩ := rfl

/-- The `false`-whiskered chain table: the level-1 pole is `([0], [0])` — DISTINCT from the `true` case. -/
example : linearizeFull whiskerDemoValuation (whiskeredCell false)
    = ⟨[([0], [0]), ([0], [0])], [1]⟩ := rfl

/-- Both single-vector tables are `[1]` — the crown row conflates (the projection tie holds on both). -/
example : (linearizeFull whiskerDemoValuation (whiskeredCell true)).top
    = (linearizeFull whiskerDemoValuation (whiskeredCell false)).top := rfl

/-- The chain tables differ exactly in their POLES (the level-1 boundary the whisker touches). -/
example : (linearizeFull whiskerDemoValuation (whiskeredCell true)).poles
    ≠ (linearizeFull whiskerDemoValuation (whiskeredCell false)).poles := by decide

end FX1Poly.Polygraph.Omega
