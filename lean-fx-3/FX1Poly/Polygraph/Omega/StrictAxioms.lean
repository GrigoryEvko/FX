import FX1Poly.Polygraph.Omega.Congruence

/-! # Polygraph/Omega/StrictAxioms — the strict omega-category laws as ONE dimension-generic relation family
(OMEGA-1 r1, B3)

The dim-2 free-2-cell rewriting (`FreeTwoCell/Model.lean`'s `TwoCellStep`) orients the strict-2-category laws —
vertical associativity, the two units, whisker-vs-identity, whisker-vs-vcomp functoriality, and the interchange
/ Godement exchange — as a fixed list of generating 3-cells.  This file lifts that list to ONE
dimension-generic relation `StrictAxiomRel : CellRelOver computad`.  The free strict congruence at every
dimension is then `SaturatedConvOver (StrictAxiomRel union presentationRows)` — the T1.axioms deliverable:
`ofFull` (the shipped dim-2 completed convertibility) is reproduced generically by firing these rows through
`SaturatedConvOver.ofRelation`.

Whiskering / vertical composites reuse the five carrier generators; the whisker boundary and the interchange
exchange are computed with the total structural boundaries `boundarySource` / `boundaryTarget` (Carrier).

## The rows (each a strict-omega law, oriented as an unordered equation)

  * `vcompAssoc`            — `(a . b) . c ~ a . (b . c)`.
  * `vcompUnitLeft`         — `id_(src a) . a ~ a`.
  * `vcompUnitRight`        — `a . id_(tgt a) ~ a`.
  * `whiskerLeftUnit`       — `w <| id_c ~ id_(w . c)`.
  * `whiskerRightUnit`      — `id_c |> w ~ id_(c . w)`.
  * `whiskerLeftFunctorial` — `w <| (b . c) ~ (w <| b) . (w <| c)`.
  * `whiskerRightFunctorial`— `(a . b) |> w ~ (a |> w) . (b |> w)`.
  * `interchange`           — the Godement middle-four exchange (two whisker orders of a horizontal composite
    agree).

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! ## The strict-axiom relation family -/

/-- ★ The **strict omega-category laws as ONE dimension-generic relation family** — associativity, the two
units, the two whisker-unit laws, the two whisker-functoriality laws, and the Godement interchange, each an
unordered generating equation at every dimension.  `SaturatedConvOver StrictAxiomRel` is the free strict
congruence; the shipped dim-2 `ofFull` (completed free-strict-2-category convertibility) is reproduced by firing
these rows through `ofRelation`. -/
inductive StrictAxiomRel (computad : OmegaComputad) :
    {dim : Nat} → CellExpr computad dim → CellExpr computad dim → Prop where
  /-- Vertical associativity `(a . b) . c ~ a . (b . c)`. -/
  | vcompAssoc {dim : Nat} (cellA cellB cellC : CellExpr computad (dim + 1)) :
      StrictAxiomRel computad
        (CellExpr.vcomp (CellExpr.vcomp cellA cellB) cellC)
        (CellExpr.vcomp cellA (CellExpr.vcomp cellB cellC))
  /-- Left unit `id_(src a) . a ~ a`. -/
  | vcompUnitLeft {dim : Nat} (cellA : CellExpr computad (dim + 1)) :
      StrictAxiomRel computad
        (CellExpr.vcomp (CellExpr.id (boundarySource cellA)) cellA) cellA
  /-- Right unit `a . id_(tgt a) ~ a`. -/
  | vcompUnitRight {dim : Nat} (cellA : CellExpr computad (dim + 1)) :
      StrictAxiomRel computad
        (CellExpr.vcomp cellA (CellExpr.id (boundaryTarget cellA))) cellA
  /-- Left whisker of an identity is an identity `w <| id_c ~ id_(w . c)`. -/
  | whiskerLeftUnit {dim : Nat} (whiskeringCell innerCell : CellExpr computad (dim + 1)) :
      StrictAxiomRel computad
        (CellExpr.whiskerLeft whiskeringCell (CellExpr.id innerCell))
        (CellExpr.id (CellExpr.vcomp whiskeringCell innerCell))
  /-- Right whisker of an identity is an identity `id_c |> w ~ id_(c . w)`. -/
  | whiskerRightUnit {dim : Nat} (innerCell whiskeringCell : CellExpr computad (dim + 1)) :
      StrictAxiomRel computad
        (CellExpr.whiskerRight (CellExpr.id innerCell) whiskeringCell)
        (CellExpr.id (CellExpr.vcomp innerCell whiskeringCell))
  /-- Left whisker distributes over vertical composition `w <| (b . c) ~ (w <| b) . (w <| c)`. -/
  | whiskerLeftFunctorial {dim : Nat} (whiskeringCell : CellExpr computad (dim + 1))
      (cellBeta cellGamma : CellExpr computad (dim + 2)) :
      StrictAxiomRel computad
        (CellExpr.whiskerLeft whiskeringCell (CellExpr.vcomp cellBeta cellGamma))
        (CellExpr.vcomp (CellExpr.whiskerLeft whiskeringCell cellBeta)
          (CellExpr.whiskerLeft whiskeringCell cellGamma))
  /-- Right whisker distributes over vertical composition `(a . b) |> w ~ (a |> w) . (b |> w)`. -/
  | whiskerRightFunctorial {dim : Nat} (cellAlpha cellBeta : CellExpr computad (dim + 2))
      (whiskeringCell : CellExpr computad (dim + 1)) :
      StrictAxiomRel computad
        (CellExpr.whiskerRight (CellExpr.vcomp cellAlpha cellBeta) whiskeringCell)
        (CellExpr.vcomp (CellExpr.whiskerRight cellAlpha whiskeringCell)
          (CellExpr.whiskerRight cellBeta whiskeringCell))
  /-- The **Godement interchange** — the two whisker orders of a horizontal composite of `cellAlpha` and
  `cellBeta` agree: `(alpha |> src beta) . (tgt alpha <| beta) ~ (src alpha <| beta) . (alpha |> tgt beta)`.
  Cast-free: both sides share the boundary computed by the total structural boundaries. -/
  | interchange {dim : Nat} (cellAlpha cellBeta : CellExpr computad (dim + 2)) :
      StrictAxiomRel computad
        (CellExpr.vcomp (CellExpr.whiskerRight cellAlpha (boundarySource cellBeta))
          (CellExpr.whiskerLeft (boundaryTarget cellAlpha) cellBeta))
        (CellExpr.vcomp (CellExpr.whiskerLeft (boundarySource cellAlpha) cellBeta)
          (CellExpr.whiskerRight cellAlpha (boundaryTarget cellBeta)))

/-! ## The free strict congruence and the presentation union -/

/-- The **disjoint union** of two cell relations — a row of either.  The strict laws unite with presentation
rows through this. -/
def unionCellRel (computad : OmegaComputad) (relLeft relRight : CellRelOver computad) : CellRelOver computad :=
  fun cellAlpha cellBeta => relLeft cellAlpha cellBeta ∨ relRight cellAlpha cellBeta

/-- ★ The **free strict congruence over a presentation** at every dimension — the saturated congruence over the
strict laws united with the presentation's generating rows (T1.axioms).  For the empty presentation this is the
free strict omega-category congruence; adding rows presents any strict omega-theory. -/
def freeStrictCongruence (computad : OmegaComputad) (presentationRows : CellRelOver computad) :
    CellRelOver computad :=
  fun cellAlpha cellBeta =>
    SaturatedConvOver computad
      (unionCellRel computad (StrictAxiomRel computad) presentationRows) cellAlpha cellBeta

/-- The empty presentation — no generating rows beyond the strict laws.  `freeStrictCongruence emptyPresentation`
is the free strict omega-category congruence. -/
def emptyPresentation (computad : OmegaComputad) : CellRelOver computad :=
  fun _ _ => False

end FX1Poly.Polygraph.Omega
