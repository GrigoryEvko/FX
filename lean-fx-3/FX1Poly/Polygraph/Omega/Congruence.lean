import FX1Poly.Polygraph.Omega.Carrier

/-! # Polygraph/Omega/Congruence — the dimension-generic saturated cell congruence (OMEGA-1 r1, B2)

The dim-2 `SaturatedConvOver` (`Amalgam/SaturatedOver.lean`) closes an explicit law relation over the free
2-cell carrier into a genuine congruence by FOUR one-hole context constructors (`vcompCongrLeft` /
`vcompCongrRight` / `whiskerLeftCongr` / `whiskerRightCongr`) plus `ofRelation` (a fixed-boundary row firing)
plus `refl` / `symm` / `trans`, and its sole eliminator `recInto` folds into any absorbing congruence
(`IsSaturatedCongruence`).  This file lifts that shape to EVERY dimension at once.

## The n=2 falsifiability check (the prime directive)

Specialised to `dim = 2` the four one-hole constructors here REPRODUCE the four shipped ones on the nose:

  * `vcompCongrLeft`   — left factor varies, right fixed, wrapped in `vcomp`.
  * `vcompCongrRight`  — right factor varies, left fixed, wrapped in `vcomp`.
  * `whiskerLeftCongr` — the whiskered cell varies under a fixed left whisker.
  * `whiskerRightCongr`— the whiskered cell varies under a fixed right whisker.

If the n=2 instance needed a DIFFERENT constructor set, a parallel structure would have crept in.  It does not.

## No `ofFull` generically (the honest divergence from dim-2)

The shipped dim-2 congruence has a NINTH constructor `ofFull` embedding `TwoCellConvFull` (the completed
free-strict-2-category convertibility: structural laws + interchange).  There is no `TwoCellConvFull` at a
generic dimension, so this file does NOT carry `ofFull`.  Instead the structural laws (associativity, units,
interchange) are supplied as a DATA relation `StrictAxiomRel` (`Omega/StrictAxioms.lean`) and fired through
`ofRelation`; the free strict congruence at dimension `n` is `SaturatedConvOver (StrictAxiomRel union
presentationRows)`.  The r2 n=2 bridge proof must exhibit the shipped `ofFull` as derivable from
`ofRelation` at `StrictAxiomRel 2`; so the bridge is `{8 generic ctors + StrictAxiomRel rows} <-> {9 shipped
ctors}`, not a ctor-for-ctor `9 <-> 9`.

## What ships here (each piece zero-axiom, structural, ASCII-only)

  * **`CellRelOver`** — a heterogeneous relation on same-dimension cells (the law-relation shape).
  * **`SaturatedConvOver`** — the generic saturated congruence (8 constructors).
  * **`IsSaturatedCongruence`** — the absorbing-congruence structure (the eliminator's hypothesis).
  * **`SaturatedConvOver.recInto`** — the sole eliminator, the invariant fold into any absorbing congruence.
  * **`DecidableSaturatedConvOver`** — the per-relation decision interface.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! ## The law-relation shape -/

/-- A **cell relation** over a computad — a heterogeneous relation on same-dimension cells.  The shape a
doctrine's law relation takes at every dimension at once; `SaturatedConvOver` closes it into a congruence. -/
def CellRelOver (computad : OmegaComputad) : Type :=
  {dim : Nat} → CellExpr computad dim → CellExpr computad dim → Prop

/-! ## The dimension-generic saturated congruence -/

/-- ★ The **dimension-generic saturated cell congruence** — the uniform shape of every per-presentation
saturated convertibility, lifted to all dimensions.  An explicit law relation `baseRel` (each row a generating
equation via `ofRelation`) closed under the four one-hole congruences (`vcompCongrLeft` / `vcompCongrRight` at
`vcomp`, `whiskerLeftCongr` / `whiskerRightCongr` at the two whiskerings) and `refl` / `symm` / `trans` into a
genuine congruence.  At `dim = 2` the four one-hole constructors reproduce the shipped dim-2 congruence's four
on the nose. -/
inductive SaturatedConvOver (computad : OmegaComputad) (baseRel : CellRelOver computad) :
    {dim : Nat} → CellExpr computad dim → CellExpr computad dim → Prop where
  /-- Embed a law row of `baseRel` as a generating equation (fixed boundary; context is supplied by the
  one-hole congruences). -/
  | ofRelation {dim : Nat} {cellAlpha cellBeta : CellExpr computad dim} :
      baseRel cellAlpha cellBeta → SaturatedConvOver computad baseRel cellAlpha cellBeta
  /-- Congruence in the LEFT factor of a vertical composite. -/
  | vcompCongrLeft {dim : Nat} {cellAlpha cellAlpha' : CellExpr computad (dim + 1)}
      (cellBeta : CellExpr computad (dim + 1)) :
      SaturatedConvOver computad baseRel cellAlpha cellAlpha' →
      SaturatedConvOver computad baseRel (CellExpr.vcomp cellAlpha cellBeta)
        (CellExpr.vcomp cellAlpha' cellBeta)
  /-- Congruence in the RIGHT factor of a vertical composite. -/
  | vcompCongrRight {dim : Nat} (cellAlpha : CellExpr computad (dim + 1))
      {cellBeta cellBeta' : CellExpr computad (dim + 1)} :
      SaturatedConvOver computad baseRel cellBeta cellBeta' →
      SaturatedConvOver computad baseRel (CellExpr.vcomp cellAlpha cellBeta)
        (CellExpr.vcomp cellAlpha cellBeta')
  /-- Congruence under a left whiskering (a law fires whiskered on the left by a lower cell). -/
  | whiskerLeftCongr {dim : Nat} (whiskeringCell : CellExpr computad (dim + 1))
      {cellBeta cellBeta' : CellExpr computad (dim + 2)} :
      SaturatedConvOver computad baseRel cellBeta cellBeta' →
      SaturatedConvOver computad baseRel (CellExpr.whiskerLeft whiskeringCell cellBeta)
        (CellExpr.whiskerLeft whiskeringCell cellBeta')
  /-- Congruence under a right whiskering. -/
  | whiskerRightCongr {dim : Nat} {cellAlpha cellAlpha' : CellExpr computad (dim + 2)}
      (whiskeringCell : CellExpr computad (dim + 1)) :
      SaturatedConvOver computad baseRel cellAlpha cellAlpha' →
      SaturatedConvOver computad baseRel (CellExpr.whiskerRight cellAlpha whiskeringCell)
        (CellExpr.whiskerRight cellAlpha' whiskeringCell)
  /-- Reflexivity. -/
  | refl {dim : Nat} (cell : CellExpr computad dim) :
      SaturatedConvOver computad baseRel cell cell
  /-- Symmetry. -/
  | symm {dim : Nat} {cellAlpha cellBeta : CellExpr computad dim} :
      SaturatedConvOver computad baseRel cellAlpha cellBeta →
      SaturatedConvOver computad baseRel cellBeta cellAlpha
  /-- Transitivity. -/
  | trans {dim : Nat} {cellAlpha cellBeta cellGamma : CellExpr computad dim} :
      SaturatedConvOver computad baseRel cellAlpha cellBeta →
      SaturatedConvOver computad baseRel cellBeta cellGamma →
      SaturatedConvOver computad baseRel cellAlpha cellGamma

/-! ## The universal property — the eliminator into any absorbing congruence -/

/-- A target relation `targetRel` **absorbs** the generic saturated congruence over `baseRel` — closed under the
law rows, the four one-hole congruences, and `refl` / `symm` / `trans`.  The universal property's hypothesis:
any such `targetRel` receives the fold `recInto` from `SaturatedConvOver`.  Fields are uniform Pi (no mixed
implicit/explicit before the arrow). -/
structure IsSaturatedCongruence (computad : OmegaComputad)
    (baseRel targetRel : CellRelOver computad) : Prop where
  /-- Absorb a law row. -/
  ofRelation : {dim : Nat} → {cellAlpha : CellExpr computad dim} → {cellBeta : CellExpr computad dim} →
    baseRel cellAlpha cellBeta → targetRel cellAlpha cellBeta
  /-- Congruence in the left factor of a vertical composite. -/
  vcompCongrLeft : {dim : Nat} → {cellAlpha : CellExpr computad (dim + 1)} →
    {cellAlpha' : CellExpr computad (dim + 1)} → {cellBeta : CellExpr computad (dim + 1)} →
    targetRel cellAlpha cellAlpha' →
    targetRel (CellExpr.vcomp cellAlpha cellBeta) (CellExpr.vcomp cellAlpha' cellBeta)
  /-- Congruence in the right factor of a vertical composite. -/
  vcompCongrRight : {dim : Nat} → {cellAlpha : CellExpr computad (dim + 1)} →
    {cellBeta : CellExpr computad (dim + 1)} → {cellBeta' : CellExpr computad (dim + 1)} →
    targetRel cellBeta cellBeta' →
    targetRel (CellExpr.vcomp cellAlpha cellBeta) (CellExpr.vcomp cellAlpha cellBeta')
  /-- Congruence under a left whiskering. -/
  whiskerLeftCongr : {dim : Nat} → {whiskeringCell : CellExpr computad (dim + 1)} →
    {cellBeta : CellExpr computad (dim + 2)} → {cellBeta' : CellExpr computad (dim + 2)} →
    targetRel cellBeta cellBeta' →
    targetRel (CellExpr.whiskerLeft whiskeringCell cellBeta)
      (CellExpr.whiskerLeft whiskeringCell cellBeta')
  /-- Congruence under a right whiskering. -/
  whiskerRightCongr : {dim : Nat} → {cellAlpha : CellExpr computad (dim + 2)} →
    {cellAlpha' : CellExpr computad (dim + 2)} → {whiskeringCell : CellExpr computad (dim + 1)} →
    targetRel cellAlpha cellAlpha' →
    targetRel (CellExpr.whiskerRight cellAlpha whiskeringCell)
      (CellExpr.whiskerRight cellAlpha' whiskeringCell)
  /-- Reflexivity. -/
  refl : {dim : Nat} → (cell : CellExpr computad dim) → targetRel cell cell
  /-- Symmetry. -/
  symm : {dim : Nat} → {cellAlpha : CellExpr computad dim} → {cellBeta : CellExpr computad dim} →
    targetRel cellAlpha cellBeta → targetRel cellBeta cellAlpha
  /-- Transitivity. -/
  trans : {dim : Nat} → {cellAlpha : CellExpr computad dim} → {cellBeta : CellExpr computad dim} →
    {cellGamma : CellExpr computad dim} →
    targetRel cellAlpha cellBeta → targetRel cellBeta cellGamma → targetRel cellAlpha cellGamma

/-- ★ **The universal property of `SaturatedConvOver`** — its sole eliminator, the invariant fold into any
absorbing congruence `targetRel`.  This is the dimension-generic form of the ~8x-bespoke soundness /
map-out leg; OMEGA-2's Steiner soundness instantiates it at `targetRel := fun a b => linearize a = linearize b`. -/
theorem SaturatedConvOver.recInto {computad : OmegaComputad} {baseRel targetRel : CellRelOver computad}
    (absorbs : IsSaturatedCongruence computad baseRel targetRel)
    {dim : Nat} {cellAlpha cellBeta : CellExpr computad dim}
    (conv : SaturatedConvOver computad baseRel cellAlpha cellBeta) : targetRel cellAlpha cellBeta := by
  induction conv with
  | ofRelation row => exact absorbs.ofRelation row
  | vcompCongrLeft _ _ ih => exact absorbs.vcompCongrLeft ih
  | vcompCongrRight _ _ ih => exact absorbs.vcompCongrRight ih
  | whiskerLeftCongr _ _ ih => exact absorbs.whiskerLeftCongr ih
  | whiskerRightCongr _ _ ih => exact absorbs.whiskerRightCongr ih
  | refl cell => exact absorbs.refl cell
  | symm _ ih => exact absorbs.symm ih
  | trans _ _ ihLeft ihRight => exact absorbs.trans ihLeft ihRight

/-! ## The decision interface -/

/-- The **saturated-convertibility decision interface** for a law relation `baseRel`: saturated convertibility
is decidable on every parallel pair of same-dimension cells.  The generic analog of the dim-2
`DecidableSaturatedConvForRel`. -/
def DecidableSaturatedConvOver (computad : OmegaComputad) (baseRel : CellRelOver computad) : Type :=
  {dim : Nat} → (cellAlpha cellBeta : CellExpr computad dim) →
  Decidable (SaturatedConvOver computad baseRel cellAlpha cellBeta)

end FX1Poly.Polygraph.Omega
