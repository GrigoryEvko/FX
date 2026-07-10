import FX1Poly.Polygraph.Omega.Congruence

/-! # Polygraph/Omega/CongruenceWithId — the idCongr-extended saturated cell congruence (OMEGA-3 r2, B1)

★ **The additive sibling of `SaturatedConvOver`.**  The shipped dimension-generic congruence
(`Omega/Congruence.lean`) has EIGHT constructors — `ofRelation` + the four one-hole congruences
(`vcompCongrLeft` / `vcompCongrRight` / `whiskerLeftCongr` / `whiskerRightCongr`) + `refl` / `symm` /
`trans` — and NO way to lift `a ~_n b` to `id a ~_{n+1} id b`, nor to vary the WHISKERING 1-cell of a
whiskered composite.  That is the exact wall the OMEGA-1 B2 conv-leg named
(`fxOmega_bridgeDimTwoConvLegOpen`): `TwoCellStep.vcompIdLeft` maps to `vcomp (id (realize F)) (toCell α)`,
whose strict-unit reduction needs `id (realize F) ~ id (boundarySource (toCell α))`, an `id`-congruence the
8-constructor relation lacks.

This file ships the fresh ELEVEN-constructor sibling `SaturatedConvOverWithId`: the eight shipped shapes
verbatim, plus

  * **`idCongr`** — the dimension-bump identity congruence `a ~_n b → CellExpr.id a ~_{n+1} CellExpr.id b`;
  * **`whiskerLeftWhiskerCongr`** / **`whiskerRightWhiskerCongr`** — the whiskering-1-cell congruences (the
    DUAL of the shipped whisker congruences: the whiskering cell varies, the whiskered cell is fixed).

All shipped declarations keep name and meaning; nothing is edited or deleted.  The sibling is a strict
superset of the old congruence — the free embedding `embedSaturatedConvOver` folds every old derivation into
the sibling.

## The fresh inductive (recon verdict: NOT a layered closure)

A layered inductive `... | ofBase : SaturatedConvOver baseRel a b → ...` would have to re-declare all four
one-hole congruences anyway (`ofBase` embeds only old derivations, which lack `idCongr` under the one-hole
contexts), saving zero constructors and worsening `recInto`.  A stratified-relation variant captures only
one `id`-shift depth (`id (id a) ~ id (id b)` unreachable).  So the sibling is a fresh 11-constructor
inductive; `recInto` stays a clean 11-arm fold and the embedding old → new is free.

## The jam discharged over the sibling (the falsifiability check)

`vcompIdLeft_bridgedWithId` discharges the EXACT OMEGA-1 wall step — from a sibling convertibility
`sourceCandidate ~ boundarySource cellA`, `idCongr` lifts it to the identity 1-cells, `vcompCongrLeft`
places it under the vertical composite, and the unit row absorbs the trailing identity.  This is the key
`idCongr` unlocks; a concrete crown-computad instance is machine-checked in `CongruenceWithIdNonVacuity`.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! ## The dimension-generic saturated congruence, extended by the dimension-bump / whisker-1-cell congruences -/

/-- ★ The **idCongr-extended dimension-generic saturated cell congruence** — the additive sibling of
`SaturatedConvOver`.  The eight shipped shapes (`ofRelation`, the four one-hole congruences, `refl` / `symm`
/ `trans`) plus the dimension-bump identity congruence `idCongr` and the two whiskering-1-cell congruences.
A strict superset of `SaturatedConvOver baseRel` (via `embedSaturatedConvOver`) that additionally proves
`id a ~ id b` from `a ~ b` and varies the whiskering cell of a whisker. -/
inductive SaturatedConvOverWithId (computad : OmegaComputad) (baseRel : CellRelOver computad) :
    {dim : Nat} → CellExpr computad dim → CellExpr computad dim → Prop where
  /-- Embed a law row of `baseRel` as a generating equation (fixed boundary). -/
  | ofRelation {dim : Nat} {cellAlpha cellBeta : CellExpr computad dim} :
      baseRel cellAlpha cellBeta → SaturatedConvOverWithId computad baseRel cellAlpha cellBeta
  /-- Congruence in the LEFT factor of a vertical composite. -/
  | vcompCongrLeft {dim : Nat} {cellAlpha cellAlpha' : CellExpr computad (dim + 1)}
      (cellBeta : CellExpr computad (dim + 1)) :
      SaturatedConvOverWithId computad baseRel cellAlpha cellAlpha' →
      SaturatedConvOverWithId computad baseRel (CellExpr.vcomp cellAlpha cellBeta)
        (CellExpr.vcomp cellAlpha' cellBeta)
  /-- Congruence in the RIGHT factor of a vertical composite. -/
  | vcompCongrRight {dim : Nat} (cellAlpha : CellExpr computad (dim + 1))
      {cellBeta cellBeta' : CellExpr computad (dim + 1)} :
      SaturatedConvOverWithId computad baseRel cellBeta cellBeta' →
      SaturatedConvOverWithId computad baseRel (CellExpr.vcomp cellAlpha cellBeta)
        (CellExpr.vcomp cellAlpha cellBeta')
  /-- Congruence under a left whiskering (the WHISKERED cell varies; the whiskering cell fixed). -/
  | whiskerLeftCongr {dim : Nat} (whiskeringCell : CellExpr computad (dim + 1))
      {cellBeta cellBeta' : CellExpr computad (dim + 2)} :
      SaturatedConvOverWithId computad baseRel cellBeta cellBeta' →
      SaturatedConvOverWithId computad baseRel (CellExpr.whiskerLeft whiskeringCell cellBeta)
        (CellExpr.whiskerLeft whiskeringCell cellBeta')
  /-- Congruence under a right whiskering (the WHISKERED cell varies; the whiskering cell fixed). -/
  | whiskerRightCongr {dim : Nat} {cellAlpha cellAlpha' : CellExpr computad (dim + 2)}
      (whiskeringCell : CellExpr computad (dim + 1)) :
      SaturatedConvOverWithId computad baseRel cellAlpha cellAlpha' →
      SaturatedConvOverWithId computad baseRel (CellExpr.whiskerRight cellAlpha whiskeringCell)
        (CellExpr.whiskerRight cellAlpha' whiskeringCell)
  /-- ★ The **dimension-bump identity congruence** — the missing rule the OMEGA-1 conv-leg named: lift a
  `dim`-cell convertibility to the identity `(dim+1)`-cells.  No boundary side condition: `CellExpr.id`
  accepts any `dim`-cell and its boundaries are automatically `(cellAlpha, cellAlpha)` / `(cellBeta,
  cellBeta)`. -/
  | idCongr {dim : Nat} {cellAlpha cellBeta : CellExpr computad dim} :
      SaturatedConvOverWithId computad baseRel cellAlpha cellBeta →
      SaturatedConvOverWithId computad baseRel (CellExpr.id cellAlpha) (CellExpr.id cellBeta)
  /-- ★ The **left whiskering-1-cell congruence** — the DUAL of `whiskerLeftCongr`: the whiskering cell
  varies, the whiskered cell is fixed.  Needed for composite 1-cells in whisker position (the general bridge
  conv leg / whiskered completeness). -/
  | whiskerLeftWhiskerCongr {dim : Nat} {whiskerAlpha whiskerAlpha' : CellExpr computad (dim + 1)}
      (innerCell : CellExpr computad (dim + 2)) :
      SaturatedConvOverWithId computad baseRel whiskerAlpha whiskerAlpha' →
      SaturatedConvOverWithId computad baseRel (CellExpr.whiskerLeft whiskerAlpha innerCell)
        (CellExpr.whiskerLeft whiskerAlpha' innerCell)
  /-- ★ The **right whiskering-1-cell congruence** — the DUAL of `whiskerRightCongr`. -/
  | whiskerRightWhiskerCongr {dim : Nat} (innerCell : CellExpr computad (dim + 2))
      {whiskerAlpha whiskerAlpha' : CellExpr computad (dim + 1)} :
      SaturatedConvOverWithId computad baseRel whiskerAlpha whiskerAlpha' →
      SaturatedConvOverWithId computad baseRel (CellExpr.whiskerRight innerCell whiskerAlpha)
        (CellExpr.whiskerRight innerCell whiskerAlpha')
  /-- Reflexivity. -/
  | refl {dim : Nat} (cell : CellExpr computad dim) :
      SaturatedConvOverWithId computad baseRel cell cell
  /-- Symmetry. -/
  | symm {dim : Nat} {cellAlpha cellBeta : CellExpr computad dim} :
      SaturatedConvOverWithId computad baseRel cellAlpha cellBeta →
      SaturatedConvOverWithId computad baseRel cellBeta cellAlpha
  /-- Transitivity. -/
  | trans {dim : Nat} {cellAlpha cellBeta cellGamma : CellExpr computad dim} :
      SaturatedConvOverWithId computad baseRel cellAlpha cellBeta →
      SaturatedConvOverWithId computad baseRel cellBeta cellGamma →
      SaturatedConvOverWithId computad baseRel cellAlpha cellGamma

/-! ## The universal property — the eliminator into any absorbing congruence -/

/-- A target relation `targetRel` **absorbs** the idCongr-extended saturated congruence over `baseRel` —
the eight shipped fields plus the three new ones (`idCongr`, the two whiskering-1-cell congruences).  Fields
are uniform Pi (no mixed implicit/explicit before the arrow). -/
structure IsSaturatedCongruenceWithId (computad : OmegaComputad)
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
  /-- Congruence under a left whiskering (the whiskered cell varies). -/
  whiskerLeftCongr : {dim : Nat} → {whiskeringCell : CellExpr computad (dim + 1)} →
    {cellBeta : CellExpr computad (dim + 2)} → {cellBeta' : CellExpr computad (dim + 2)} →
    targetRel cellBeta cellBeta' →
    targetRel (CellExpr.whiskerLeft whiskeringCell cellBeta)
      (CellExpr.whiskerLeft whiskeringCell cellBeta')
  /-- Congruence under a right whiskering (the whiskered cell varies). -/
  whiskerRightCongr : {dim : Nat} → {cellAlpha : CellExpr computad (dim + 2)} →
    {cellAlpha' : CellExpr computad (dim + 2)} → {whiskeringCell : CellExpr computad (dim + 1)} →
    targetRel cellAlpha cellAlpha' →
    targetRel (CellExpr.whiskerRight cellAlpha whiskeringCell)
      (CellExpr.whiskerRight cellAlpha' whiskeringCell)
  /-- The dimension-bump identity congruence. -/
  idCongr : {dim : Nat} → {cellAlpha : CellExpr computad dim} → {cellBeta : CellExpr computad dim} →
    targetRel cellAlpha cellBeta → targetRel (CellExpr.id cellAlpha) (CellExpr.id cellBeta)
  /-- The left whiskering-1-cell congruence (the whiskering cell varies). -/
  whiskerLeftWhiskerCongr : {dim : Nat} → {whiskerAlpha : CellExpr computad (dim + 1)} →
    {whiskerAlpha' : CellExpr computad (dim + 1)} → {innerCell : CellExpr computad (dim + 2)} →
    targetRel whiskerAlpha whiskerAlpha' →
    targetRel (CellExpr.whiskerLeft whiskerAlpha innerCell)
      (CellExpr.whiskerLeft whiskerAlpha' innerCell)
  /-- The right whiskering-1-cell congruence (the whiskering cell varies). -/
  whiskerRightWhiskerCongr : {dim : Nat} → {innerCell : CellExpr computad (dim + 2)} →
    {whiskerAlpha : CellExpr computad (dim + 1)} → {whiskerAlpha' : CellExpr computad (dim + 1)} →
    targetRel whiskerAlpha whiskerAlpha' →
    targetRel (CellExpr.whiskerRight innerCell whiskerAlpha)
      (CellExpr.whiskerRight innerCell whiskerAlpha')
  /-- Reflexivity. -/
  refl : {dim : Nat} → (cell : CellExpr computad dim) → targetRel cell cell
  /-- Symmetry. -/
  symm : {dim : Nat} → {cellAlpha : CellExpr computad dim} → {cellBeta : CellExpr computad dim} →
    targetRel cellAlpha cellBeta → targetRel cellBeta cellAlpha
  /-- Transitivity. -/
  trans : {dim : Nat} → {cellAlpha : CellExpr computad dim} → {cellBeta : CellExpr computad dim} →
    {cellGamma : CellExpr computad dim} →
    targetRel cellAlpha cellBeta → targetRel cellBeta cellGamma → targetRel cellAlpha cellGamma

/-- ★ **The universal property of `SaturatedConvOverWithId`** — its sole eliminator, the invariant fold into
any absorbing congruence.  The dimension-generic map-out for the idCongr-extended sibling; OMEGA-3's soundness
cascade instantiates it at `targetRel := fun a b => linearize a = linearize b` and its chain analog. -/
theorem SaturatedConvOverWithId.recInto {computad : OmegaComputad}
    {baseRel targetRel : CellRelOver computad}
    (absorbs : IsSaturatedCongruenceWithId computad baseRel targetRel)
    {dim : Nat} {cellAlpha cellBeta : CellExpr computad dim}
    (conv : SaturatedConvOverWithId computad baseRel cellAlpha cellBeta) :
    targetRel cellAlpha cellBeta := by
  induction conv with
  | ofRelation row => exact absorbs.ofRelation row
  | vcompCongrLeft _ _ ih => exact absorbs.vcompCongrLeft ih
  | vcompCongrRight _ _ ih => exact absorbs.vcompCongrRight ih
  | whiskerLeftCongr _ _ ih => exact absorbs.whiskerLeftCongr ih
  | whiskerRightCongr _ _ ih => exact absorbs.whiskerRightCongr ih
  | idCongr _ ih => exact absorbs.idCongr ih
  | whiskerLeftWhiskerCongr _ _ ih => exact absorbs.whiskerLeftWhiskerCongr ih
  | whiskerRightWhiskerCongr _ _ ih => exact absorbs.whiskerRightWhiskerCongr ih
  | refl cell => exact absorbs.refl cell
  | symm _ ih => exact absorbs.symm ih
  | trans _ _ ihLeft ihRight => exact absorbs.trans ihLeft ihRight

/-! ## The free embedding old → new -/

/-- The shipped 8-constructor congruence absorbs into the sibling: every one of its eight shapes is a
namesake constructor of `SaturatedConvOverWithId`.  The fold data for `embedSaturatedConvOver`. -/
def isSaturatedCongruenceEmbedWithId (computad : OmegaComputad) (baseRel : CellRelOver computad) :
    IsSaturatedCongruence computad baseRel
      (fun {_dim : Nat} cellAlpha cellBeta => SaturatedConvOverWithId computad baseRel cellAlpha cellBeta) where
  ofRelation := by intro _dim _cellAlpha _cellBeta row; exact SaturatedConvOverWithId.ofRelation row
  vcompCongrLeft := by
    intro _dim _cellAlpha _cellAlpha' cellBeta conv
    exact SaturatedConvOverWithId.vcompCongrLeft cellBeta conv
  vcompCongrRight := by
    intro _dim cellAlpha _cellBeta _cellBeta' conv
    exact SaturatedConvOverWithId.vcompCongrRight cellAlpha conv
  whiskerLeftCongr := by
    intro _dim whiskeringCell _cellBeta _cellBeta' conv
    exact SaturatedConvOverWithId.whiskerLeftCongr whiskeringCell conv
  whiskerRightCongr := by
    intro _dim _cellAlpha _cellAlpha' whiskeringCell conv
    exact SaturatedConvOverWithId.whiskerRightCongr whiskeringCell conv
  refl := by intro _dim cell; exact SaturatedConvOverWithId.refl cell
  symm := by intro _dim _cellAlpha _cellBeta conv; exact SaturatedConvOverWithId.symm conv
  trans := by
    intro _dim _cellAlpha _cellBeta _cellGamma convLeft convRight
    exact SaturatedConvOverWithId.trans convLeft convRight

/-- ★ **The free embedding** — every shipped `SaturatedConvOver` derivation folds into the sibling.  The
sibling is a strict superset of the old congruence, so downstream stays on the old relation while the sibling
adds the id / whisker-1-cell content. -/
theorem embedSaturatedConvOver {computad : OmegaComputad} {baseRel : CellRelOver computad}
    {dim : Nat} {cellAlpha cellBeta : CellExpr computad dim}
    (conv : SaturatedConvOver computad baseRel cellAlpha cellBeta) :
    SaturatedConvOverWithId computad baseRel cellAlpha cellBeta :=
  SaturatedConvOver.recInto (isSaturatedCongruenceEmbedWithId computad baseRel) conv

/-! ## The vcompIdLeft jam, discharged over the sibling -/

/-- ★ **THE OMEGA-1 JAM STEP, DISCHARGED.**  The exact wall step the 8-constructor congruence could not take:
from a sibling convertibility `sourceCandidate ~ boundarySource cellA`, `idCongr` lifts it to the identity
1-cells, `vcompCongrLeft` places it under the vertical composite, and the supplied unit row absorbs the
trailing identity — yielding `vcomp (id sourceCandidate) cellA ~ cellA`.  Generic in `baseRel`, keyed on
`idCongr` (the 8-constructor relation has no such rule). -/
theorem vcompIdLeft_bridgedWithId {computad : OmegaComputad} {baseRel : CellRelOver computad}
    {dim : Nat} {sourceCandidate : CellExpr computad dim} (cellA : CellExpr computad (dim + 1))
    (hconv : SaturatedConvOverWithId computad baseRel sourceCandidate (boundarySource cellA))
    (unitRow : SaturatedConvOverWithId computad baseRel
      (CellExpr.vcomp (CellExpr.id (boundarySource cellA)) cellA) cellA) :
    SaturatedConvOverWithId computad baseRel
      (CellExpr.vcomp (CellExpr.id sourceCandidate) cellA) cellA :=
  SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.vcompCongrLeft cellA (SaturatedConvOverWithId.idCongr hconv))
    unitRow

end FX1Poly.Polygraph.Omega
