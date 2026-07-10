import FX1Poly.Polygraph.Omega.CongruenceWithId
import FX1Poly.Polygraph.Omega.Steiner.Reconstruct

/-! # Polygraph/Omega/EckmannHiltonWithId — conv-form Eckmann-Hilton on the doubly-degenerate fragment
(OMEGA-3 r2, B4)

★ **Conv-form Eckmann-Hilton, as a genuine `SaturatedConvOverWithId` derivation.**  OMEGA-3 r1 shipped
Eckmann-Hilton at the ARITHMETIC (single-vector table) level: `linearize (godementComp a b) = linearize
(vcomp a b)` and commutativity by `addCoordinates_comm` (`Suspension.lean`).  This file lifts it to the
CONV form — an actual convertibility derivation — on the doubly-degenerate fragment (cells whose deep
boundaries are identity 1-cells, e.g. crown atoms `a = b = crownAtom`).

## The honest ingredient (recon §4, executed)

The conv-form EH does NOT use `idCongr`: its two legs need the whisker-BY-IDENTITY-1-CELL unit laws
`whiskerLeft (id c) b ~ b` and `whiskerRight b (id c) ~ b`, which the shipped `StrictAxiomRel` lacks (its
`whiskerLeftUnit` / `whiskerRightUnit` whisker an identity 2-CELL, not by an identity 1-cell).  So this
ships them as a fresh ADDITIVE 2-row relation `whiskerUnitRel` (never editing `StrictAxiomRel`), unites it
with the strict laws, and derives EH over the sibling congruence `SaturatedConvOverWithId` on that union.
The whisker-unit rows are single-vector SOUND (`linearize_whiskerUnitRel`, `rfl`), so the augmented model
does not collapse.

  * **Interchange `*_0 = *_1`** — `godementComp a b ~ vcomp a b` — when `boundaryTarget a` and
    `boundarySource b` are identity 1-cells: `whiskerRight a (id ·) ~ a`, `whiskerLeft (id ·) b ~ b`, then
    `vcompCongr`.
  * **Commutativity** — `vcomp a b ~ vcomp b a` — when all four boundaries are identity 1-cells: run the
    interchange row (`StrictAxiomRel.interchange`) between the two Godement forms and cancel the whisker
    units.  (Non-vacuous only at DISTINCT `a`, `b`; the two-generator `ehComputad` supplies them.)

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

open FX1Poly.Polygraph.Steiner

/-! ## The whisker-by-identity-1-cell unit rows (fresh, additive) -/

/-- ★ The **whisker-by-identity-1-cell unit laws** — the two rows the conv-form EH needs and the shipped
`StrictAxiomRel` lacks: whiskering a cell by an IDENTITY 1-CELL is a no-op.  A fresh 2-row relation
(`StrictAxiomRel` is untouched); single-vector sound (`linearize` forgets the whisker). -/
inductive whiskerUnitRel (computad : OmegaComputad) :
    {dim : Nat} → CellExpr computad dim → CellExpr computad dim → Prop where
  /-- Left whisker by an identity 1-cell `id lower` is a no-op. -/
  | whiskerLeftIdCellUnit {dim : Nat} (lower : CellExpr computad dim)
      (cell : CellExpr computad (dim + 2)) :
      whiskerUnitRel computad (CellExpr.whiskerLeft (CellExpr.id lower) cell) cell
  /-- Right whisker by an identity 1-cell `id lower` is a no-op. -/
  | whiskerRightIdCellUnit {dim : Nat} (cell : CellExpr computad (dim + 2))
      (lower : CellExpr computad dim) :
      whiskerUnitRel computad (CellExpr.whiskerRight cell (CellExpr.id lower)) cell

/-- The **strict laws augmented with the whisker-by-identity-1-cell units** — the relation the conv-form EH
runs over.  Additive: `unionCellRel` of the shipped `StrictAxiomRel` and the fresh `whiskerUnitRel`. -/
def strictWithWhiskerUnits (computad : OmegaComputad) : CellRelOver computad :=
  unionCellRel computad (StrictAxiomRel computad) (whiskerUnitRel computad)

/-- ★ **The whisker-unit rows are single-vector SOUND.**  Both discharge by `rfl`: `linearize` projects a
whisker to its main factor, forgetting the whiskering cell.  So the augmented model does not collapse. -/
theorem linearize_whiskerUnitRel {computad : OmegaComputad} (valuation : ComputadValuation computad)
    {dim : Nat} {cellA cellB : CellExpr computad dim} (row : whiskerUnitRel computad cellA cellB) :
    linearize valuation cellA = linearize valuation cellB := by
  cases row with
  | whiskerLeftIdCellUnit lower cell => rfl
  | whiskerRightIdCellUnit cell lower => rfl

/-! ## Conv-form interchange `*_0 = *_1` (identity-boundary hypothesis) -/

/-- ★ **CONV-FORM INTERCHANGE.**  When `boundaryTarget cellAlpha` and `boundarySource cellBeta` are
identity 1-cells, the Godement composite is convertible to the vertical composite:
`godementComp a b ~ vcomp a b`.  The two whisker-by-identity-1-cell units cancel the outer whiskers, then
`vcompCongr` reassembles.  No `idCongr` — the whisker-unit rows carry it. -/
theorem godementComp_conv_vcomp_ofIdBoundaries {computad : OmegaComputad} {dim : Nat}
    (cellAlpha cellBeta : CellExpr computad (dim + 2))
    {lowerTargetAlpha lowerSourceBeta : CellExpr computad dim}
    (hBtAlpha : boundaryTarget cellAlpha = CellExpr.id lowerTargetAlpha)
    (hBsBeta : boundarySource cellBeta = CellExpr.id lowerSourceBeta) :
    SaturatedConvOverWithId computad (strictWithWhiskerUnits computad)
      (godementComp cellAlpha cellBeta) (CellExpr.vcomp cellAlpha cellBeta) := by
  show SaturatedConvOverWithId computad (strictWithWhiskerUnits computad)
    (CellExpr.vcomp (CellExpr.whiskerRight cellAlpha (boundarySource cellBeta))
      (CellExpr.whiskerLeft (boundaryTarget cellAlpha) cellBeta)) (CellExpr.vcomp cellAlpha cellBeta)
  rw [hBsBeta, hBtAlpha]
  exact SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.vcompCongrLeft _
      (SaturatedConvOverWithId.ofRelation
        (Or.inr (whiskerUnitRel.whiskerRightIdCellUnit cellAlpha lowerSourceBeta))))
    (SaturatedConvOverWithId.vcompCongrRight cellAlpha
      (SaturatedConvOverWithId.ofRelation
        (Or.inr (whiskerUnitRel.whiskerLeftIdCellUnit lowerTargetAlpha cellBeta))))

/-! ## Conv-form commutativity (all-identity-boundary hypothesis) -/

/-- ★★ **CONV-FORM ECKMANN-HILTON COMMUTATIVITY.**  When ALL four boundaries of `cellAlpha` and `cellBeta`
are identity 1-cells, `vcomp a b ~ vcomp b a`: run the Godement interchange row between the two Godement
forms, and cancel the whisker-by-identity-1-cell units.  The syntactic form of Eckmann-Hilton — genuine
convertibility, not merely equal tables. -/
theorem vcomp_comm_conv_ofIdBoundaries {computad : OmegaComputad} {dim : Nat}
    (cellAlpha cellBeta : CellExpr computad (dim + 2))
    {lowerSourceAlpha lowerTargetAlpha lowerSourceBeta lowerTargetBeta : CellExpr computad dim}
    (hBsAlpha : boundarySource cellAlpha = CellExpr.id lowerSourceAlpha)
    (hBtAlpha : boundaryTarget cellAlpha = CellExpr.id lowerTargetAlpha)
    (hBsBeta : boundarySource cellBeta = CellExpr.id lowerSourceBeta)
    (hBtBeta : boundaryTarget cellBeta = CellExpr.id lowerTargetBeta) :
    SaturatedConvOverWithId computad (strictWithWhiskerUnits computad)
      (CellExpr.vcomp cellAlpha cellBeta) (CellExpr.vcomp cellBeta cellAlpha) := by
  refine SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.symm
      (godementComp_conv_vcomp_ofIdBoundaries cellAlpha cellBeta hBtAlpha hBsBeta)) ?_
  refine SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.ofRelation (Or.inl (StrictAxiomRel.interchange cellAlpha cellBeta))) ?_
  rw [hBsAlpha, hBtBeta]
  exact SaturatedConvOverWithId.trans
    (SaturatedConvOverWithId.vcompCongrLeft _
      (SaturatedConvOverWithId.ofRelation
        (Or.inr (whiskerUnitRel.whiskerLeftIdCellUnit lowerSourceAlpha cellBeta))))
    (SaturatedConvOverWithId.vcompCongrRight cellBeta
      (SaturatedConvOverWithId.ofRelation
        (Or.inr (whiskerUnitRel.whiskerRightIdCellUnit cellAlpha lowerTargetBeta))))

/-! ## Non-vacuity 1 — the crown doubly-degenerate demo (interchange collapses) -/

/-- ★ **Conv-form interchange on the doubly-degenerate crown atom.**  `a = b = crownAtom (dim+1)`, whose
deep boundaries are the identity 1-cell `crownBaseCell (dim+1) = id (crownBaseCell dim)` — so
`godementComp a a ~ vcomp a a` holds by `rfl` boundary hypotheses. -/
theorem crownGodement_conv_vcomp (dim : Nat) :
    SaturatedConvOverWithId crownComputad (strictWithWhiskerUnits crownComputad)
      (godementComp (crownAtom (dim + 1)) (crownAtom (dim + 1)))
      (CellExpr.vcomp (crownAtom (dim + 1)) (crownAtom (dim + 1))) :=
  godementComp_conv_vcomp_ofIdBoundaries (crownAtom (dim + 1)) (crownAtom (dim + 1)) rfl rfl

/-! ## Non-vacuity 2 — a two-generator demo (commutativity, distinct cells) -/

/-- A two-generator one-object computad — `Unit` modes, `Bool` generator labels — enough for two DISTINCT
cells sharing an identity boundary. -/
def ehComputad : OmegaComputad where
  modeCarrier := Unit
  genLabel := fun _ => Bool

/-- The identity tower base cell of `ehComputad`. -/
def ehBaseCell : (dim : Nat) → CellExpr ehComputad dim
  | 0 => CellExpr.ofMode ()
  | dim + 1 => CellExpr.id (ehBaseCell dim)

/-- A `(dim+2)`-cell generator over `ehComputad`, labelled by a `Bool`, with identity-1-cell boundaries. -/
def ehAtom (label : Bool) (dim : Nat) : CellExpr ehComputad (dim + 2) :=
  CellExpr.gen label (ehBaseCell (dim + 1)) (ehBaseCell (dim + 1))

/-- ★★ **Conv-form Eckmann-Hilton commutativity on DISTINCT cells.**  The two distinct `ehAtom` generators
(`true` / `false`) commute up to sibling convertibility: `vcomp (ehAtom true) (ehAtom false) ~ vcomp (ehAtom
false) (ehAtom true)`.  Their four boundaries are the identity 1-cell `ehBaseCell (dim+1)` by `rfl`, so the
commutativity theorem applies. -/
theorem ehGenComm (dim : Nat) :
    SaturatedConvOverWithId ehComputad (strictWithWhiskerUnits ehComputad)
      (CellExpr.vcomp (ehAtom true dim) (ehAtom false dim))
      (CellExpr.vcomp (ehAtom false dim) (ehAtom true dim)) :=
  vcomp_comm_conv_ofIdBoundaries (ehAtom true dim) (ehAtom false dim) rfl rfl rfl rfl

/-! ## OMEGA-3 r2 conv-form EH markers (B4 — strictly factual) -/

/-- ★ **B4 — conv-form Eckmann-Hilton is SHIPPED (via the whisker-by-id-1-cell rows).**  Interchange
`*_0 = *_1` (`godementComp_conv_vcomp_ofIdBoundaries`, `crownGodement_conv_vcomp`) and commutativity on
DISTINCT cells (`vcomp_comm_conv_ofIdBoundaries`, `ehGenComm`) are genuine `SaturatedConvOverWithId`
derivations — the SYNTACTIC form of Eckmann-Hilton, not merely equal tables.  Honest per recon §4: this uses
the two whisker-by-identity-1-cell unit rows (fresh, single-vector sound), NOT `idCongr` — conv-form EH and
the idCongr sibling are orthogonal.  `= true`. -/
def fxOmega_convFormEckmannHiltonShippedR2 : Bool := true

end FX1Poly.Polygraph.Omega
