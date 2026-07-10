import FX1Poly.Polygraph.Omega.Steiner.Reconstruct

/-! # Polygraph/Omega/Suspension — the dimension-RAISING operation (OMEGA-3 r1, B1+B2+B3)

★ **Suspension** carries an omega-computad, its free cells, and their Steiner tables ONE dimension up, and
proves the free strict congruence is FAITHFULLY embedded by it.  This is the world-first (d) of the staircase:
a dimension-RAISING op that lets dim-2 mode theory / confluence certificates be viewed at dim 3 without
re-encoding, plus the arithmetic that the ceiling lift (`Omega/CeilingLift.lean`) and Eckmann-Hilton ride.

## The three suspension maps (B1)

  * **`suspendComputad`** — two poles (`Bool`) replace the single old object; the old `d`-cell generators become
    `(d+1)`-cell generators, and the old 0-cells (modes) become the `⊥ → ⊤` 1-generators.  (`suspendGenLabel`
    is the per-dimension label reindex.)
  * **`suspendCell`** — the structural cell map `CellExpr computad dim → CellExpr (suspendComputad computad)
    (dim+1)`: a homomorphism for `gen`/`id`/`vcomp`/`whisker` (constant-shape codomain modulo the uniform
    `dim ↦ dim+1` shift) that sends a 0-cell (object) to the `⊥ → ⊤` suspension 1-cell.
  * **`suspendValuation` / `suspendTable`** — the Steiner side: because `SteinerCell` is dimension-agnostic
    (a single ambient basis), suspension leaves the TOP vector literally unchanged.  With the compatibly
    shifted valuation, `linearize (suspendCell a) = linearize a` (`linearize_suspend`), so **`suspendTable`
    is the IDENTITY** — stronger and cleaner than a list reindex.

## The faithful embedding (B1 preservation + B2 reflection)

  * **Preservation.**  `suspendPreservesStrictConv` — the 8-arm `SaturatedConvOver` induction: each strict-axiom
    row maps to its own row one dimension up (`suspendStrictRow`, discharged by the boundary-commutation
    `suspendCell_boundarySource` / `_boundaryTarget`), and the four one-hole congruences lift by the
    `suspendCell` homomorphism (each `rfl`).
  * **Reflection (arithmetic route).**  `suspend_reflects_atomWordConv` — the memo's fallback: `linearize
    (suspendCell a) = linearize a` (with `suspendTable` injective, being `id`) reflects table equality DOWN
    the suspension; composed with atom-word completeness (`atomWord_conv_of_linearize_eq`) it reflects
    CONVERTIBILITY on the whisker-free single-generator fragment, dodging syntactic fullness.  Together with
    preservation this is the FAITHFUL embedding `suspend_faithful_atomWord`, scoped honestly.

## Eckmann-Hilton as structure (B3)

`godementComp` (the horizontal `*_dim`) and `vcomp` (the vertical `*_{dim}`) both linearize to the coordinate
SUM, so:
  * **Interchange `*_0 = *_1`** is `linearize (godementComp a b) = linearize (vcomp a b)` — by **`rfl`**.
  * **Commutativity** is `linearize (godementComp a b) = linearize (godementComp b a)` — by **`addCoordinates_comm`**,
    the SAME lemma the interchange soundness row already discharges.  Eckmann-Hilton FALLS OUT of Int-addition
    commutativity (no bespoke argument); the honest conv-form is the OMEGA-3 r2 owe (needs completeness on the
    doubly-degenerate fragment).

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

open FX1Poly.Polygraph.Steiner

/-! ## The suspended computad (B1) -/

/-- The **suspended generator-label family**: no 0-cell generators (`PEmpty` — the two poles ARE the 0-cells),
the old modes become the `⊥ → ⊤` 1-generators (`suspendGenLabel 1 = modeCarrier`), and the old `(k+1)`-cell
generators become `(k+2)`-cell generators (`suspendGenLabel (k+2) = genLabel (k+1)`).  A `Nat`-recursive
`Type`, propext-free. -/
def suspendGenLabel (computad : OmegaComputad) : Nat → Type
  | 0 => PEmpty
  | 1 => computad.modeCarrier
  | k + 2 => computad.genLabel (k + 1)

/-- The **suspended computad** — two poles (`Bool`: `⊥ = false`, `⊤ = true`) replace the single old object,
with the dimension-shifted generator labels.  This is the topological suspension of the generating data. -/
def suspendComputad (computad : OmegaComputad) : OmegaComputad where
  modeCarrier := Bool
  genLabel := suspendGenLabel computad

/-! ## The suspended cell map (B1) -/

/-- ★ **The structural suspension of a cell** — `CellExpr computad dim → CellExpr (suspendComputad computad)
(dim+1)`.  A 0-cell (object) becomes the suspension 1-cell `⊥ → ⊤` (`gen` at label = the old mode); every other
generator raises its dimension by one; `id`/`vcomp`/`whisker` map homomorphically (constant-shape codomain
modulo the uniform `dim ↦ dim+1` shift).  Total over all six constructors — no impossible-case discharge, so
propext-free like `cellSize` / `toSkeleton`. -/
def suspendCell {computad : OmegaComputad} :
    {dim : Nat} → CellExpr computad dim → CellExpr (suspendComputad computad) (dim + 1)
  | _, .ofMode mode => CellExpr.gen mode (CellExpr.ofMode false) (CellExpr.ofMode true)
  | _, .gen label source target => CellExpr.gen label (suspendCell source) (suspendCell target)
  | _, .id inner => CellExpr.id (suspendCell inner)
  | _, .vcomp left right => CellExpr.vcomp (suspendCell left) (suspendCell right)
  | _, .whiskerLeft whiskeringCell inner => CellExpr.whiskerLeft (suspendCell whiskeringCell) (suspendCell inner)
  | _, .whiskerRight inner whiskeringCell =>
      CellExpr.whiskerRight (suspendCell inner) (suspendCell whiskeringCell)

/-! ## The homomorphism computation lemmas (each `rfl`) -/

/-- `suspendCell` of a vertical composite is the vertical composite of the suspensions. -/
theorem suspendCell_vcomp {computad : OmegaComputad} {dim : Nat}
    (left right : CellExpr computad (dim + 1)) :
    suspendCell (CellExpr.vcomp left right) = CellExpr.vcomp (suspendCell left) (suspendCell right) := rfl

/-- `suspendCell` of an identity is the identity of the suspension. -/
theorem suspendCell_id {computad : OmegaComputad} {dim : Nat} (inner : CellExpr computad dim) :
    suspendCell (CellExpr.id inner) = CellExpr.id (suspendCell inner) := rfl

/-- `suspendCell` of a left whisker is the left whisker of the suspensions. -/
theorem suspendCell_whiskerLeft {computad : OmegaComputad} {dim : Nat}
    (whiskeringCell : CellExpr computad (dim + 1)) (inner : CellExpr computad (dim + 2)) :
    suspendCell (CellExpr.whiskerLeft whiskeringCell inner)
      = CellExpr.whiskerLeft (suspendCell whiskeringCell) (suspendCell inner) := rfl

/-- `suspendCell` of a right whisker is the right whisker of the suspensions. -/
theorem suspendCell_whiskerRight {computad : OmegaComputad} {dim : Nat}
    (inner : CellExpr computad (dim + 2)) (whiskeringCell : CellExpr computad (dim + 1)) :
    suspendCell (CellExpr.whiskerRight inner whiskeringCell)
      = CellExpr.whiskerRight (suspendCell inner) (suspendCell whiskeringCell) := rfl

/-- `suspendCell` preserves the structural size (each generator counts one at either dimension). -/
theorem suspendCell_cellSize {computad : OmegaComputad} :
    {dim : Nat} → (cell : CellExpr computad dim) → cellSize (suspendCell cell) = cellSize cell
  | _, .ofMode _ => rfl
  | _, .gen _ _ _ => rfl
  | _, .id _ => rfl
  | _, .vcomp left right => by
      show cellSize (suspendCell left) + cellSize (suspendCell right) + 1
        = cellSize left + cellSize right + 1
      rw [suspendCell_cellSize left, suspendCell_cellSize right]
  | _, .whiskerLeft _ inner => by
      show cellSize (suspendCell inner) + 1 = cellSize inner + 1
      rw [suspendCell_cellSize inner]
  | _, .whiskerRight inner _ => by
      show cellSize (suspendCell inner) + 1 = cellSize inner + 1
      rw [suspendCell_cellSize inner]

/-! ## Boundary commutation — suspension commutes with the total boundaries

The globularity legs live at every successor dimension; the total-motive `SuspendBoundaryCommutes` is `True` at
dimension 0 (no boundary) and the two commutation equations at `dim+1`.  Proven by plain structural induction
(the `globularLegs_of_isGlobularCell` pattern): `gen`/`id` are `rfl`, `vcomp` chains the two subcell
hypotheses, and the whisker legs `congrArg` the inner hypothesis through the whisker's formal `vcomp`. -/

/-- The **boundary-commutation motive** — `True` at dimension 0, the two commutation equations
(`suspendCell (boundarySource cell) = boundarySource (suspendCell cell)` and the target dual) at `dim+1`.
Full `Nat` enumeration — propext-free. -/
def SuspendBoundaryCommutes {computad : OmegaComputad} :
    {dim : Nat} → CellExpr computad dim → Prop
  | 0, _ => True
  | _ + 1, cell =>
      suspendCell (boundarySource cell) = boundarySource (suspendCell cell)
      ∧ suspendCell (boundaryTarget cell) = boundaryTarget (suspendCell cell)

/-- ★ **Suspension commutes with the total boundaries** on every cell.  Structural induction: `ofMode` is
`True`; `gen`/`id` are `⟨rfl, rfl⟩` (the boundary read-off commutes with the generator raise on the nose);
`vcomp` picks the left source / right target commutation; the whisker legs push the inner commutation through
the whisker's formal `vcomp` by `congrArg`. -/
theorem suspendBoundaryCommutes_all {computad : OmegaComputad} :
    {dim : Nat} → (cell : CellExpr computad dim) → SuspendBoundaryCommutes cell := by
  intro dim cell
  induction cell with
  | ofMode _ => exact True.intro
  | gen _ _ _ _ _ => exact ⟨rfl, rfl⟩
  | id _ _ => exact ⟨rfl, rfl⟩
  | vcomp _ _ ihLeft ihRight => exact ⟨ihLeft.1, ihRight.2⟩
  | whiskerLeft whiskeringCell _ _ ihInner =>
      exact ⟨congrArg (CellExpr.vcomp (suspendCell whiskeringCell)) ihInner.1,
        congrArg (CellExpr.vcomp (suspendCell whiskeringCell)) ihInner.2⟩
  | whiskerRight _ whiskeringCell ihInner _ =>
      exact ⟨congrArg (fun boundary => CellExpr.vcomp boundary (suspendCell whiskeringCell)) ihInner.1,
        congrArg (fun boundary => CellExpr.vcomp boundary (suspendCell whiskeringCell)) ihInner.2⟩

/-- Suspension commutes with the SOURCE boundary at a successor dimension. -/
theorem suspendCell_boundarySource {computad : OmegaComputad} {dim : Nat}
    (cell : CellExpr computad (dim + 1)) :
    suspendCell (boundarySource cell) = boundarySource (suspendCell cell) :=
  (suspendBoundaryCommutes_all cell).1

/-- Suspension commutes with the TARGET boundary at a successor dimension. -/
theorem suspendCell_boundaryTarget {computad : OmegaComputad} {dim : Nat}
    (cell : CellExpr computad (dim + 1)) :
    suspendCell (boundaryTarget cell) = boundaryTarget (suspendCell cell) :=
  (suspendBoundaryCommutes_all cell).2

/-! ## Preservation: the free strict congruence is embedded by suspension (B1) -/

/-- ★ **Each strict-axiom row maps to its row one dimension up.**  `vcompAssoc` / the whisker functorialities /
the whisker units are pure `vcomp`/`whisker`/`id` shapes preserved by the `suspendCell` homomorphism; the two
unit rows and the Godement interchange need the boundary-commutation to align the `boundarySource` /
`boundaryTarget` arguments after suspension.  No linearize, no arithmetic — a syntactic row map. -/
theorem suspendStrictRow {computad : OmegaComputad} {dim : Nat}
    {cellAlpha cellBeta : CellExpr computad dim} (row : StrictAxiomRel computad cellAlpha cellBeta) :
    StrictAxiomRel (suspendComputad computad) (suspendCell cellAlpha) (suspendCell cellBeta) := by
  cases row with
  | vcompAssoc cellA cellB cellC =>
      exact StrictAxiomRel.vcompAssoc (suspendCell cellA) (suspendCell cellB) (suspendCell cellC)
  | vcompUnitLeft cellA =>
      show StrictAxiomRel (suspendComputad computad)
        (CellExpr.vcomp (CellExpr.id (suspendCell (boundarySource cellA))) (suspendCell cellA))
        (suspendCell cellA)
      rw [suspendCell_boundarySource]
      exact StrictAxiomRel.vcompUnitLeft (suspendCell cellA)
  | vcompUnitRight cellA =>
      show StrictAxiomRel (suspendComputad computad)
        (CellExpr.vcomp (suspendCell cellA) (CellExpr.id (suspendCell (boundaryTarget cellA))))
        (suspendCell cellA)
      rw [suspendCell_boundaryTarget]
      exact StrictAxiomRel.vcompUnitRight (suspendCell cellA)
  | whiskerLeftUnit whiskeringCell innerCell =>
      exact StrictAxiomRel.whiskerLeftUnit (suspendCell whiskeringCell) (suspendCell innerCell)
  | whiskerRightUnit innerCell whiskeringCell =>
      exact StrictAxiomRel.whiskerRightUnit (suspendCell innerCell) (suspendCell whiskeringCell)
  | whiskerLeftFunctorial whiskeringCell cellBeta cellGamma =>
      exact StrictAxiomRel.whiskerLeftFunctorial (suspendCell whiskeringCell)
        (suspendCell cellBeta) (suspendCell cellGamma)
  | whiskerRightFunctorial cellAlpha cellBeta whiskeringCell =>
      exact StrictAxiomRel.whiskerRightFunctorial (suspendCell cellAlpha)
        (suspendCell cellBeta) (suspendCell whiskeringCell)
  | interchange cellAlpha cellBeta =>
      show StrictAxiomRel (suspendComputad computad)
        (CellExpr.vcomp
          (CellExpr.whiskerRight (suspendCell cellAlpha) (suspendCell (boundarySource cellBeta)))
          (CellExpr.whiskerLeft (suspendCell (boundaryTarget cellAlpha)) (suspendCell cellBeta)))
        (CellExpr.vcomp
          (CellExpr.whiskerLeft (suspendCell (boundarySource cellAlpha)) (suspendCell cellBeta))
          (CellExpr.whiskerRight (suspendCell cellAlpha) (suspendCell (boundaryTarget cellBeta))))
      rw [suspendCell_boundarySource, suspendCell_boundaryTarget,
        suspendCell_boundarySource, suspendCell_boundaryTarget]
      exact StrictAxiomRel.interchange (suspendCell cellAlpha) (suspendCell cellBeta)

/-- ★ **PRESERVATION — the free strict congruence is FAITHFULLY embedded by suspension.**  If `a` and `b` are
free-strict convertible, their suspensions are convertible one dimension up: the 8-arm `SaturatedConvOver`
induction maps `ofRelation` through `suspendStrictRow` and each one-hole congruence through the `suspendCell`
homomorphism (each `rfl`).  This is the `→` of the memo's T3.susp. -/
theorem suspendPreservesStrictConv {computad : OmegaComputad} {dim : Nat}
    {cellAlpha cellBeta : CellExpr computad dim}
    (conv : SaturatedConvOver computad (StrictAxiomRel computad) cellAlpha cellBeta) :
    SaturatedConvOver (suspendComputad computad) (StrictAxiomRel (suspendComputad computad))
      (suspendCell cellAlpha) (suspendCell cellBeta) := by
  induction conv with
  | ofRelation row => exact SaturatedConvOver.ofRelation (suspendStrictRow row)
  | vcompCongrLeft cellBeta _ ih => exact SaturatedConvOver.vcompCongrLeft (suspendCell cellBeta) ih
  | vcompCongrRight cellAlpha _ ih => exact SaturatedConvOver.vcompCongrRight (suspendCell cellAlpha) ih
  | whiskerLeftCongr whiskeringCell _ ih =>
      exact SaturatedConvOver.whiskerLeftCongr (suspendCell whiskeringCell) ih
  | whiskerRightCongr whiskeringCell _ ih =>
      exact SaturatedConvOver.whiskerRightCongr (suspendCell whiskeringCell) ih
  | refl cell => exact SaturatedConvOver.refl (suspendCell cell)
  | symm _ ih => exact SaturatedConvOver.symm ih
  | trans _ _ ihLeft ihRight => exact SaturatedConvOver.trans ihLeft ihRight

/-! ## The suspended Steiner valuation and `linearize_suspend` (B2) -/

/-- The **suspended generator valuation** — the poles carry the degenerate table (never read: `suspendCell`
never produces a bare pole), the old modes' tables become the `⊥ → ⊤` 1-generators' tables
(`suspendGenValue 1 = modeValue`), and the old generators keep their tables one dimension up
(`suspendGenValue (k+2) = genValue (k+1)`).  This is the compatible shift that makes `linearize` invariant. -/
def suspendGenValue {computad : OmegaComputad} (valuation : ComputadValuation computad) :
    (dim : Nat) → suspendGenLabel computad dim → SteinerCell
  | 0, label => PEmpty.elim label
  | 1, label => valuation.modeValue label
  | k + 2, label => valuation.genValue (k + 1) label

/-- Every suspended generator table has the (unchanged) ambient length. -/
theorem suspendGenValue_length {computad : OmegaComputad} (valuation : ComputadValuation computad) :
    (dim : Nat) → (label : suspendGenLabel computad dim) →
    (suspendGenValue valuation dim label).coordinates.length = valuation.ambientDim
  | 0, label => PEmpty.elim label
  | 1, label => valuation.modeValueLength label
  | k + 2, label => valuation.genValueLength (k + 1) label

/-- The **suspended valuation** — same ambient basis (so `suspendTable` is length-preserving), degenerate pole
tables, the dimension-shifted generator tables. -/
def suspendValuation {computad : OmegaComputad} (valuation : ComputadValuation computad) :
    ComputadValuation (suspendComputad computad) where
  ambientDim := valuation.ambientDim
  modeValue := fun _pole => ⟨zeroVector valuation.ambientDim⟩
  genValue := suspendGenValue valuation
  modeValueLength := fun _pole => zeroVector_length valuation.ambientDim
  genValueLength := suspendGenValue_length valuation

/-- ★ **`linearize` is INVARIANT under suspension** — `linearize (suspendCell a) = linearize a`.  Because
`SteinerCell` is dimension-agnostic (single ambient basis), suspension leaves the top vector literally
unchanged: generators keep their tables (the valuation is shifted to match), identities stay degenerate,
composites add, whiskers project.  Structural induction; the leaf cases are `rfl` (the shifted valuation
reconciles the object-becomes-1-generator arm). -/
theorem linearize_suspend {computad : OmegaComputad} (valuation : ComputadValuation computad) :
    {dim : Nat} → (cell : CellExpr computad dim) →
    linearize (suspendValuation valuation) (suspendCell cell) = linearize valuation cell
  | _, .ofMode _ => rfl
  | _, .gen _ _ _ => rfl
  | _, .id _ => rfl
  | _, .vcomp left right => by
      show (⟨addCoordinates (linearize (suspendValuation valuation) (suspendCell left)).coordinates
          (linearize (suspendValuation valuation) (suspendCell right)).coordinates⟩ : SteinerCell)
        = ⟨addCoordinates (linearize valuation left).coordinates (linearize valuation right).coordinates⟩
      rw [linearize_suspend valuation left, linearize_suspend valuation right]
  | _, .whiskerLeft _ inner => linearize_suspend valuation inner
  | _, .whiskerRight inner _ => linearize_suspend valuation inner

/-- **`suspendTable` is the IDENTITY.**  The dimension-agnostic Steiner table is unchanged by suspension
(`linearize_suspend`), so the "table shift" the memo forecast is definitionally `id` — trivially injective
(the memo's arithmetic-reflection prerequisite, made sharp). -/
def suspendTable (table : SteinerCell) : SteinerCell := table

/-- `suspendTable` is injective (it is the identity). -/
theorem suspendTable_injective {tableLeft tableRight : SteinerCell}
    (equal : suspendTable tableLeft = suspendTable tableRight) : tableLeft = tableRight := equal

/-- ★ **Table equality REFLECTS down the suspension.**  If two suspended cells have equal tables, so do the
originals — because `linearize (suspendCell a) = linearize a` and `suspendTable = id` is injective.  The
arithmetic half of the memo's reflection route. -/
theorem linearize_reflects_along_suspend {computad : OmegaComputad}
    (valuation : ComputadValuation computad) {dim : Nat} (cellAlpha cellBeta : CellExpr computad dim)
    (tablesEqualUp :
      linearize (suspendValuation valuation) (suspendCell cellAlpha)
        = linearize (suspendValuation valuation) (suspendCell cellBeta)) :
    linearize valuation cellAlpha = linearize valuation cellBeta := by
  rw [linearize_suspend valuation cellAlpha, linearize_suspend valuation cellBeta] at tablesEqualUp
  exact tablesEqualUp

/-! ## Reflection of convertibility on the atom-word fragment (B2, arithmetic route) -/

/-- ★ **REFLECTION — suspension reflects convertibility on the atom-word fragment.**  If the suspensions of two
single-generator atom words are convertible one dimension up, so are the originals: soundness UP gives equal
suspended tables, `linearize_suspend` reflects them DOWN to equal original tables, and atom-word completeness
(`atomWord_conv_of_linearize_eq`) reconstructs convertibility — the memo's arithmetic-first reflection at the
free fragment, dodging syntactic fullness.  Scoped to `IsAtomWord` (whisker-free, single-generator), where
completeness holds. -/
theorem suspend_reflects_atomWordConv {dim : Nat}
    {cellAlpha cellBeta : CellExpr crownComputad (dim + 1)}
    (hAtomAlpha : IsAtomWord cellAlpha) (hAtomBeta : IsAtomWord cellBeta)
    (convUp : SaturatedConvOver (suspendComputad crownComputad)
      (StrictAxiomRel (suspendComputad crownComputad)) (suspendCell cellAlpha) (suspendCell cellBeta)) :
    SaturatedConvOver crownComputad (StrictAxiomRel crownComputad) cellAlpha cellBeta := by
  have tablesEqualUp :
      linearize (suspendValuation crownValuation) (suspendCell cellAlpha)
        = linearize (suspendValuation crownValuation) (suspendCell cellBeta) :=
    linearize_eq_of_saturatedConv (suspendValuation crownValuation) convUp
  have tablesEqual : linearize crownValuation cellAlpha = linearize crownValuation cellBeta :=
    linearize_reflects_along_suspend crownValuation cellAlpha cellBeta tablesEqualUp
  exact atomWord_conv_of_linearize_eq hAtomAlpha hAtomBeta tablesEqual

/-- ★★ **THE FAITHFUL EMBEDDING (scoped).**  On the single-generator atom-word fragment, at every dimension,
convertibility is preserved AND reflected by suspension: `a ~ b ↔ suspendCell a ~ suspendCell b`.  Preservation
is the generic `suspendPreservesStrictConv`; reflection is the arithmetic `suspend_reflects_atomWordConv`.  The
memo's T3.susp, honest scope named in the statement. -/
theorem suspend_faithful_atomWord {dim : Nat}
    {cellAlpha cellBeta : CellExpr crownComputad (dim + 1)}
    (hAtomAlpha : IsAtomWord cellAlpha) (hAtomBeta : IsAtomWord cellBeta) :
    SaturatedConvOver crownComputad (StrictAxiomRel crownComputad) cellAlpha cellBeta
      ↔ SaturatedConvOver (suspendComputad crownComputad)
          (StrictAxiomRel (suspendComputad crownComputad)) (suspendCell cellAlpha) (suspendCell cellBeta) :=
  ⟨suspendPreservesStrictConv, suspend_reflects_atomWordConv hAtomAlpha hAtomBeta⟩

/-! ## Eckmann-Hilton as structure (B3) -/

/-- ★ **INTERCHANGE `*_0 = *_1` (arithmetic).**  The horizontal Godement composite and the vertical composite
linearize to the SAME coordinate sum: `linearize (godementComp a b) = linearize (vcomp a b)` — by `rfl` (both
project their whisker legs to the main factors and add).  Eckmann-Hilton's interchange collapse, on the table
side. -/
theorem linearize_godementComp_eq_vcomp {computad : OmegaComputad} (valuation : ComputadValuation computad)
    {dim : Nat} (cellAlpha cellBeta : CellExpr computad (dim + 2)) :
    linearize valuation (godementComp cellAlpha cellBeta)
      = linearize valuation (CellExpr.vcomp cellAlpha cellBeta) := rfl

/-- ★ **COMMUTATIVITY (arithmetic Eckmann-Hilton).**  `linearize (godementComp a b) = linearize (godementComp
b a)` — decided by `addCoordinates_comm`, the SAME lemma the interchange soundness row discharges.
Eckmann-Hilton commutativity FALLS OUT of Int-addition commutativity; no bespoke argument. -/
theorem godementComp_linearize_comm {computad : OmegaComputad} (valuation : ComputadValuation computad)
    {dim : Nat} (cellAlpha cellBeta : CellExpr computad (dim + 2)) :
    linearize valuation (godementComp cellAlpha cellBeta)
      = linearize valuation (godementComp cellBeta cellAlpha) := by
  show (⟨addCoordinates (linearize valuation cellAlpha).coordinates
      (linearize valuation cellBeta).coordinates⟩ : SteinerCell)
    = ⟨addCoordinates (linearize valuation cellBeta).coordinates (linearize valuation cellAlpha).coordinates⟩
  exact congrArg SteinerCell.mk
    (addCoordinates_comm (linearize valuation cellAlpha).coordinates
      (linearize valuation cellBeta).coordinates)

/-- The vertical composite is likewise commutative on the table side (the doubly-degenerate collapse). -/
theorem vcomp_linearize_comm {computad : OmegaComputad} (valuation : ComputadValuation computad)
    {dim : Nat} (cellAlpha cellBeta : CellExpr computad (dim + 1)) :
    linearize valuation (CellExpr.vcomp cellAlpha cellBeta)
      = linearize valuation (CellExpr.vcomp cellBeta cellAlpha) := by
  show (⟨addCoordinates (linearize valuation cellAlpha).coordinates
      (linearize valuation cellBeta).coordinates⟩ : SteinerCell)
    = ⟨addCoordinates (linearize valuation cellBeta).coordinates (linearize valuation cellAlpha).coordinates⟩
  exact congrArg SteinerCell.mk
    (addCoordinates_comm (linearize valuation cellAlpha).coordinates
      (linearize valuation cellBeta).coordinates)

/-! ## Non-vacuity — a dim-2 cell suspended to dim-3, boundaries and table computed (B1) -/

/-- `suspendCell demoTwoCell` is a genuine dimension-3 cell (a dim-2 generator raised): size preserved. -/
theorem suspended_demoTwoCell_size :
    cellSize (suspendCell demoTwoCell) = cellSize demoTwoCell :=
  suspendCell_cellSize demoTwoCell

/-- ★ The suspended dim-3 cell's SOURCE boundary is the suspension of the original dim-2 cell's source boundary
(boundaries commute on a concrete cell). -/
theorem suspended_demoTwoCell_boundarySource :
    boundarySource (suspendCell demoTwoCell) = suspendCell (boundarySource demoTwoCell) :=
  (suspendCell_boundarySource demoTwoCell).symm

/-- ★ The suspended dim-3 cell's TARGET boundary is the suspension of the original's target boundary. -/
theorem suspended_demoTwoCell_boundaryTarget :
    boundaryTarget (suspendCell demoTwoCell) = suspendCell (boundaryTarget demoTwoCell) :=
  (suspendCell_boundaryTarget demoTwoCell).symm

/-- ★ **`suspendTable` is the identity, witnessed.**  The dim-3 generator `cellThreeA` and its dim-4 suspension
carry the SAME Steiner table `[1, 0, 0]` — suspension is table-invariant. -/
theorem suspended_cellThreeA_table :
    linearize (suspendValuation demoValuation) (suspendCell cellThreeA)
      = linearize demoValuation cellThreeA :=
  linearize_suspend demoValuation cellThreeA

/-- The suspended dim-4 cell's table computes to the same basis vector `[1, 0, 0]`. -/
example : (linearize (suspendValuation demoValuation) (suspendCell cellThreeA)).coordinates = [1, 0, 0] := rfl

/-- The suspended dim-3 cell's size computes to `1` (a raised generator). -/
example : cellSize (suspendCell demoTwoCell) = 1 := rfl

/-! ## OMEGA-3 r1 honesty markers (B5 — strictly factual) -/

/-- ★ **B1 — the three suspension maps + PRESERVATION are SHIPPED.**  `suspendComputad` / `suspendCell` /
`suspendValuation` (`suspendTable = id`) type-check zero-axiom; `suspendCell` is a size-preserving homomorphism
(`suspendCell_cellSize`, the four `rfl` computation lemmas) that commutes with the total boundaries
(`suspendCell_boundarySource` / `_boundaryTarget`); and `suspendPreservesStrictConv` embeds the free strict
congruence one dimension up via `suspendStrictRow`.  `= true`. -/
def fxOmega_suspensionPreservationShippedR1 : Bool := true

/-- ★ **B2 — `linearize_suspend` (= id `suspendTable`) + REFLECTION are SHIPPED.**  `linearize (suspendCell a)
= linearize a` (`linearize_suspend`), so `suspendTable` is the injective identity, table equality reflects DOWN
(`linearize_reflects_along_suspend`), and on the single-generator atom-word fragment convertibility itself
reflects (`suspend_reflects_atomWordConv`) — the faithful embedding `suspend_faithful_atomWord`.  The GENERAL
(whiskered / multi-generator) conv-reflection stays the honest OMEGA-2.5 / syntactic-fullness wall.  `= true`. -/
def fxOmega_suspensionArithmeticReflectionShippedR1 : Bool := true

/-- ★ **B3 — Eckmann-Hilton AS STRUCTURE is SHIPPED (arithmetic form).**  Interchange `*_0 = *_1`
(`linearize_godementComp_eq_vcomp`, `rfl`) and commutativity (`godementComp_linearize_comm`,
`vcomp_linearize_comm`, via `addCoordinates_comm`) — Eckmann-Hilton FALLS OUT of Int-addition commutativity,
the SAME lemma the interchange soundness row uses (the falsifiability clause passes: no bespoke argument).  The
conv-form Eckmann-Hilton (not merely equal tables) needs completeness on the doubly-degenerate fragment — the
OMEGA-3 r2 owe.  `= true`. -/
def fxOmega_eckmannHiltonArithmeticShippedR1 : Bool := true

/-- ★ **OMEGA-3 r1 rung state (B5).**  `= false` — NOT the full rung: r1 ships suspension (B1) + arithmetic
reflection at the free fragment (B2) + arithmetic Eckmann-Hilton (B3) + the ceiling-lift preservation
(`Omega/CeilingLift.lean`, B4).  The 2-round budget's r2 OWES: the general (whiskered / multi-generator)
convertibility reflection (the OMEGA-2.5 boundary-faithful full-chain table, an ADDITIVE sibling — NOT an r1
brick), the conv-form Eckmann-Hilton on the doubly-degenerate fragment, and the iterated n+k FORM-A ceiling
statement.  Set `true` only when those land. -/
def fxOmega_omega3Complete : Bool := false

end FX1Poly.Polygraph.Omega
