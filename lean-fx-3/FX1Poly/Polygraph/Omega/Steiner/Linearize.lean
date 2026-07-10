import FX1Poly.Polygraph.Omega.Carrier
import FX1Poly.Polygraph.Omega.Steiner.CoordinateArithmetic

/-! # Polygraph/Omega/Steiner/Linearize — the ν/basis map `CellExpr → SteinerCell` (OMEGA-2 r1, B2+B3)

★ The CROWN bridge: `linearize` sends a free `dim`-cell to its Steiner integer chain table.  This is
the ONE generic map that stitches the syntax carrier (`CellExpr n`, above the `isStrongSteiner`
interface line) to the arithmetic carrier (`SteinerCell = List Int`, below the line) — the
`inv`-argument the OMEGA-2 soundness fold (`Soundness.lean`) feeds through `SaturatedConvOver.recInto`.

## The dimension-agnostic flattened-chain representation (why `linearize (id a) = zeroCell`)

`SteinerCell` is a SINGLE integer vector (a fixed ambient basis), NOT a graded table, so `linearize`
is DIMENSION-AGNOSTIC in its codomain (matching `OmegaTwoLinearizeSoundnessShape`'s single
`SteinerCellCarrier`).  A cell's table records its NET top-dimensional generator content:

  * `ofMode` / `gen` — a chosen basis value (`modeValue` / `genValue`), the generator IS an atom.
  * **`id a` — the DEGENERATE (zero) table.**  An identity contributes NO new generator content, so
    `linearize (CellExpr.id a) = ⟨zeroVector ambientDim⟩`.  This is the honest arithmetic form of the
    memo's "ID HYPOTHESIS made a theorem": the memo's literal `linearize (id a) = linearize a` is
    dimensionally loose (recon JOB 1) — `id a` and `a` inhabit different graded components — but the
    LOAD-BEARING content ("identities are degenerate") is exactly `linearize_id`, and it is what makes
    the two unit laws cancel (`0 + linearize a = linearize a`).  The inherited OMEGA-1 conv-leg wall
    (the missing `id`-congruence) is INVISIBLE here: the soundness fold is a map-OUT (`recInto`), which
    never CONSTRUCTS an id-congruence — the hybrid-design payoff.
  * **`vcomp α β` — coordinate ADDITION.**  `linearize (vcomp α β) = ⟨addCoordinates (lin α) (lin β)⟩`.
    Composition IS addition (Steiner, arXiv:math/0403237); the shared boundary of a FREE composite is
    the degenerate identity table (zero), so `x + y - 0 = x + y` — no shared-boundary derivation from
    the ADC is needed on the free fragment (`linearize_vcomp_composeAt` states the `composeAtDimension`
    form against the shipped substrate).
  * **`whiskerLeft w β` / `whiskerRight α w` — projection to the MAIN factor.**  Whiskering by a lower
    cell `w` contributes zero NET top content (w appears in both source and target of the whisker), so
    the whisker's table is the main cell's table.

Every output has length `ambientDim` (`linearize_length`), so all coordinate arithmetic inside one
dimension is exact (no truncation).

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

open FX1Poly.Polygraph.Steiner

/-! ## The valuation — the generating data of a Steiner realization -/

/-- A **computad valuation** — the free data a Steiner realization needs: an ambient basis size and
a chosen chain table for each mode and each generator, all of that common ambient length.  (The full
`AugmentedDirectedComplex` realization refines this with the boundary matrices; the free-fragment
`linearize` needs only the generator values.)  Uniform-Pi fields (no mixed implicit/explicit). -/
structure ComputadValuation (computad : OmegaComputad) where
  /-- The common ambient basis size — every table has this length. -/
  ambientDim : Nat
  /-- The chain table of each 0-cell (mode). -/
  modeValue : computad.modeCarrier → SteinerCell
  /-- The chain table (basis atom) of each generator at each dimension. -/
  genValue : (dim : Nat) → computad.genLabel dim → SteinerCell
  /-- Every mode table has the ambient length. -/
  modeValueLength : (mode : computad.modeCarrier) →
    (modeValue mode).coordinates.length = ambientDim
  /-- Every generator table has the ambient length. -/
  genValueLength : (dim : Nat) → (label : computad.genLabel dim) →
    (genValue dim label).coordinates.length = ambientDim

/-! ## The linearize map -/

/-- ★ **The ν / basis map** `linearize : CellExpr computad dim → SteinerCell` relative to a
valuation — the CROWN bridge.  Constant `SteinerCell` motive (dimension-agnostic codomain), a
structural fold over the six constructors: modes/generators to their chosen tables, identities to the
degenerate zero table, vertical composites to coordinate addition, whiskers to the main factor. -/
def linearize {computad : OmegaComputad} (valuation : ComputadValuation computad) :
    {dim : Nat} → CellExpr computad dim → SteinerCell
  | _, .ofMode mode => valuation.modeValue mode
  | _, .gen (dim := labelDim) label _ _ => valuation.genValue (labelDim + 1) label
  | _, .id _ => ⟨zeroVector valuation.ambientDim⟩
  | _, .vcomp leftCell rightCell =>
      ⟨addCoordinates (linearize valuation leftCell).coordinates
        (linearize valuation rightCell).coordinates⟩
  | _, .whiskerLeft _ mainCell => linearize valuation mainCell
  | _, .whiskerRight mainCell _ => linearize valuation mainCell

/-! ## The computation lemmas (B3 — the homomorphism legs, each `rfl`) -/

/-- `linearize` on a 0-cell reads off the mode table. -/
theorem linearize_ofMode {computad : OmegaComputad} (valuation : ComputadValuation computad)
    (mode : computad.modeCarrier) :
    linearize valuation (CellExpr.ofMode mode) = valuation.modeValue mode := rfl

/-- `linearize` on a generator reads off its basis table. -/
theorem linearize_gen {computad : OmegaComputad} (valuation : ComputadValuation computad)
    {dim : Nat} (label : computad.genLabel (dim + 1)) (source target : CellExpr computad dim) :
    linearize valuation (CellExpr.gen label source target) = valuation.genValue (dim + 1) label := rfl

/-- ★ **The ID theorem (arithmetic form).**  An identity cell linearizes to the DEGENERATE (zero)
table — identities carry no top-dimensional generator content.  The honest, dimensionally-sound form
of the memo's "linearize (id a) = linearize a"; the literal equality holds exactly when `linearize a`
is itself the zero table.  This single fact discharges both unit-law rows in the soundness fold. -/
theorem linearize_id {computad : OmegaComputad} (valuation : ComputadValuation computad)
    {dim : Nat} (cell : CellExpr computad dim) :
    linearize valuation (CellExpr.id cell) = ⟨zeroVector valuation.ambientDim⟩ := rfl

/-- ★ **Composition IS addition.**  A vertical composite linearizes to the coordinate SUM of its
factors (Steiner).  Definitional. -/
theorem linearize_vcomp {computad : OmegaComputad} (valuation : ComputadValuation computad)
    {dim : Nat} (leftCell rightCell : CellExpr computad (dim + 1)) :
    linearize valuation (CellExpr.vcomp leftCell rightCell)
      = ⟨addCoordinates (linearize valuation leftCell).coordinates
          (linearize valuation rightCell).coordinates⟩ := rfl

/-- Left-whiskering projects to the main factor (the whiskering cell has zero net top content). -/
theorem linearize_whiskerLeft {computad : OmegaComputad} (valuation : ComputadValuation computad)
    {dim : Nat} (whiskeringCell : CellExpr computad (dim + 1)) (mainCell : CellExpr computad (dim + 2)) :
    linearize valuation (CellExpr.whiskerLeft whiskeringCell mainCell) = linearize valuation mainCell := rfl

/-- Right-whiskering projects to the main factor. -/
theorem linearize_whiskerRight {computad : OmegaComputad} (valuation : ComputadValuation computad)
    {dim : Nat} (mainCell : CellExpr computad (dim + 2)) (whiskeringCell : CellExpr computad (dim + 1)) :
    linearize valuation (CellExpr.whiskerRight mainCell whiskeringCell) = linearize valuation mainCell := rfl

/-! ## The length invariant -/

/-- **Every linearize table has the ambient length** — the exactness invariant that keeps coordinate
arithmetic inside one dimension from truncating.  Structural induction: modes/generators by the
valuation length fields, identities by `zeroVector_length`, composites by `addCoordinates_length_eq`
(equal-length operands), whiskers by the inductive hypothesis. -/
theorem linearize_length {computad : OmegaComputad} (valuation : ComputadValuation computad) :
    {dim : Nat} → (cell : CellExpr computad dim) →
    (linearize valuation cell).coordinates.length = valuation.ambientDim
  | _, .ofMode mode => valuation.modeValueLength mode
  | _, .gen (dim := labelDim) label _ _ => valuation.genValueLength (labelDim + 1) label
  | _, .id _ => zeroVector_length valuation.ambientDim
  | _, .vcomp leftCell rightCell => by
      show (addCoordinates (linearize valuation leftCell).coordinates
        (linearize valuation rightCell).coordinates).length = valuation.ambientDim
      have leftLength := linearize_length valuation leftCell
      have rightLength := linearize_length valuation rightCell
      exact (addCoordinates_length_eq _ _ (leftLength.trans rightLength.symm)).trans leftLength
  | _, .whiskerLeft _ mainCell => linearize_length valuation mainCell
  | _, .whiskerRight mainCell _ => linearize_length valuation mainCell

/-! ## The `composeAtDimension` connection (B3 — the shipped substrate form) -/

/-- ★ **The homomorphism leg against the shipped `composeAtDimension` substrate.**  A vertical
composite equals `composeAtDimension left right shared` with `shared` the DEGENERATE identity table
`⟨zeroVector ambientDim⟩` — so on the free fragment the explicit shared-boundary argument of the
shipped `composeAtDimension` (`Steiner/CellCoordinates.lean:88`) is the zero table, and
`x + y - 0 = x + y`.  Composition = truncated addition, exactly as the memo forecast, with the
shared-boundary crux DISCHARGED (it is degenerate) on the free fragment. -/
theorem linearize_vcomp_composeAt {computad : OmegaComputad} (valuation : ComputadValuation computad)
    {dim : Nat} (leftCell rightCell : CellExpr computad (dim + 1)) :
    linearize valuation (CellExpr.vcomp leftCell rightCell)
      = composeAtDimension (linearize valuation leftCell) (linearize valuation rightCell)
          ⟨zeroVector valuation.ambientDim⟩ := by
  rw [linearize_vcomp]
  show (⟨addCoordinates (linearize valuation leftCell).coordinates
      (linearize valuation rightCell).coordinates⟩ : SteinerCell)
    = ⟨subtractCoordinates (addCoordinates (linearize valuation leftCell).coordinates
        (linearize valuation rightCell).coordinates) (zeroVector valuation.ambientDim)⟩
  have sumLength :
      (addCoordinates (linearize valuation leftCell).coordinates
        (linearize valuation rightCell).coordinates).length = valuation.ambientDim :=
    (addCoordinates_length_eq _ _
      ((linearize_length valuation leftCell).trans (linearize_length valuation rightCell).symm)).trans
      (linearize_length valuation leftCell)
  rw [← sumLength, subtractCoordinates_zeroVector_right]

end FX1Poly.Polygraph.Omega
