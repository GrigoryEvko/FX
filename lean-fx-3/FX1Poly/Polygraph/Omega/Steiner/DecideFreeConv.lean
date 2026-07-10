import FX1Poly.Polygraph.Omega.SteinerFoundation.DecidableCellEq
import FX1Poly.Polygraph.Omega.Steiner.Soundness

/-! # Polygraph/Omega/Steiner/DecideFreeConv — the sound semi-decider + non-vacuity (OMEGA-2 r1, B5)

★ **The free-omega word problem, one SOUND side.**  `decideFreeConvSound` tests table equality —
`linearize valuation a == linearize valuation b` via the shipped structural `DecidableEq SteinerCell`
(`Steiner/DecidableCellEq.lean`).  By CROWN soundness (`linearizeSoundness`) table equality is a
NECESSARY condition for convertibility, so table INEQUALITY soundly REFUTES convertibility
(`not_conv_of_linearize_ne`).  This is the honest r1 deliverable: a sound semi-decider that never lies
in the negative direction.  It is NOT claimed complete — equal tables do not (yet) imply conv; the
converse (reconstruct / excision-of-extremals) is the OMEGA-2 r3 completeness item, and at n=2 FREE-7
(`SpineTraceDecision`) is the complete oracle on the admitted intersection (r2 agreement).

## Non-vacuity ledger (per the memo B5 discipline)

A concrete demo computad with a dimension-3 free cell, exercised end to end:
  * `demo_linearize_cellThreeA` — the dim-3 cell's Steiner table `#eval`s to `[1, 0, 0]` (world-first-(c)
    substrate is inhabited and computes).
  * `demo_conv_tables_equal` — two CONV-related dim-3 cells (`vcomp (id (src a)) a ~ a`, an ACTUAL
    `SaturatedConvOver` derivation via the `vcompUnitLeft` row) have EQUAL tables, PROVEN through the
    soundness fold.
  * `demo_distinct_tables` — two structurally-distinct dim-3 generators have DISTINCT tables, hence are
    provably NON-convertible (`demo_cellsThree_not_conv`).

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

open FX1Poly.Polygraph.Steiner

/-! ## The sound semi-decider -/

/-- **The free-fragment word-problem semi-decider** — table equality, a SOUND necessary condition for
convertibility (decided by the shipped structural `DecidableEq SteinerCell`). -/
def decideFreeConvSound {computad : OmegaComputad} (valuation : ComputadValuation computad)
    {dim : Nat} (cellAlpha cellBeta : CellExpr computad dim) : Bool :=
  decide (linearize valuation cellAlpha = linearize valuation cellBeta)

/-- ★ **The sound refutation** — DISTINCT tables soundly refute convertibility (the contrapositive of
CROWN soundness).  This is what the semi-decider proves when it answers `false`: the two cells are
genuinely NON-convertible under the free strict congruence. -/
theorem not_conv_of_linearize_ne {computad : OmegaComputad} (valuation : ComputadValuation computad)
    {dim : Nat} {cellAlpha cellBeta : CellExpr computad dim}
    (tablesDiffer : linearize valuation cellAlpha ≠ linearize valuation cellBeta) :
    ¬ SaturatedConvOver computad (StrictAxiomRel computad) cellAlpha cellBeta :=
  fun conv => tablesDiffer (linearize_eq_of_saturatedConv valuation conv)

/-! ## The demo computad and valuation (non-vacuity) -/

/-- A demo omega-computad: two modes, two generator labels at every dimension. -/
def steinerDemoComputad : OmegaComputad where
  modeCarrier := Bool
  genLabel := fun _ => Bool

/-- A demo valuation into a length-3 ambient basis; distinguishes the two dimension-3 generators. -/
def demoValuation : ComputadValuation steinerDemoComputad where
  ambientDim := 3
  modeValue := fun _ => ⟨[0, 0, 1]⟩
  genValue := fun labelDim label =>
    ⟨[if (labelDim == 3 && label) then 1 else 0,
      if (labelDim == 3 && !label) then 1 else 0, 0]⟩
  modeValueLength := fun _ => rfl
  genValueLength := fun _ _ => rfl

/-! ## A concrete dimension-3 free cell (the tower) -/

/-- A demo 0-cell. -/
def demoZeroCell : CellExpr steinerDemoComputad 0 := CellExpr.ofMode false

/-- A demo 1-generator. -/
def demoOneCell : CellExpr steinerDemoComputad 1 := CellExpr.gen true demoZeroCell demoZeroCell

/-- A demo 2-generator. -/
def demoTwoCell : CellExpr steinerDemoComputad 2 := CellExpr.gen true demoOneCell demoOneCell

/-- ★ A demo dimension-3 generator (label `true`) — world-first-(c) substrate, inhabited. -/
def cellThreeA : CellExpr steinerDemoComputad 3 := CellExpr.gen true demoTwoCell demoTwoCell

/-- A second demo dimension-3 generator (label `false`) — structurally distinct from `cellThreeA`. -/
def cellThreeB : CellExpr steinerDemoComputad 3 := CellExpr.gen false demoTwoCell demoTwoCell

/-! ## The non-vacuity facts -/

/-- The dim-3 cell's Steiner table computes to the basis vector `[1, 0, 0]`. -/
theorem demo_linearize_cellThreeA :
    (linearize demoValuation cellThreeA).coordinates = [1, 0, 0] := rfl

/-- The second dim-3 cell's table computes to the basis vector `[0, 1, 0]`. -/
theorem demo_linearize_cellThreeB :
    (linearize demoValuation cellThreeB).coordinates = [0, 1, 0] := rfl

/-- ★ **Two CONV-related dim-3 cells have EQUAL tables** — an ACTUAL `SaturatedConvOver` derivation
(the `vcompUnitLeft` row) mapped through the soundness fold.  The end-to-end non-vacuity of the CROWN. -/
theorem demo_conv_tables_equal :
    linearize demoValuation (CellExpr.vcomp (CellExpr.id (boundarySource cellThreeA)) cellThreeA)
      = linearize demoValuation cellThreeA :=
  linearize_eq_of_saturatedConv demoValuation
    (SaturatedConvOver.ofRelation (StrictAxiomRel.vcompUnitLeft cellThreeA))

/-- Two structurally-distinct dim-3 generators have DISTINCT tables. -/
theorem demo_distinct_tables :
    linearize demoValuation cellThreeA ≠ linearize demoValuation cellThreeB := by
  intro tablesEqual
  have hcoords : ([1, 0, 0] : List Int) = [0, 1, 0] := by
    rw [← demo_linearize_cellThreeA, ← demo_linearize_cellThreeB]
    exact congrArg SteinerCell.coordinates tablesEqual
  injection hcoords with headEqual _
  injection headEqual with headNatEqual
  exact Nat.noConfusion headNatEqual

/-- ★ **Two non-conv dim-3 cells are provably NON-convertible** — distinct tables refute conv. -/
theorem demo_cellsThree_not_conv :
    ¬ SaturatedConvOver steinerDemoComputad (StrictAxiomRel steinerDemoComputad) cellThreeA cellThreeB :=
  not_conv_of_linearize_ne demoValuation demo_distinct_tables

/-! ## The non-vacuity evals -/

/-- The dim-3 cell's table (`[1, 0, 0]`). -/
example : (linearize demoValuation cellThreeA).coordinates = [1, 0, 0] := rfl

/-- Conv-related cells: EQUAL tables (`decideFreeConvSound = true`). -/
example : decideFreeConvSound demoValuation
    (CellExpr.vcomp (CellExpr.id (boundarySource cellThreeA)) cellThreeA) cellThreeA = true := rfl

/-- Non-conv cells: DISTINCT tables (`decideFreeConvSound = false`). -/
example : decideFreeConvSound demoValuation cellThreeA cellThreeB = false := rfl

end FX1Poly.Polygraph.Omega
