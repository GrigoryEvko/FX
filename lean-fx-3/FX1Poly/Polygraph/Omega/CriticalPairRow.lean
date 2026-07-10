import FX1Poly.Polygraph.Omega.CongruenceWithId
import FX1Poly.Polygraph.Omega.StrictAxioms
import FX1Poly.Polygraph.Omega.NonVacuity

/-! # Polygraph/Omega/CriticalPairRow — the dim-3 critical-pair row family (OMEGA-4 r1, B1)

★ **The FIRST dim-3 row family — the OMEGA-1 `CellRelOver` pattern one dimension up, VERBATIM.**  A Squier
critical pair, resolved to a distinguished valley, is a generating 3-cell: a convertibility between two
PARALLEL 2-cells (the two reduction legs).  The recon verdict is that this needs **no new structure** — the
dim-3 row family is `CellRelOver computad` firing at `dim = 2` (relating two `CellExpr computad 2`), closed
by the idCongr-extended congruence `SaturatedConvOverWithId` (whose `idCongr` is exactly the 2-cell -> 3-cell
dimension bump).  This file supplies the packaging that turns a critical overlap into such a row and fires it
as a genuine 3-cell.

## Globularity discipline (the recon's risk #2, ENFORCED)

The free `gen` / `vcomp` admit legs that are NOT a parallel pair; a genuine 3-cell must be GLOBULAR — the two
legs `IsParallelPair` at dim 2: co-initial (same source 1-cell `peak`) AND co-final (same target 1-cell
`valley`).  `CriticalPairRow` carries the four boundary equations as FIELDS, so a row is globular by
construction; `criticalPairRow_isParallelPair` reads the `IsParallelPair` off them.  The
`criticalPairRowOfParallelLegs` smart constructor builds a row from any two legs plus a bare
`IsParallelPair` proof (the critical-pair-to-row constructor).

## The 3-cell (the FIRST genuine dim-3 congruence content over the row family)

`criticalPairRel row` is the singleton `CellRelOver` firing only on `(leftLeg, rightLeg)`.
`criticalPairThreeCell row : SaturatedConvOverWithId computad (criticalPairRel row) leftLeg rightLeg` is the
generating 3-cell — `ofRelation` on the fired row.  The dim-3 congruence MUST be the 11-constructor
`SaturatedConvOverWithId` (NOT the 8-constructor `SaturatedConvOver`): only the sibling's `idCongr` bumps a
dim-2 convertibility to the dim-3 identity cells; the 8-ctor relation reopens the OMEGA-1 `vcompIdLeft` jam.

## Non-vacuity — a REAL globular row from a REAL critical pair

The archetypal PARALLEL critical pair of two-dimensional rewriting is the **Godement / interchange** overlap:
the two whisker-orders of a horizontal composite (`interchangeCriticalRow` over the demo computad).  Its two
sides share source `(src alpha) . (src beta)` and target `(tgt alpha) . (tgt beta)` BY CONSTRUCTION (the
boundary fields discharge by `rfl`), so it is a genuine globular `CriticalPairRow`; `interchangeThreeCell`
is a REAL dim-3 3-cell, and the two legs are structurally DISTINCT (`interchangeCriticalRow_legsDistinct`
computes `false`).  This is `StrictAxiomRel.interchange` re-read as a critical-pair 3-cell (the interchange
is simultaneously a strict-omega axiom AND the canonical parallel critical pair).

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! ## The globular critical-pair row -/

/-- ★ A **globular critical-pair row** at base dimension `dim`: two reduction legs (`(dim+1)`-cells) that are
GLOBULAR — co-initial at a common `peak` `dim`-cell and co-final at a common `valley` `dim`-cell.  The four
boundary equations are FIELDS, so a row is a parallel pair by construction (the recon's extrinsic globularity
discipline).  At `dim = 2` (legs are 2-cells, peak/valley are 1-cells) this is the Squier critical-pair
datum: the branching `peak` resolved through two 2-cell legs to a distinguished `valley`. -/
structure CriticalPairRow (computad : OmegaComputad) (dim : Nat) where
  /-- The overlap / branching source `dim`-cell shared by both legs. -/
  peak : CellExpr computad dim
  /-- The distinguished common reduct `dim`-cell both legs reach. -/
  valley : CellExpr computad dim
  /-- The left reduction leg (a `(dim+1)`-cell). -/
  leftLeg : CellExpr computad (dim + 1)
  /-- The right reduction leg. -/
  rightLeg : CellExpr computad (dim + 1)
  /-- The left leg is co-initial at `peak`. -/
  leftLegSource : boundarySource leftLeg = peak
  /-- The left leg is co-final at `valley`. -/
  leftLegTarget : boundaryTarget leftLeg = valley
  /-- The right leg is co-initial at `peak`. -/
  rightLegSource : boundarySource rightLeg = peak
  /-- The right leg is co-final at `valley`. -/
  rightLegTarget : boundaryTarget rightLeg = valley

/-- ★ **The two legs of a globular critical-pair row are a parallel pair** — the extrinsic globularity of the
3-cell, read off the four boundary fields (co-initial: both sources are `peak`; co-final: both targets are
`valley`). -/
theorem criticalPairRow_isParallelPair {computad : OmegaComputad} {dim : Nat}
    (row : CriticalPairRow computad dim) : IsParallelPair row.leftLeg row.rightLeg :=
  ⟨row.leftLegSource.trans row.rightLegSource.symm,
   row.leftLegTarget.trans row.rightLegTarget.symm⟩

/-- ★ **The critical-pair-to-row constructor** — build a globular row from two legs plus a bare
`IsParallelPair` proof.  The peak / valley are read off the LEFT leg's boundaries; the right-leg equations are
the two halves of the parallelism.  This is the map from a raw overlap (two legs known parallel) to the row
datum. -/
def criticalPairRowOfParallelLegs {computad : OmegaComputad} {dim : Nat}
    (leftLeg rightLeg : CellExpr computad (dim + 1))
    (parallel : IsParallelPair leftLeg rightLeg) : CriticalPairRow computad dim where
  peak := boundarySource leftLeg
  valley := boundaryTarget leftLeg
  leftLeg := leftLeg
  rightLeg := rightLeg
  leftLegSource := rfl
  leftLegTarget := rfl
  rightLegSource := parallel.1.symm
  rightLegTarget := parallel.2.symm

/-! ## The row as a `CellRelOver` and the generating 3-cell -/

/-- The **singleton relation of a critical-pair row** — a `CellRelOver` firing only on the row's two legs.
The dim-3 row family is exactly this: a `CellRelOver computad` inhabited at one parallel pair. -/
inductive CriticalPairRel {computad : OmegaComputad} {dim : Nat} (row : CriticalPairRow computad dim) :
    {d : Nat} → CellExpr computad d → CellExpr computad d → Prop where
  /-- Fire the row on its two legs. -/
  | fire : CriticalPairRel row row.leftLeg row.rightLeg

/-- The critical-pair row packaged as a `CellRelOver` (the shape `SaturatedConvOverWithId` closes). -/
def criticalPairRel {computad : OmegaComputad} {dim : Nat} (row : CriticalPairRow computad dim) :
    CellRelOver computad :=
  fun cellAlpha cellBeta => CriticalPairRel row cellAlpha cellBeta

/-- ★ **The generating 3-cell of a critical-pair row** — its two legs are convertible under the
idCongr-extended congruence, by firing the row through `ofRelation`.  This is the FIRST genuine dim-3
congruence content over the row family: a convertibility between two parallel 2-cells (when `dim = 1`),
i.e. a 3-cell. -/
def criticalPairThreeCell {computad : OmegaComputad} {dim : Nat} (row : CriticalPairRow computad dim) :
    SaturatedConvOverWithId computad (criticalPairRel row) row.leftLeg row.rightLeg :=
  SaturatedConvOverWithId.ofRelation CriticalPairRel.fire

/-! ## Non-vacuity — the Godement / interchange critical pair as a globular dim-3 row -/

/-- ★ The **Godement / interchange critical-pair row** over the demo computad: the two whisker-orders of the
horizontal composite of `twoCellGen` and `twoCellId`.  The archetypal PARALLEL critical pair of
two-dimensional rewriting — both sides share source `(src alpha) . (src beta)` and target
`(tgt alpha) . (tgt beta)`, so the four boundary fields discharge by `rfl`.  This is `StrictAxiomRel.interchange`
re-read as a critical-pair row. -/
def interchangeCriticalRow : CriticalPairRow demoComputad 1 where
  peak := CellExpr.vcomp (boundarySource twoCellGen) (boundarySource twoCellId)
  valley := CellExpr.vcomp (boundaryTarget twoCellGen) (boundaryTarget twoCellId)
  leftLeg := CellExpr.vcomp (CellExpr.whiskerRight twoCellGen (boundarySource twoCellId))
    (CellExpr.whiskerLeft (boundaryTarget twoCellGen) twoCellId)
  rightLeg := CellExpr.vcomp (CellExpr.whiskerLeft (boundarySource twoCellGen) twoCellId)
    (CellExpr.whiskerRight twoCellGen (boundaryTarget twoCellId))
  leftLegSource := rfl
  leftLegTarget := rfl
  rightLegSource := rfl
  rightLegTarget := rfl

/-- ★ **A REAL dim-3 3-cell from a REAL critical pair.**  The interchange row fired through
`criticalPairThreeCell` — a genuine `SaturatedConvOverWithId` convertibility between the two parallel legs
(the two whisker orders of the horizontal composite). -/
def interchangeThreeCell :
    SaturatedConvOverWithId demoComputad (criticalPairRel interchangeCriticalRow)
      interchangeCriticalRow.leftLeg interchangeCriticalRow.rightLeg :=
  criticalPairThreeCell interchangeCriticalRow

/-- The interchange row is globular — its two legs are a parallel pair (non-vacuity of the globularity
discipline at dim 2). -/
theorem interchangeCriticalRow_isParallelPair :
    IsParallelPair interchangeCriticalRow.leftLeg interchangeCriticalRow.rightLeg :=
  criticalPairRow_isParallelPair interchangeCriticalRow

#eval cellSize interchangeCriticalRow.leftLeg

/-- ★ The two legs are structurally DISTINCT (a right-whisker-first vs left-whisker-first composite): the
3-cell genuinely identifies non-equal 2-cells (non-vacuity of the congruence content). -/
theorem interchangeCriticalRow_legsDistinct :
    cellBeq demoModeBeq demoGenBeq interchangeCriticalRow.leftLeg interchangeCriticalRow.rightLeg = false :=
  rfl

end FX1Poly.Polygraph.Omega
