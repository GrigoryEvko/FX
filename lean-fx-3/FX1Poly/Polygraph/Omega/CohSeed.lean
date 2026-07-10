import FX1Poly.Polygraph.Omega.PsContext
import FX1Poly.Polygraph.Omega.CriticalPairRow

/-! # Polygraph/Omega/CohSeed — the CaTT coherence rule as a checked-ps + parallel-boundary generator seed
    (OMEGA-6 r1, B2)

★ **The `coh` rule of CaTT, seeded over the Omega carrier — clone of `CriticalPairRow`, one admissibility gate
richer.**  Finster–Mimram's `coh` rule: given a checked ps-context `Γ` and a PARALLEL pair of boundary terms
`(u, v)` over `Γ`, you get a generating **coherence cell** `coh_{Γ, u⇒v} : u → v`.  This is precisely a
*filler for a parallel pair arising from a pasting scheme* — the admissibility gate (only parallel pairs over a
valid ps-context get a filler) is exactly what makes CaTT WEAK ω rather than the free globular set.

## The r1-shippable form (`CohRow`, cloning `CriticalPairRow`)

A `CohRow` bundles the CaTT `coh` premises the r1 layer can decide / carry:

  * a `PsContextRow` with a `psContextCheck _ = true` proof — the **checked ps-context** gate (the B1
    decidable ps-judgment);
  * a `source` / `target` pair of `dim`-cells with an `IsParallelPair` proof — the **globular boundary** gate
    (co-initial + co-final, exactly the `CriticalPairRow` field-carried globularity discipline).

and the **fire** `cohGenerator`: `CellExpr.gen cohLabel source target` — a fresh generating `(dim+1)`-cell with
the checked parallel boundary.  Its boundaries compute back to `source` / `target` (`rfl`), and it is
`IsGlobularCell` whenever `source` / `target` are (globularity is FREE from `boundaryParallel`, the exact
`Carrier.lean` `globularLegs_of_isGlobularCell`-style read-off one notch over).

## Semantic anchor (cite, do not re-derive)

`GlobularContraction` (`TwoCategory/GlobularSet.lean`) is Leinster's contraction — a chosen filler
`(n+1)`-cell for EVERY parallel pair (`filler` / `fillerSource` / `fillerTarget`).  The CaTT `coh` rule is the
*pasting-scheme-restricted* contraction (Batanin–Leinster): only parallel pairs over a VALID ps-context get a
filler.  The `CohRow` seed is exactly "the ps-gated fragment of the contraction"; the full contractible-operad
algebra is deferred (`GlobularSet.lean` markers `fxMode_hasInitialContractibleOperadAlgebras := false`).

## What r1 does NOT enforce (named honestly, deferred to OMEGA-7)

r1's `CohRow` carries the ps-check gate and the parallelism gate, but NOT the CaTT **fullness** side-condition
("every variable of `Γ` occurs in the boundary type"), and NOT the TYPED LINK that `source` / `target` actually
live OVER `psContext` — both need the typed telescope + substitution, i.e. the OMEGA-7 pasting engine.  In r1
the ps-context and the boundary are INDEPENDENT fields; the witnesses below choose the morally-correct
ps-context for each boundary (the disk for a 2-cell coherence, the horizontal-composite scheme for the
interchange), but the checker does not verify the boundary is typeable over it.  That cross-check is the
OMEGA-7 "substitution = pasting" gate.

## Non-vacuity — two REAL coherence generators

  1. `twoGlobeCohGenerator` — the single-2-cell **disk** ps-context filled by the parallel 1-cell pair
     `(oneCellGen, oneCellId)`; a genuine `CellExpr demoComputad 2`, globular by construction.
  2. `interchangeCohGenerator` — the **horizontal-composite** ps-context filled by `interchangeCriticalRow`'s
     two whisker-order legs (the ready-made `interchangeCriticalRow_isParallelPair` parallelism witness); a
     genuine `CellExpr demoComputad 3` whose two boundaries are the STRUCTURALLY DISTINCT interchange legs —
     the interchange coherence IS a CaTT `coh` cell.

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! ## The coherence row -/

/-- ★ A **coherence row** at base dimension `dim` — the CaTT `coh` premises the r1 layer carries: a checked
ps-context (the `psContextChecks` gate), a coherence label, and a PARALLEL `source` / `target` boundary (the
`boundaryParallel` globularity gate).  Cloning `CriticalPairRow`: the parallelism is a FIELD, so a row is a
globular filler datum by construction.  The typed link between the boundary and the ps-context (fullness +
"boundary lives over `Γ`") is the OMEGA-7 pasting gate, NOT carried here. -/
structure CohRow (computad : OmegaComputad) (dim : Nat) where
  /-- The pasting-scheme context the coherence is built over. -/
  psContext : PsContextRow
  /-- The ps-context passes the decidable ps-judgment (B1's `psContextCheck`). -/
  psContextChecks : psContextCheck psContext = true
  /-- The generating label the coherence cell draws from. -/
  cohLabel : computad.genLabel (dim + 1)
  /-- The source boundary `dim`-cell. -/
  source : CellExpr computad dim
  /-- The target boundary `dim`-cell. -/
  target : CellExpr computad dim
  /-- The boundary is a parallel pair (co-initial + co-final) — the globularity gate. -/
  boundaryParallel : IsParallelPair source target

/-! ## The coherence generator (the fire) -/

/-- ★ **The generating coherence cell of a coherence row** — a fresh generating `(dim+1)`-cell with the
checked parallel boundary, `CellExpr.gen cohLabel source target`.  The CaTT `coh_{Γ, source⇒target}`. -/
def cohGenerator {computad : OmegaComputad} {dim : Nat} (row : CohRow computad dim) :
    CellExpr computad (dim + 1) :=
  CellExpr.gen row.cohLabel row.source row.target

/-- The coherence generator's source boundary is the row's declared `source` (read off `gen`). -/
theorem cohGenerator_boundarySource {computad : OmegaComputad} {dim : Nat} (row : CohRow computad dim) :
    boundarySource (cohGenerator row) = row.source := rfl

/-- The coherence generator's target boundary is the row's declared `target`. -/
theorem cohGenerator_boundaryTarget {computad : OmegaComputad} {dim : Nat} (row : CohRow computad dim) :
    boundaryTarget (cohGenerator row) = row.target := rfl

/-- ★ **The row-generation seed**: every coherence row yields a generator FILLING its declared parallel
boundary — both boundaries compute back to `source` / `target` by `rfl`.  Combined with `boundaryParallel`,
this says the generator is a genuine globular filler of a parallel pair over a checked ps-context (the CaTT
`coh` cell). -/
theorem cohGenerator_fills {computad : OmegaComputad} {dim : Nat} (row : CohRow computad dim) :
    boundarySource (cohGenerator row) = row.source ∧ boundaryTarget (cohGenerator row) = row.target :=
  ⟨rfl, rfl⟩

/-- ★ **The coherence generator is well-formed (globular)** whenever its boundary cells are — globularity is
FREE from the row's `boundaryParallel` field (the `IsGlobularCell` `gen` obligation is exactly parallelism of
the declared boundary). -/
theorem cohGenerator_isGlobularCell {computad : OmegaComputad} {dim : Nat} (row : CohRow computad dim)
    (sourceGlobular : IsGlobularCell row.source) (targetGlobular : IsGlobularCell row.target) :
    IsGlobularCell (cohGenerator row) :=
  ⟨sourceGlobular, targetGlobular, row.boundaryParallel⟩

/-! ## Non-vacuity 1 — the single-2-cell disk coherence -/

/-- The identity 1-cell is well-formed (its `id`-boundary is the globular object cell). -/
theorem oneCellId_isGlobularCell : IsGlobularCell oneCellId := True.intro

/-- ★ The **single-2-cell disk coherence row**: the disk ps-context (`twoGlobePsContext`, CHECKED) filled by
the parallel 1-cell pair `(oneCellGen, oneCellId)` (both `objectCell → objectCell`, parallel by `rfl`). -/
def twoGlobeCohRow : CohRow demoComputad 1 where
  psContext := twoGlobePsContext
  psContextChecks := twoGlobePsContext_checks
  cohLabel := ()
  source := oneCellGen
  target := oneCellId
  boundaryParallel := ⟨rfl, rfl⟩

/-- ★ A genuine `CellExpr demoComputad 2` coherence generator over the disk. -/
def twoGlobeCohGenerator : CellExpr demoComputad 2 := cohGenerator twoGlobeCohRow

#eval cellSize twoGlobeCohGenerator

/-- The disk coherence generator fills its parallel 1-cell boundary. -/
theorem twoGlobeCohGenerator_fills :
    boundarySource twoGlobeCohGenerator = oneCellGen ∧ boundaryTarget twoGlobeCohGenerator = oneCellId :=
  ⟨rfl, rfl⟩

/-- ★ The disk coherence generator is globular (non-vacuity of `cohGenerator_isGlobularCell`). -/
theorem twoGlobeCohGenerator_isGlobular : IsGlobularCell twoGlobeCohGenerator :=
  cohGenerator_isGlobularCell twoGlobeCohRow oneCellGen_isGlobular oneCellId_isGlobularCell

/-! ## Non-vacuity 2 — the interchange coherence (a CaTT `coh` cell from the Godement critical pair) -/

/-- ★ The **interchange coherence row**: the horizontal-composite ps-context
(`horizontalCompositePsContext`, CHECKED) filled by `interchangeCriticalRow`'s two whisker-order legs — the
ready-made `interchangeCriticalRow_isParallelPair` supplies the boundary parallelism.  The Godement / interchange
coherence, presented as a CaTT `coh` cell. -/
def interchangeCohRow : CohRow demoComputad 2 where
  psContext := horizontalCompositePsContext
  psContextChecks := horizontalCompositePsContext_checks
  cohLabel := ()
  source := interchangeCriticalRow.leftLeg
  target := interchangeCriticalRow.rightLeg
  boundaryParallel := interchangeCriticalRow_isParallelPair

/-- ★ A genuine `CellExpr demoComputad 3` interchange coherence generator. -/
def interchangeCohGenerator : CellExpr demoComputad 3 := cohGenerator interchangeCohRow

#eval cellSize interchangeCohGenerator

/-- The interchange coherence generator fills the two whisker-order legs. -/
theorem interchangeCohGenerator_fills :
    boundarySource interchangeCohGenerator = interchangeCriticalRow.leftLeg ∧
    boundaryTarget interchangeCohGenerator = interchangeCriticalRow.rightLeg :=
  ⟨rfl, rfl⟩

/-- ★ The interchange coherence generator fills a NON-DEGENERATE parallel pair: its source and target
boundaries are STRUCTURALLY DISTINCT (the two whisker orders of the horizontal composite), so the coherence
cell genuinely identifies non-equal 2-cells — not a trivial identity filler. -/
theorem interchangeCohGenerator_boundariesDistinct :
    cellBeq demoModeBeq demoGenBeq (boundarySource interchangeCohGenerator)
      (boundaryTarget interchangeCohGenerator) = false := rfl

end FX1Poly.Polygraph.Omega
