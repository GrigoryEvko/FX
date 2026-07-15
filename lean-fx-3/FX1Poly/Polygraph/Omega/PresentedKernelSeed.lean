import FX1Poly.Polygraph.Omega.CriticalPairRow

/-! # Polygraph/Omega/PresentedKernelSeed — the kernel as (signature, table2, table3) (OMEGA-7 r1, B2)

★ **THE PRESENTED-KERNEL SEED.**  OMEGA-7's grand thesis is "the kernel = (signature, table2, table3, …)":
a finitely-presented ω-polygraph whose signature is the generating data, table2 the 2-cell (rewrite)
generators, table3 the 3-cell (coherence / critical-pair) generators, and so on up.  This file makes that
tuple a MACHINE-CHECKED VALUE over the shipped Omega carrier — `PresentedKernel` — and re-reads OMEGA-4's
`CriticalPairRow` as the explicit table3, so the OMEGA-4 Squier ascent is exactly the dim-3 slot of the
tuple, made explicit.

## The live-kernel instantiation (cited by name, recon JOB 3)

The tuple's PRODUCTION instance over the actual FX kernel is:

  * **signature** = `fxSignature` (`Axis/…/GeneratorSignatureValue.lean`), packaged as
    `fxFibredKernel.presentation` (`Core/Fib/FibrationArchitecture.lean`, `= fxSignature` by `rfl`);
  * **table2** = the term/iota rewrite ROWS — `IotaRuleTable`, `fxTypingBundle` / `TypingTableBundle`
    (`Typed/Engine/RuleTables/`), `StepOverTable` (`Core/Rewriting/RuleTables/StepOver/`): the dim-2
    rewrite generators of the kernel;
  * **table3** = OMEGA-4's `CriticalPairRow` (this tree) — a Squier critical pair resolved to a valley IS a
    generating 3-cell, closed by `SaturatedConvOverWithId` (whose `idCongr` is the 2->3 dimension bump).

Those production tables are the heavy typed engine; r1 SEEDS the tuple over the light `OmegaComputad`
carrier (`CellRelOver` as the uniform row shape at every dimension) and instantiates it non-vacuously so the
SHAPE is machine-checked, deferring the full typed-table instantiation (which needs the OMEGA-7 pasting
engine to type the rows' boundaries) to a later round.  This mirrors OMEGA-6's `OmegaSevenPastingShape`
handoff signature: a value-level record, not a heavy import.

## What ships here (each machine-checked zero-axiom)

  * **`PresentedKernel`** — the tuple record `(signature, table2, table3)`: an `OmegaComputad` plus two
    `CellRelOver` rows (the dim-2 rewrite generators and the dim-3 coherence generators).
  * **`presentedKernelRow`** — the per-dimension table family `(dim : Nat) → CellRelOver`, seeding the "…"
    of the tuple: table2 at the 2-cell slot, table3 at the 3-cell slot, the empty row elsewhere (the r3
    kernel-as-value lift replaces this with a genuine per-dimension `AdmittedTable`).
  * **`demoPresentedKernel`** — the non-vacuous instance over the demo computad: `signature :=
    demoComputad`, `table2 := StrictAxiomRel demoComputad` (the strict-ω structural rewrite rows), `table3
    := criticalPairRel interchangeCriticalRow` (the Godement/interchange critical pair as a 3-cell).
  * **`demoPresentedKernel_table2_inhabited`** / **`demoPresentedKernel_table3_inhabited`** — non-vacuity:
    table2 fires on a real vcomp-associativity pair, table3 fires on the two interchange legs.
  * **`demoPresentedKernel_table3_threeCell`** — ★ the dim-3 generator's genuine 3-cell: the interchange
    row's `SaturatedConvOverWithId` closure, typed over `demoPresentedKernel.table3` (the OMEGA-4
    `interchangeThreeCell`).

Raw Lean 4 + Init.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! ## The empty row (the tuple's off-slot filler) -/

/-- The **empty cell relation** — relates nothing.  The filler for tuple slots without generators (every
dimension except the ones carrying table2 / table3 in the r1 seed). -/
def emptyCellRel (computad : OmegaComputad) : CellRelOver computad :=
  fun _ _ => False

/-! ## The presented-kernel tuple -/

/-- ★ **THE PRESENTED KERNEL — the (signature, table2, table3) tuple as a value.**  A finitely-presented
ω-polygraph seed: the generating `signature` (an `OmegaComputad`), the dim-2 rewrite generators `table2`,
and the dim-3 coherence generators `table3` (each a `CellRelOver` — the uniform row shape at every
dimension).  The "…" of the grand tuple is seeded by `presentedKernelRow`; the live-kernel instantiation
`(fxSignature, IotaRuleTable/TypingTableBundle, CriticalPairRow)` is cited in the file docstring. -/
structure PresentedKernel where
  /-- The generating data — the ω-computad the cells are built over. -/
  signature : OmegaComputad
  /-- The dim-2 rewrite generators (the 2-cell rows — the kernel's iota/strict rewrite table). -/
  table2 : CellRelOver signature
  /-- The dim-3 coherence generators (the 3-cell rows — the OMEGA-4 critical-pair table). -/
  table3 : CellRelOver signature

/-- The **per-dimension row family** of a presented kernel — seeds the "…" of the tuple: table2 at the
2-cell slot, table3 at the 3-cell slot, the empty row elsewhere.  The r3 kernel-as-value lift (POLY-CAP
`Kernel := (n : Nat) → AdmittedTable n`) replaces this stub with a genuine per-dimension admitted table. -/
def presentedKernelRow (kernel : PresentedKernel) : Nat → CellRelOver kernel.signature
  | 2 => kernel.table2
  | 3 => kernel.table3
  | _ => emptyCellRel kernel.signature

/-! ## The non-vacuous demo instance (OMEGA-4 CriticalPairRow AS table3) -/

/-- ★ **The demo presented kernel** — the tuple instantiated non-vacuously over the demo computad: the
strict-ω structural rewrite rows as table2, and the Godement/interchange critical pair (OMEGA-4's
`interchangeCriticalRow`) re-read as the dim-3 coherence generator table3. -/
def demoPresentedKernel : PresentedKernel where
  signature := demoComputad
  table2 := StrictAxiomRel demoComputad
  table3 := criticalPairRel interchangeCriticalRow

/-- Non-vacuity: table2 (the strict rewrite rows) fires on a REAL vcomp-associativity pair — the
substitution/pasting associativity law (OMEGA-7 B1) sitting in the dim-2 slot as a rewrite generator. -/
theorem demoPresentedKernel_table2_inhabited :
    demoPresentedKernel.table2
      (CellExpr.vcomp (CellExpr.vcomp twoCellGen twoCellId) whiskerCell)
      (CellExpr.vcomp twoCellGen (CellExpr.vcomp twoCellId whiskerCell)) :=
  StrictAxiomRel.vcompAssoc twoCellGen twoCellId whiskerCell

/-- Non-vacuity: table3 (the critical-pair rows) fires on the two interchange legs — the OMEGA-4 dim-3
generator sitting in the 3-cell slot. -/
theorem demoPresentedKernel_table3_inhabited :
    demoPresentedKernel.table3 interchangeCriticalRow.leftLeg interchangeCriticalRow.rightLeg :=
  CriticalPairRel.fire

/-- ★ **The dim-3 generator's genuine 3-cell.**  The interchange critical pair, fired through
`criticalPairThreeCell`, is a real `SaturatedConvOverWithId` convertibility between its two parallel 2-cell
legs — typed over `demoPresentedKernel.table3`.  This is the OMEGA-4 `interchangeThreeCell` reseated as the
tuple's table3 content: the presented kernel's dim-3 slot carries a genuine 3-cell. -/
def demoPresentedKernel_table3_threeCell :
    SaturatedConvOverWithId demoComputad demoPresentedKernel.table3
      interchangeCriticalRow.leftLeg interchangeCriticalRow.rightLeg :=
  interchangeThreeCell

end FX1Poly.Polygraph.Omega
