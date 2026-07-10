import FX1Poly.Polygraph.Omega.CriticalPairRow
import FX1Poly.Polygraph.Omega.InvolutionDemonstrator
import FX1Poly.Polygraph.Omega.KernelDiamondReading

/-! # Polygraph/Omega/DesignLockOmega4 — the OMEGA-4 (Squier ascent) ledger + OMEGA-5 handoff (B4)

The honest ledger of the OMEGA-4 r1 Squier ascent: every shipped piece cited, every surviving wall named
with its exact goal state and the named node that blocks it, and the OMEGA-5 (graded round) handoff spec.
This file edits NOTHING outside `Omega/`; the r1 markers are fresh `fxOmega4_*` names.  Markers are
hypothesis-free `Bool` defs, so every declaration is axiom-free.

## What OMEGA-4 r1 SHIPPED (each machine-checked zero-axiom)

  * **B1 — the dim-3 critical-pair row family** (`CriticalPairRow.lean`).  `CriticalPairRow` (the globular
    row datum, four boundary fields enforcing `IsParallelPair`), `criticalPairRow_isParallelPair`, the
    critical-pair-to-row constructor `criticalPairRowOfParallelLegs`, the singleton `CellRelOver`
    (`criticalPairRel`), the generating 3-cell `criticalPairThreeCell`, and the interchange non-vacuity
    (`interchangeCriticalRow` / `interchangeThreeCell` / `interchangeCriticalRow_isParallelPair` /
    `interchangeCriticalRow_legsDistinct`).  No new structure — the OMEGA-1 `CellRelOver` pattern one
    dimension up, closed by the 11-constructor `SaturatedConvOverWithId` (whose `idCongr` is the 2->3 bump).

  * **B2 — the walking-involution dim-3 demonstrator** (`InvolutionDemonstrator.lean`).  The presentation
    re-encoded as an `OmegaComputad` (`involutionSGen` / `involutionRhoGen`), the SOLE critical pair `sss`
    with its two legs (`involutionLeftLeg` / `involutionRightLeg`), the single generating 3-cell
    (`involutionSssThreeCell`), and the joinability of the peak (`involutionPeakJoin`, associativity) and
    valley (`involutionValleyJoin`, both units) modulo the strict congruence.  Scope named HONESTLY:
    literal globularity fails (`involutionLegs_notLiterallyParallel`).

  * **B3 — the kernel confluence certificate as dim-3 content** (`KernelDiamondReading.lean`).  The
    kernel's orthogonal `SquierDiamond` / `SquierConfluence` (`FX1Poly.Core`, `fxRewriteBundle_rowsDisjoint
    = true`) re-read as a globular `CellExpr diamondComputad` boundary pair (`diamondCriticalRow`) + a
    `SaturatedConvOverWithId` 3-cell (`diamondThreeCell`) — the FIRST dim-3 kernel content.  The abstract
    certificate `kernelDiamondCoherence` (= `completeCoherentJoin`) is cited; rides coherent CONFLUENCE, not
    the vacuous NF-coherence.

## The surviving walls (each named with its exact goal + blocking node)

  * **JAM — the involution's LITERAL globularity.**  Goal: the two `sss` legs as a LITERAL `IsParallelPair`
    in the free carrier.  FALSE: `(ss)s` and `s(ss)` are structurally distinct
    (`involutionLegs_notLiterallyParallel`), the critical pair spans two associations, and no strict-axiom
    row is an outgoing 2-cell in the free carrier.  The legs are parallel only modulo strict.  Blocking
    node: a strict-quotient carrier (associativity definitional), OR unit/assoc 2-cell generators — either
    changes the presentation.  Recorded by `fxOmega4_involutionLiteralGlobularityWallR1`.

  * **JAM — the involution's FULL homotopy basis.**  Goal: every pair of parallel 2-paths `s^n => s^k` is
    3-cell-homotopic modulo the single generating 3-cell `A` (coherence by structural length-fuel).  The
    single 3-cell + the joins are shipped; the full basis needs a 2-path normalization one dimension up
    (the involution's rewriting is length-monotone, so the recursion IS structural fuel, but the
    map-through-normal-form assembly is unbuilt).  Blocking node: a `conv_toParityNF`-analogue at the
    2-PATH level (`InvolutionDecision.lean:52` one dimension up).  Handed to OMEGA-5.  Recorded by
    `fxOmega4_involutionFullHomotopyBasisOpenR1`.

  * **WALL (cited, stays) — GENERAL Squier coherence.**  Goal: arbitrary convergent presentation implies
    coherent (a homotopy basis).  Needs OMEGA-2 Steiner arithmetic at n=3 AND termination of 3-cell
    rewriting — where Forest-Mimram (arXiv:2109.05369) stayed pen-and-paper.  Cite Guiraud-Malbos.
    Recorded by `fxOmega4_generalSquierCoherenceWallR1`.

  * **WALL (cited, stays) — the SATURATED walkers have NO convergent presentation.**  Two machine-checked
    falsifications: SAT-CONF (`9458da53d`, the interchange x whiskerRightVcomp Godement critical pair) and
    SAT-NF (`3902ea817`, `saturatedFragment_notConfluent` — the whiskered snake).  Their coherent story
    rides the MATCHING decision, not rewriting NF.  Recorded by
    `fxOmega4_saturatedWalkersNoConvergentPresentationR1`.

  * **WALL (cited, stays) — the OmegacE convergent confluences need a DATA upgrade.**  The
    genuinely-convergent OmegacE systems (`sortingHasConfluence` / `transpositionHasConfluence`) are
    `Prop`-valued over `OmegacEWord`, so re-reading as dim-3 cells needs a word->CellExpr embedding + a
    `Prop -> SquierConfluence` data upgrade (a bridge, budgeted separately).  The naive recon-constraint
    ("dim-3 = confluence certificates without reshaping") holds for the abstract `SquierDiamond` DATA (B3),
    NOT for these Prop-confluences.  Recorded by `fxOmega4_omegacEConfluencesNeedDataUpgradeR1`.

## The honest ceiling ledger

  * Squier buys DECIDABLE ISLANDS (per-presentation walkers), never a general decider: the undecidability
    ceiling STAYS (`CeilingLift.lean`, `fxOmega_ceilingLiftUndecidableInstanceMechanized = false`;
    Post-Markov / Burroni).  `fxOmega4_undecidabilityCeilingDissolvedR1 = false`.
  * OMEGA-4 reaches FINITE-CONVERGENT homology only; Squier homology forbidding finite convergent
    presentations (the H2-SQUIER-NOGO frontier, #2139) is NOT reached.
    `fxOmega4_squierHomologyBeyondFiniteConvergentOpenR1 = false`.
  * The saturated fragment's convergent content ships as MATCHING invariance, not rewriting NF (SAT-CONF).

## The OMEGA-5 (graded round) handoff — the interfaces it consumes

OMEGA-5 attaches grades to critical-pair resolutions.  It consumes:

  * **The row family `CriticalPairRow` + `criticalPairThreeCell`** — the generating 3-cells whose
    resolutions the graded round weights; the globular discipline `criticalPairRow_isParallelPair` fixes
    their boundaries.
  * **The idCongr-extended congruence `SaturatedConvOverWithId` + `recInto`** — the dim-3 congruence whose
    classes the graded 3-cells refine (any grade-respecting invariant folds through `recInto`).
  * **The worked instances** — the involution demonstrator (`involutionSssThreeCell`, the sole critical
    pair, joinable modulo strict) and the kernel diamond reading (`diamondThreeCell`, the orthogonal
    confluence certificate) as the two archetypes (critical-pair vs disjoint-redex) the graded round grades.

Raw Lean 4 + Init; a docstring record plus `Bool` markers, so every declaration is axiom-free.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! ## The r1 shipped-piece markers (each cites machine-checked code) -/

/-- ★ **B1 SHIPPED — the dim-3 critical-pair row family.**  `CriticalPairRow` (globular by four boundary
fields), `criticalPairRow_isParallelPair`, the critical-pair-to-row constructor, `criticalPairRel`,
`criticalPairThreeCell`, and the interchange non-vacuity — all zero-axiom.  `= true`. -/
def fxOmega4_criticalPairRowFamilyShippedR1 : Bool := true

/-- ★ **B2 SHIPPED — the walking-involution dim-3 demonstrator.**  The `OmegaComputad` re-encoding, the sole
`sss` critical pair, the generating 3-cell `involutionSssThreeCell`, and the peak/valley joins modulo strict,
all zero-axiom.  `= true`. -/
def fxOmega4_involutionDemonstratorShippedR1 : Bool := true

/-- ★ **B3 SHIPPED — the kernel confluence certificate as the FIRST dim-3 kernel content.**  The orthogonal
`SquierDiamond` / `SquierConfluence` re-read as `diamondCriticalRow` + `diamondThreeCell`, citing
`kernelDiamondCoherence` (= `completeCoherentJoin`), all zero-axiom.  `= true`. -/
def fxOmega4_kernelRereadingShippedR1 : Bool := true

/-! ## The surviving-wall markers (each names the exact jam + blocking node) -/

/-- ★ **JAM — the involution's LITERAL globularity is OPEN.**  `= true` records the wall: the `sss` legs are
parallel only modulo the strict congruence (`(ss)s` vs `s(ss)` structurally distinct,
`involutionLegs_notLiterallyParallel`); literal `IsParallelPair` in the free carrier is FALSE.  Blocking
node: a strict-quotient carrier or unit/assoc 2-cell generators (either changes the presentation). -/
def fxOmega4_involutionLiteralGlobularityWallR1 : Bool := true

/-- ★ **JAM — the involution's FULL homotopy basis is OPEN.**  `= true`: the single generating 3-cell + the
peak/valley joins are shipped; every-parallel-2-path-homotopic (coherence by structural length-fuel) needs a
2-path normalization one dimension up (blocking node: a `conv_toParityNF`-analogue at the 2-path level).
Handed to OMEGA-5. -/
def fxOmega4_involutionFullHomotopyBasisOpenR1 : Bool := true

/-- ★ **WALL (cited, stays) — GENERAL Squier coherence.**  `= true` records the wall present: arbitrary
convergent-implies-coherent needs Steiner arithmetic at n=3 AND termination of 3-cell rewriting, where
Forest-Mimram (arXiv:2109.05369) stayed pen-and-paper (Guiraud-Malbos).  OMEGA-4 does NOT reach it. -/
def fxOmega4_generalSquierCoherenceWallR1 : Bool := true

/-- ★ **WALL (cited, stays) — the saturated walkers have NO convergent presentation.**  `= true`: two
machine-checked falsifications, SAT-CONF (`9458da53d`, the interchange x whiskerRightVcomp Godement critical
pair) and SAT-NF (`3902ea817`, `saturatedFragment_notConfluent`, the whiskered snake).  Their coherent story
rides the MATCHING decision, not rewriting NF. -/
def fxOmega4_saturatedWalkersNoConvergentPresentationR1 : Bool := true

/-- ★ **WALL (cited, stays) — the OmegacE convergent confluences need a DATA upgrade.**  `= true`: the
convergent OmegacE systems are `Prop`-valued over `OmegacEWord`, so re-reading as dim-3 cells needs a
word->CellExpr embedding + a `Prop -> SquierConfluence` data upgrade (budgeted separately).  The naive
"confluence certificates without reshaping" holds only for the abstract `SquierDiamond` DATA (B3). -/
def fxOmega4_omegacEConfluencesNeedDataUpgradeR1 : Bool := true

/-! ## The honest ceiling markers (each `= false` — NOT dissolved / NOT reached) -/

/-- ★ **The undecidability ceiling is NOT dissolved.**  `= false` — Squier buys decidable ISLANDS
(per-presentation walkers), never a general decider; arbitrary presented word problems stay undecidable at
every suspended dimension (`CeilingLift.lean`, `fxOmega_ceilingLiftUndecidableInstanceMechanized = false`;
Post-Markov / Burroni). -/
def fxOmega4_undecidabilityCeilingDissolvedR1 : Bool := false

/-- ★ **Squier homology beyond finite-convergent is NOT reached.**  `= false` — OMEGA-4 reaches
finite-convergent homology only; homology forbidding finite convergent presentations (the H2-SQUIER-NOGO
frontier, #2139) is out of scope. -/
def fxOmega4_squierHomologyBeyondFiniteConvergentOpenR1 : Bool := false

/-- ★ **The honest re-assessment: the Squier ascent is NOT complete.**  `= false` — B1/B2/B3 shipped the
row family, one demonstrator (fragment scope: parallel modulo strict), and the kernel re-reading; but the
involution's full homotopy basis, general Squier coherence, the saturated-walker convergence (IMPOSSIBLE),
and the OmegacE data upgrade all remain.  Set `true` only when the general convergent-implies-coherent
lands (it will not, at this dimension — see the cited walls). -/
def fxOmega4_squierAscentCompleteR1 : Bool := false

/-! ## The OMEGA-5 handoff marker -/

/-- ★ **The OMEGA-5 (graded round) handoff is RECORDED.**  The interfaces OMEGA-5 consumes are named in the
file docstring: the row family `CriticalPairRow` + `criticalPairThreeCell` (the generating 3-cells the graded
round weights) with the globularity discipline `criticalPairRow_isParallelPair`; the idCongr-extended
congruence `SaturatedConvOverWithId` + `recInto` (the dim-3 classes the graded 3-cells refine); and the two
worked archetypes — the involution demonstrator (`involutionSssThreeCell`, a critical-pair filler) and the
kernel diamond reading (`diamondThreeCell`, a disjoint-redex filler).  `= true` (recorded). -/
def fxOmega4_omegaFiveGradedRoundHandoffRecordedR1 : Bool := true

end FX1Poly.Polygraph.Omega
