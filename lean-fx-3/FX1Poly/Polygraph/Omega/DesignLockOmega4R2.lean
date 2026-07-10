import FX1Poly.Polygraph.Omega.CertificateFunctor
import FX1Poly.Polygraph.Omega.InvolutionSquierBasis
import FX1Poly.Polygraph.Omega.DesignLockOmega4

/-! # Polygraph/Omega/DesignLockOmega4R2 — the OMEGA-4 r2 ledger + refined OMEGA-5 handoff (B4)

The honest r2 ledger: what the 110-percent grind SHIPPED over r1, the r2 re-assessment
(hypothesis-free), every surviving jam named with its exact goal and blocking node, and the refined
OMEGA-5 (graded round) handoff spec.  This file edits NOTHING outside `Omega/`; every r1 marker stays.
All markers are hypothesis-free `Bool` defs, so every declaration is axiom-free.

## What OMEGA-4 r2 SHIPPED over r1 (each machine-checked zero-axiom)

  * **B1 — THE FUNCTOR** (`CertificateFunctor.lean`).  The r1 OMEGA-5 residual "the full functor
    `SquierConfluence -> CellExpr 3` (every abstract diamond, not just one instance)" is DISCHARGED:
      - `encodePath` — abstract reduction paths -> `vcomp` chains of 2-cells (`RewritePath.foldMap`);
      - `encodePath_comp_conv` — THE COMPOSITION LAW, modulo the strict congruence (free `vcomp` is not
        associative/unital on the nose — the r1 "parallel only modulo strict" caveat one dimension up,
        now on the composition law);
      - `encodeHomotopy` — THE FUNCTOR: every `RewriteHomotopy dp p q` becomes a dim-3
        `SaturatedConvOverWithId` cell, by a 6-case induction consuming the composition law in
        `whiskerRight`;
      - `encodeHomotopy_viaLeastCongruence` — the same map re-obtained through the abstract least-
        congruence UP `RewriteHomotopy.toModel` (the uniqueness half);
      - `encodeConfluenceRow` / `encodeConfluenceThreeCell` — a coherent `SquierConfluence` square as a
        globular `CriticalPairRow` + its dim-3 3-cell.
    TOTAL for arbitrary type-level `Step` (no finiteness / `DecidableEq`).  Characterization: a STRICT
    functor into the `SaturatedConvOverWithId` quotient, a LAX functor into the free carrier.  The r1
    `diamondThreeCell` is re-derived through the functor (`functorialCompleteDiamondCell`), the label-
    degeneracy difference NAMED (`functorialCompleteDiamondLegsCoincide`: the abstract `completeStep`
    collapses all steps, so the faithful image has coincident legs, whereas r1 hand-picked 4 distinct
    labels), and a SECOND non-degenerate certificate has STRUCTURALLY DISTINCT legs
    (`secondCertificateLegsDistinct`).

  * **B2 — the involution homotopy-basis fragment** (`InvolutionSquierBasis.lean`).  The least-congruence
    UP `involutionSssLegsIdentifiedInEveryModel` (the single 3-cell generates the identification in every
    absorbing congruence) and the assembled coherent resolution `involutionCriticalPairResolved` (peak /
    legs / valley convertible — joinable-modulo-strict as one datum).  The recon's Route A (push
    `SquierDiamond.coherence` through the functor) is HONESTLY WALLED — see the jam below.

  * **B3 — the OmegacE data upgrade — DEFERRED (own round), r1 verdict re-affirmed.**  `RewritesMany` is
    `Prop`-valued, so a data-level `SquierConfluence` needs a `Prop -> Type` choice, BANNED in this
    Init-only zero-axiom setting.  The functor (B1) consumes `SquierConfluence` DATA; the OmegacE systems
    supply only `Prop` joinability, so a per-system Type-valued re-derivation is a full brick per system,
    not folded into r2.

## The r2 re-assessment (hypothesis-free) — the ascent is STILL NOT complete

B1 discharged the FULL functor residual and B2 advanced the involution fragment, but the FULL homotopy
basis, general Squier coherence, the saturated-walker convergence (IMPOSSIBLE — SAT-CONF / SAT-NF), and
the OmegacE data upgrade all remain.  `fxOmega4_squierAscentCompleteR2 = false`.

## The surviving jams (each: exact goal + NAMED blocking node)

  * **JAM — Route A (the involution full Squier coherent presentation via the functor).**  Goal: feed the
    involution's coherence-to-normal-form (`SquierDiamond.coherence`) through the r2 functor to land a
    machine-checked coherent presentation.  WALLED: the STRONG single-step `SquierDiamond` demands total
    single-step residuals over ALL coinitial peaks, which is incompatible with reachable normal forms (a
    peak whose reducts are the NFs `s` / `id` has no single-step residual), so `coherence` is vacuous for
    the involution and no `SquierConfluence` DATA exists to feed `encodeHomotopy`.  Blocking node: a
    `SquierDiamond`-with-PATH-residuals + termination (the WF-coherent-Newman argument, whose
    `WellFounded.fix` leaks `propext` / `Quot.sound`), OR a strict-quotient carrier making the legs
    literally parallel.  Recorded by `InvolutionSquierBasis.fxOmega4_involutionRouteAStrongDiamondWallR2`.

  * **JAM — the involution's FULL homotopy basis** (r1, re-affirmed).  Goal: every parallel 2-path
    `s^n => s^k` is 3-cell-homotopic modulo the single generating 3-cell.  Blocking node: a
    `conv_toParityNF`-analogue at the 2-PATH level (2-path normalization one dimension up).  Handed to
    OMEGA-5.  `fxOmega4_involutionFullHomotopyBasisReachedR2 = false`.

  * **WALL (cited, stays) — GENERAL Squier coherence** (r1).  Goal: arbitrary convergent presentation
    implies coherent.  Needs OMEGA-2 Steiner arithmetic at n=3 AND termination of 3-cell rewriting —
    where Forest-Mimram (arXiv:2109.05369) stayed pen-and-paper (Guiraud-Malbos).
    `fxOmega4_generalSquierCoherenceReachedR2 = false`.

  * **WALL (cited, stays) — the OmegacE convergent confluences need a DATA upgrade** (r1).  `Prop`-valued
    `RewritesMany` -> a Type-valued re-derivation per system; `Prop -> Type` choice BANNED.
    `fxOmega4_omegacEDataUpgradeReachedR2 = false`.

  * **WALL (cited, stays) — the saturated walkers have NO convergent presentation** (r1).  Two
    machine-checked falsifications (SAT-CONF `9458da53d`, SAT-NF `3902ea817`); their coherent story rides
    the MATCHING decision, not rewriting NF.  Unchanged by r2.

## The refined OMEGA-5 (graded round) handoff — what the graded round consumes

OMEGA-5 attaches grades to critical-pair resolutions.  It consumes, from r1:

  * `CriticalPairRow` + `criticalPairThreeCell` — the generating 3-cells the graded round weights (with
    the globular discipline `criticalPairRow_isParallelPair`);
  * `SaturatedConvOverWithId` + `recInto` — the dim-3 congruence whose classes the graded 3-cells refine;
  * the two worked archetypes — `involutionSssThreeCell` (critical-pair filler) and `diamondThreeCell`
    (disjoint-redex filler).

and NOW, from r2:

  * **the certificate FUNCTOR** `encodeHomotopy` / `encodeConfluenceThreeCell` — the machine that turns
    ANY abstract confluence certificate (`RewriteHomotopy` / `SquierConfluence`) into a gradeable dim-3
    cell, so the graded round can weight resolutions PRODUCED from certificates rather than only
    hand-built rows;
  * **the least-congruence factorization** `encodeHomotopy_viaLeastCongruence` — the guarantee that the
    grading of the functorial image is FORCED (the diamonds generate the congruence), so a
    grade-respecting invariant on the functor's codomain folds through `recInto` uniquely;
  * **the involution coherent resolution** `involutionCriticalPairResolved` + the least-congruence UP
    `involutionSssLegsIdentifiedInEveryModel` — the single-critical-pair archetype the graded round
    weights, with its joinable-modulo-strict boundary data (peak / valley) attached.

Raw Lean 4 + Init; a docstring record plus `Bool` markers, so every declaration is axiom-free.
Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! ## The r2 shipped-piece markers (each cites machine-checked code) -/

/-- ★ **B1 — the r1 OMEGA-5 full-functor residual DISCHARGED.**  `= true`: `encodePath` /
`encodePath_comp_conv` / `encodeHomotopy` / `encodeHomotopy_viaLeastCongruence` / `encodeConfluenceRow`
/ `encodeConfluenceThreeCell` ship the total, structural map from abstract certificate data into dim-3
cells (`CertificateFunctor.lean`, `fxOmega4_certificateFunctorShippedR2 = true`), TOTAL for arbitrary
type-level `Step`.  This is the "full functor `SquierConfluence -> CellExpr 3`" r1 named as OMEGA-5. -/
def fxOmega4_certificateFunctorResidualDischargedR2 : Bool := true

/-- ★ **B2 — the involution homotopy-basis fragment ADVANCED.**  `= true`: the least-congruence UP
`involutionSssLegsIdentifiedInEveryModel` and the assembled coherent resolution
`involutionCriticalPairResolved` (`InvolutionSquierBasis.lean`,
`fxOmega4_involutionSquierBasisFragmentShippedR2 = true`) — a genuine increment over r1's loose
peak/legs/valley facts, at the honest fragment scope. -/
def fxOmega4_involutionBasisFragmentAdvancedR2 : Bool := true

/-! ## The r2 re-assessment (hypothesis-free) -/

/-- ★ **The honest r2 re-assessment: the Squier ascent is STILL NOT complete.**  `= false` — B1
discharged the full functor and B2 advanced the involution fragment, but the involution's full homotopy
basis, general Squier coherence, the saturated-walker convergence (IMPOSSIBLE), and the OmegacE data
upgrade all remain.  Set `true` only when the general convergent-implies-coherent lands (it will not, at
this dimension — see the cited walls). -/
def fxOmega4_squierAscentCompleteR2 : Bool := false

/-! ## The surviving-jam markers (each `= false` — NOT reached; the exact goal + blocking node in the
file docstring) -/

/-- ★ **The involution's FULL homotopy basis is NOT reached.**  `= false` — every-parallel-2-path
homotopic needs a `conv_toParityNF`-analogue at the 2-PATH level (2-path normalization one dimension up).
Handed to OMEGA-5. -/
def fxOmega4_involutionFullHomotopyBasisReachedR2 : Bool := false

/-- ★ **GENERAL Squier coherence is NOT reached.**  `= false` — arbitrary convergent-implies-coherent
needs Steiner arithmetic at n=3 AND termination of 3-cell rewriting (Forest-Mimram pen-and-paper,
Guiraud-Malbos).  OMEGA-4 does not reach it. -/
def fxOmega4_generalSquierCoherenceReachedR2 : Bool := false

/-- ★ **The OmegacE data upgrade is NOT reached (deferred, own round).**  `= false` — the convergent
OmegacE systems are `Prop`-valued over `OmegacEWord`; a data-level `SquierConfluence` needs a
`Prop -> Type` choice, BANNED in this Init-only zero-axiom setting.  A per-system Type-valued
re-derivation is a full brick per system; the functor (B1) is ready to consume it once the DATA exists. -/
def fxOmega4_omegacEDataUpgradeReachedR2 : Bool := false

/-! ## The refined OMEGA-5 handoff marker -/

/-- ★ **The OMEGA-5 (graded round) handoff is REFINED.**  `= true` (recorded).  Beyond the r1 interfaces
(the row family + `criticalPairThreeCell`, the `SaturatedConvOverWithId` congruence + `recInto`, the two
archetypes), the graded round now ALSO consumes the r2 certificate functor
(`encodeHomotopy` / `encodeConfluenceThreeCell` — the certificate-to-gradeable-cell machine), the
least-congruence factorization (`encodeHomotopy_viaLeastCongruence` — grading is forced), and the
involution coherent resolution (`involutionCriticalPairResolved` + `involutionSssLegsIdentifiedInEveryModel`).
See the file docstring for the full spec. -/
def fxOmega4_omegaFiveGradedRoundHandoffRefinedR2 : Bool := true

end FX1Poly.Polygraph.Omega
