import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidRiffleNaturality
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidCoxeterUniqueness
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidWellTypedAbsorber

/-! # Polygraph/Omega/WalkingBunchedBimonoidStarAssembly — the corrected star RE-STATED at its honest
non-refutable scope (`additive AND well-typed`), the two-guard exclusion of BOTH self-attack counterexamples, the
gated retraction legs, and the honest partial ledger with the star NOT flipped (WP-PROP r7, #2033, the 110-percent
grind)

★ **THE r7 SPINE — the recon's headline finding, discharged.**  The r5 `StarRetractionCensus` corrected the
unrestricted star to the ADDITIVE-colour scope `bunchedBimonoidStarStatementAdditive` (excluding the `mu_m` /
`mu_a` mixed-colour datum by additivity).  But the recon's r7 headline is that the additive-only star is ITSELF
still refutable: the r6 mis-declared datum `bunchedBimonoidMisdeclaredMu` is ADDITIVE (`cellUsesOnlyAdditive =
true`) and shares `mu_a`'s matrix (`[[1,1]]`), yet is not convertible to `mu_a` (a bare gen with a different
boundary is a normal form).  So additivity ALONE is not enough — the star ALSO needs the Job-3 well-typedness
restriction.

## The re-stated star (`additive AND well-typed`) and its two guards

`bunchedBimonoidStarStatementAdditiveWellTyped` adds the `CellWellTyped` hypothesis (B3) to the additive star.
`bunchedBimonoidStarNeedsBothGuards` machine-witnesses that BOTH restrictions are load-bearing: `misdeclaredMu` is
additive-but-not-well-typed (excluded by the well-typedness guard, `bunchedBimonoidMisdeclaredMuNotWellTyped`) and
`mu_m` is not additive (excluded by the additivity guard, r6 `bunchedBimonoidMultMuIsNotAdditive`).
`bunchedBimonoidRestatedStarExcludesMisdeclaredDatum` proves the full premise conjunction of the re-stated star is
UNSATISFIABLE for the `(misdeclaredMu, mu_a)` datum — so the r6 counterexample cannot refute it.

## The star is NOT closed — gated on B1 and B2, no flip

The retraction chain `alpha ~ retract alpha = retract beta ~ beta` has its `gen` / `id` / `whisker` OUTER legs
shipped as r6 CONV deltas (`RetractionConvDeltas`); its `vcomp` case is the wide collision recursion (B1
`RiffleNaturality`, walled — the general `wideSwap` word is unbuilt); its equal-matrices MIDDLE is the perm-middle
`CoxeterWordUnique` (B2 `CoxeterUniqueness`, walled — the bubble-sort is unbuilt though all five moves are in
scope).  Both walls stand, so the star does NOT close in r7; every upstream star marker stays `= false`
byte-intact — NO fabricated flip.

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

set_option maxHeartbeats 4000000

/-! # =========================================================================================
    # B4 — THE RE-STATED STAR (`additive AND well-typed`, non-refutable)
    # =========================================================================================
-/

/-- ★★ **THE r7 CORRECTED STAR, RE-STATED at its honest non-refutable scope (NOT proven).**  The additive star
`bunchedBimonoidStarStatementAdditive` (r5) is still refutable by the r6 mis-declared additive datum
`misdeclaredMu`; this re-statement adds the B3 `CellWellTyped` hypothesis on BOTH cells.  Every two
same-dimension 2-cells that are additive AND well-typed with equal `Mat(N)` matrix are convertible over the star
scope.  This is the honest completeness target — it carries BOTH the additivity and the well-typedness
restrictions, so neither the `mu_m` (mixed-colour) nor the `misdeclaredMu` (mis-declared) datum can refute it.
Still NOT proven (the wide collision recursion B1 + the `CoxeterWordUnique` bubble-sort B2 are walled). -/
def bunchedBimonoidStarStatementAdditiveWellTyped : Prop :=
  ∀ {dim : Nat} (cellAlpha cellBeta : CellExpr bunchedBimonoidOmegaComputad dim),
    bunchedBimonoidCellUsesOnlyAdditive cellAlpha = true →
    bunchedBimonoidCellUsesOnlyAdditive cellBeta = true →
    bunchedBimonoidCellWellTyped cellAlpha →
    bunchedBimonoidCellWellTyped cellBeta →
    bunchedBimonoidEvalCell cellAlpha = bunchedBimonoidEvalCell cellBeta →
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope cellAlpha cellBeta

/-! # =========================================================================================
    # B4 — THE TWO-GUARD EXCLUSION (the headline self-attacks)
    # =========================================================================================
-/

/-- ★ **The mis-declared datum shares `mu_a`'s matrix** — `evalCell misdeclaredMu = evalCell mu_a` (both
`[[1,1]]`), on the nose.  So `(misdeclaredMu, mu_a)` satisfies the equal-matrix hypothesis; only the
well-typedness guard separates them. -/
theorem bunchedBimonoidMisdeclaredMuMatchesAddMuMatrix :
    bunchedBimonoidEvalCell bunchedBimonoidMisdeclaredMu = bunchedBimonoidEvalCell bunchedBimonoidAddMuGen :=
  rfl

/-- ★★★ **THE HEADLINE — the mis-declared datum is ADDITIVE but NOT well-typed.**  `misdeclaredMu` passes the
additive-colour restriction (`cellUsesOnlyAdditive = true`: label `addMult` additive, sub-cells `id`/`ofMode`
additive) yet FAILS well-typedness (`bunchedBimonoidMisdeclaredMuNotWellTyped`).  So the additive-ONLY star is
refutable by it — the well-typedness guard is MANDATORY, exactly the recon's r7 headline. -/
theorem bunchedBimonoidMisdeclaredMuIsAdditiveButNotWellTyped :
    bunchedBimonoidCellUsesOnlyAdditive bunchedBimonoidMisdeclaredMu = true
      ∧ ¬ bunchedBimonoidCellWellTyped bunchedBimonoidMisdeclaredMu :=
  ⟨rfl, bunchedBimonoidMisdeclaredMuNotWellTyped⟩

/-- ★★★ **THE RE-STATED STAR EXCLUDES the r6 counterexample.**  The full premise conjunction of
`bunchedBimonoidStarStatementAdditiveWellTyped` for the `(misdeclaredMu, mu_a)` datum is UNSATISFIABLE: it demands
`CellWellTyped misdeclaredMu`, which is false.  So the datum that refutes the additive-only star CANNOT refute the
re-stated `additive AND well-typed` star — the well-typedness restriction excises the obstruction. -/
theorem bunchedBimonoidRestatedStarExcludesMisdeclaredDatum :
    ¬ (bunchedBimonoidCellUsesOnlyAdditive bunchedBimonoidMisdeclaredMu = true
        ∧ bunchedBimonoidCellUsesOnlyAdditive bunchedBimonoidAddMuGen = true
        ∧ bunchedBimonoidCellWellTyped bunchedBimonoidMisdeclaredMu
        ∧ bunchedBimonoidCellWellTyped bunchedBimonoidAddMuGen
        ∧ bunchedBimonoidEvalCell bunchedBimonoidMisdeclaredMu
            = bunchedBimonoidEvalCell bunchedBimonoidAddMuGen) := by
  intro hpremises
  exact bunchedBimonoidMisdeclaredMuNotWellTyped hpremises.2.2.1

/-- ★★★ **THE STAR NEEDS BOTH GUARDS — machine-witnessed.**  The two self-attack counterexamples are excised by
DIFFERENT restrictions: `misdeclaredMu` is additive-but-not-well-typed (needs the well-typedness guard) and `mu_m`
is not additive (needs the additivity guard, r6 `bunchedBimonoidMultMuIsNotAdditive`).  Neither guard alone
suffices; the corrected star must carry BOTH — the recon's r7 headline, machine-checked. -/
theorem bunchedBimonoidStarNeedsBothGuards :
    (bunchedBimonoidCellUsesOnlyAdditive bunchedBimonoidMisdeclaredMu = true
        ∧ ¬ bunchedBimonoidCellWellTyped bunchedBimonoidMisdeclaredMu)
      ∧ bunchedBimonoidCellUsesOnlyAdditive bunchedBimonoidMultMuGen = false :=
  ⟨⟨rfl, bunchedBimonoidMisdeclaredMuNotWellTyped⟩, bunchedBimonoidMultMuIsNotAdditive⟩

/-! # =========================================================================================
    # B4 — THE MARKERS + THE HONEST NO-FLIP LEDGER
    # =========================================================================================
-/

/-- ★★ **ESTABLISHED (B4) — the corrected star is re-stated with the well-typedness guard.**  `= true` records
`bunchedBimonoidStarStatementAdditiveWellTyped` (the additive star plus the B3 `CellWellTyped` hypothesis) and the
headline `bunchedBimonoidMisdeclaredMuIsAdditiveButNotWellTyped` (the additive-only star is refutable; the
well-typedness guard is mandatory).  The honest non-refutable star scope. -/
def fxBunchedBimonoid_restatedStarCarriesWellTypedness : Bool := true

/-- ★★★ **ESTABLISHED (B4) — the re-stated star excludes BOTH self-attack counterexamples.**  `= true` records
`bunchedBimonoidStarNeedsBothGuards` and `bunchedBimonoidRestatedStarExcludesMisdeclaredDatum`: `misdeclaredMu` is
excised by the well-typedness guard, `mu_m` by the additivity guard, and the full premise conjunction for the
`(misdeclaredMu, mu_a)` datum is unsatisfiable.  The two guards together make the star non-refutable by the known
self-attacks (recon Job-5 (iii) + (iv)). -/
def fxBunchedBimonoid_restatedStarExcludesBothCounterexamples : Bool := true

/-- ★ **ESTABLISHED (B4) — the retraction legs are gated on B1 and B2.**  `= true` records the honest star-chain
shape `alpha ~ retract alpha = retract beta ~ beta`: the `gen` / `id` / `whisker` OUTER legs are the shipped r6
CONV deltas (`RetractionConvDeltas`); the `vcomp` case is the wide collision recursion (B1
`fxBunchedBimonoid_wideCollisionRecursionStillUnbuilt`, walled); the equal-matrices MIDDLE is the perm-middle
`CoxeterWordUnique` (B2 `fxBunchedBimonoid_coxeterWordUniqueBubbleSortStillUnbuilt`, walled, all five moves in
scope).  The elementary legs ship; the two heavy nodes are walled. -/
def fxBunchedBimonoid_starLegsGatedOnB1AndB2 : Bool := true

/-- ★ **THE CORRECTED WELL-TYPED STAR STAYS OPEN — no flip.**  `= false` records that
`bunchedBimonoidStarStatementAdditiveWellTyped` is NOT proven in r7: its outer legs are the r6 CONV deltas, its
`vcomp` case is the walled B1 wide collision recursion, and its equal-matrices step is the walled B2
`CoxeterWordUnique` bubble-sort — both residuals live.  The upstream star markers
(`fxBunchedBimonoid_correctedStarStaysRSix`, `...correctedStarStillRSixAfterConvDeltas`,
`...spiderNormalFormStarNamedRThree`, `...propGeneralCompletenessStarReached`) stay `= false` byte-intact — NO
fabricated flip. -/
def fxBunchedBimonoid_correctedWellTypedStarStillOpen : Bool := false

/-- ★★★ **ESTABLISHED (B4) — the WP-PROP r7 star-assembly ledger (the honest scoreboard).**  `= true` records the
complete r7 B4 adjudication: the corrected star RE-STATED at its honest `additive AND well-typed` scope
(`fxBunchedBimonoid_restatedStarCarriesWellTypedness` — the recon headline that additivity alone is refutable by
`misdeclaredMu`); the two-guard exclusion of BOTH self-attacks
(`fxBunchedBimonoid_restatedStarExcludesBothCounterexamples`); the retraction legs gated on B1 (wide collision
recursion) and B2 (`CoxeterWordUnique`) (`fxBunchedBimonoid_starLegsGatedOnB1AndB2`).  The star does NOT close
(`fxBunchedBimonoid_correctedWellTypedStarStillOpen = false`); the two heavy residuals (B1 general `wideSwap`
word, B2 general bubble-sort) stay walled byte-intact; every upstream star marker byte-intact — NO fabricated
flip; zero-axiom.  THE STAR = the honest partial ledger, its exact residual nodes named. -/
def fxBunchedBimonoid_starAssemblyRoundSevenLedgerShipped : Bool := true

end FX1Poly.Polygraph.Omega
