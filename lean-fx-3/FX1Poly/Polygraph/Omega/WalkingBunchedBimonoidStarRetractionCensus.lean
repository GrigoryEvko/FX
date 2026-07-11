import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidNormalFormCensus
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidMatrixReconstruction

/-! # Polygraph/Omega/WalkingBunchedBimonoidStarRetractionCensus — the NF-induction base + whisker census, the
CORRECTED (additive-restricted) star, the width-2 vcomp-collision witness, and the honest r6 residual ledger
(WP-PROP r5, #2033, the 110-percent grind)

★ **Three honest deliverables layered on the r4 star scope:**

  * **B2 — the NF-induction base + generator + whisker census** (each generator's staged-form MATRIX witnessed by
    `rfl`): the `id`-cell base evaluates to the identity matrix; the five additive generators each evaluate to
    their staged-form matrix (`mu_a = muFold 2`, `delta_a = deltaFan 2`, `eta_a = muFold 0`, `eps_a = deltaFan 0`,
    `sigma_a` the permutation matrix); the whisker cases evaluate to the block-diagonal placement.
  * **THE STAR-STATEMENT CORRECTION (non-optional).**  The r4 `bunchedBimonoidStarStatement` quantifies over ALL
    same-dimension 2-cells, INCLUDING mult-coloured ones; but `bunchedBimonoidGenMatrix` sends `mu_m` and `mu_a`
    to the SAME matrix `[[1,1]]` while `mu_m` and `mu_a` are NOT convertible (`bunchedBimonoidColours_distinct`).
    So the star AS STATED is refutable.  This file ships the concrete refutation datum
    (`bunchedBimonoidMixedMuEqualMatrix`: equal matrix across colours) and the CORRECTED domain-restricted star
    `bunchedBimonoidStarStatementAdditive` (both cells drawn from the additive-colour fragment), together with the
    witnesses that the additive predicate EXCLUDES `mu_m` (so the counterexample cannot satisfy the corrected
    hypothesis).
  * **B3/B4 — the width-2 vcomp collision, matrix-witnessed, + the honest r6 residual ledger.**  The width-2
    bialgebra collision `mu_a ; delta_a` evaluates to the all-ones `[[1,1],[1,1]]` (the resolved bialgebra RHS's
    matrix), and the `1 x 1` collision `delta_a ; mu_a` to the scalar `[[2]]`.  The CONVERTIBILITY-level wide
    collision recursion (the `(m,n)`-grid double induction assembling the wide swap from elementary `sigma`s via
    the hexagon) AND the middle-determinism double-coset canonicalization are the genuine r6 research residuals,
    each NAMED here with its exact goal — NO fake flip.

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! # =========================================================================================
    # B2 — THE NF-INDUCTION BASE + GENERATOR + WHISKER CENSUS (staged-form matrix witnesses)
    # =========================================================================================
-/

/-- ★ **The `id`-cell base evaluates to the identity matrix** — `evalCell (id (a.a)) = identityMat 2`.  The NF
induction's identity base: an identity spider IS the identity matrix on its width. -/
theorem bunchedBimonoidIdCellStagedWitness :
    bunchedBimonoidEvalCell (CellExpr.id bunchedBimonoidAaWord)
      = bunchedBimonoidIdentityMat 2 := rfl

/-- ★ **`mu_a` is the `muFold 2` spider** — `evalCell mu_a = evalCell (muFold 2)` (both `[[1,1]]`).  The additive
multiplication generator's staged form. -/
theorem bunchedBimonoidAddMuStagedWitness :
    bunchedBimonoidEvalCell bunchedBimonoidAddMuGen
      = bunchedBimonoidEvalCell (bunchedBimonoidMuFold 2) := rfl

/-- ★ **`delta_a` is the `deltaFan 2` spider** — `evalCell delta_a = evalCell (deltaFan 2)` (both `[[1],[1]]`). -/
theorem bunchedBimonoidAddDeltaStagedWitness :
    bunchedBimonoidEvalCell bunchedBimonoidAddDeltaGen
      = bunchedBimonoidEvalCell (bunchedBimonoidDeltaFan 2) := rfl

/-- ★ **`eta_a` is the `muFold 0` spider** — `evalCell eta_a = evalCell (muFold 0)` (both the `1 x 0` empty
row). -/
theorem bunchedBimonoidAddEtaStagedWitness :
    bunchedBimonoidEvalCell bunchedBimonoidAddEtaGen
      = bunchedBimonoidEvalCell (bunchedBimonoidMuFold 0) := rfl

/-- ★ **`eps_a` is the `deltaFan 0` spider** — `evalCell eps_a = evalCell (deltaFan 0)` (both the `0 x 1` empty
column). -/
theorem bunchedBimonoidAddEpsStagedWitness :
    bunchedBimonoidEvalCell bunchedBimonoidAddEpsGen
      = bunchedBimonoidEvalCell (bunchedBimonoidDeltaFan 0) := rfl

/-- ★ **`sigma_a` is the swap permutation matrix** — `evalCell sigma_a = [[0,1],[1,0]]`.  The additive swap
generator is the perm-stage word (the `2 x 2` permutation matrix). -/
theorem bunchedBimonoidAddSigmaStagedWitness :
    bunchedBimonoidEvalCell bunchedBimonoidAddSigmaGen
      = { rows := 2, cols := 2, entries := [[0, 1], [1, 0]] } := rfl

/-- ★ **The whisker case evaluates to the block-diagonal placement** — `evalCell (whiskerLeft a mu_a) =
directSum (identityMat 1) [[1,1]] = [[1,0,0],[0,1,1]]`.  The left whisker conjugates the whiskered cell by the
whisker's identity block placed FIRST. -/
theorem bunchedBimonoidWhiskerLeftStagedWitness :
    bunchedBimonoidEvalCell (CellExpr.whiskerLeft bunchedBimonoidAdditiveGen bunchedBimonoidAddMuGen)
      = { rows := 2, cols := 3, entries := [[1, 0, 0], [0, 1, 1]] } := rfl

/-- ★★ **ESTABLISHED (B2) — the NF-induction base + generator + whisker census is matrix-witnessed.**  `= true`
records the per-`CellExpr`-constructor staged-form MATRIX agreements: the `id` base (identity matrix); the five
additive generators (`mu_a = muFold 2`, `delta_a = deltaFan 2`, `eta_a = muFold 0`, `eps_a = deltaFan 0`,
`sigma_a` the swap matrix); and the whisker block-diagonal placement.  Each `rfl`; the semantic side of the NF
induction's base / generator / whisker cases. -/
def fxBunchedBimonoid_nfBaseGeneratorWhiskerCensusMatrixWitnessed : Bool := true

/-! # =========================================================================================
    # THE STAR-STATEMENT CORRECTION — the additive-colour restriction (non-optional)
    # =========================================================================================

★ **The r4 `bunchedBimonoidStarStatement` is refutable as stated: mult and additive generators with equal
matrices are non-convertible.  The corrected star restricts the domain to the additive-colour fragment.** -/

/-- **Is a generator label additive-coloured?**  `true` for the six additive-family labels (`additiveColour`,
`addMult`, `addUnit`, `addComult`, `addCounit`, `addSwap`), `false` for the three mult-family labels.  Full
nine-arm split — propext-clean. -/
def bunchedBimonoidLabelIsAdditive : BunchedBIGenLabel → Bool
  | .additiveColour => true
  | .addMult => true
  | .addUnit => true
  | .addComult => true
  | .addCounit => true
  | .addSwap => true
  | .multColour => false
  | .multMult => false
  | .multUnit => false

/-- **Does a cell use ONLY additive-colour generators?**  A structural `Bool` fold over all six `CellExpr`
constructors (mirroring `bunchedBimonoidEvalCell`): every `gen` label must be additive, and every sub-cell must
recursively use only additive generators.  Propext-clean (Bool `&&`). -/
def bunchedBimonoidCellUsesOnlyAdditive : {dim : Nat} → CellExpr bunchedBimonoidOmegaComputad dim → Bool
  | _, .ofMode _ => true
  | _, .gen label source target =>
      bunchedBimonoidLabelIsAdditive label
        && bunchedBimonoidCellUsesOnlyAdditive source && bunchedBimonoidCellUsesOnlyAdditive target
  | _, .id cell => bunchedBimonoidCellUsesOnlyAdditive cell
  | _, .vcomp leftCell rightCell =>
      bunchedBimonoidCellUsesOnlyAdditive leftCell && bunchedBimonoidCellUsesOnlyAdditive rightCell
  | _, .whiskerLeft whiskerCell cell =>
      bunchedBimonoidCellUsesOnlyAdditive whiskerCell && bunchedBimonoidCellUsesOnlyAdditive cell
  | _, .whiskerRight cell whiskerCell =>
      bunchedBimonoidCellUsesOnlyAdditive cell && bunchedBimonoidCellUsesOnlyAdditive whiskerCell

/-- ★★ **THE CORRECTED #2033 STAR, NAMED (NOT proven).**  The additive-colour-restricted completeness star: every
two same-dimension 2-cells DRAWN FROM THE ADDITIVE-COLOUR FRAGMENT with EQUAL `Mat(N)` matrix are convertible over
the widened congruence `bunchedBimonoidStarCongruenceScope`.  The domain restriction
(`bunchedBimonoidCellUsesOnlyAdditive _ = true`) is exactly what the r4 star was MISSING — without it the star is
refutable (`bunchedBimonoidMixedMuEqualMatrix` below).  Still NOT proven (the wide vcomp collision + the
middle-determinism are r6); stated at its HONEST, non-refutable scope. -/
def bunchedBimonoidStarStatementAdditive : Prop :=
  ∀ {dim : Nat} (cellAlpha cellBeta : CellExpr bunchedBimonoidOmegaComputad dim),
    bunchedBimonoidCellUsesOnlyAdditive cellAlpha = true →
    bunchedBimonoidCellUsesOnlyAdditive cellBeta = true →
    bunchedBimonoidEvalCell cellAlpha = bunchedBimonoidEvalCell cellBeta →
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope cellAlpha cellBeta

/-- ★★ **THE REFUTATION DATUM — mult and additive multiplications have EQUAL matrices.**  `evalCell mu_m =
evalCell mu_a` (both `[[1,1]]`), on the nose.  Since `mu_m` and `mu_a` are NOT convertible (distinct colours,
`bunchedBimonoidColours_distinct`), this equal-matrix pair is a counterexample to the UNRESTRICTED
`bunchedBimonoidStarStatement` — the r4 star quantifies over both, so its conclusion (convertibility) would be
false here.  This is why the additive-colour restriction is mandatory. -/
theorem bunchedBimonoidMixedMuEqualMatrix :
    bunchedBimonoidEvalCell bunchedBimonoidMultMuGen = bunchedBimonoidEvalCell bunchedBimonoidAddMuGen := rfl

/-- ★ **The additive multiplication IS in the additive fragment** — `cellUsesOnlyAdditive mu_a = true`. -/
theorem bunchedBimonoidAddMuIsAdditive :
    bunchedBimonoidCellUsesOnlyAdditive bunchedBimonoidAddMuGen = true := rfl

/-- ★ **The mult multiplication is EXCLUDED from the additive fragment** — `cellUsesOnlyAdditive mu_m = false`.
So the `(mu_m, mu_a)` counterexample CANNOT satisfy the corrected star's hypothesis (which requires BOTH cells
additive): the corrected `bunchedBimonoidStarStatementAdditive` is not refuted by the mixed-colour datum. -/
theorem bunchedBimonoidMultMuIsNotAdditive :
    bunchedBimonoidCellUsesOnlyAdditive bunchedBimonoidMultMuGen = false := rfl

/-- ★★ **ESTABLISHED — the star statement is corrected to its honest (non-refutable) additive scope.**  `= true`
records the correction: the refutation datum (`bunchedBimonoidMixedMuEqualMatrix` — equal matrix across colours),
the additive-fragment predicate (`bunchedBimonoidCellUsesOnlyAdditive`), the corrected star
(`bunchedBimonoidStarStatementAdditive`), and the exclusion witnesses (`mu_a` in / `mu_m` out).  The r4
`bunchedBimonoidStarStatement` (all 2-cells) stays byte-intact and is name-only flagged refutable; the corrected
star is the r5 replacement target. -/
def fxBunchedBimonoid_starStatementCorrectedToAdditiveScope : Bool := true

/-- ★ **THE UNRESTRICTED r4 STAR IS REFUTABLE — named, byte-intact.**  `= false` records that
`bunchedBimonoidStarStatement` (r4 NormalFormCensus, quantifying over ALL same-dimension 2-cells including
mult-coloured ones) is REFUTABLE: `bunchedBimonoidMixedMuEqualMatrix` exhibits an equal-matrix pair
`(mu_m, mu_a)` that is non-convertible.  The r4 marker keeps its name and value byte-intact; this `= false`
records that the unrestricted named proposition should not be the completeness target — the corrected
`bunchedBimonoidStarStatementAdditive` is. -/
def fxBunchedBimonoid_unrestrictedStarIsRefutable : Bool := false

/-! # =========================================================================================
    # B3 — THE WIDTH-2 vcomp COLLISION (matrix-witnessed) + the honest r6 residual ledger
    # =========================================================================================
-/

/-- ★★ **The width-2 bialgebra collision `mu_a ; delta_a` evaluates to the all-ones matrix** — `evalCell (vcomp
mu_a delta_a) = [[1,1],[1,1]]`.  This is the `2 x 2` "brick wall" the bialgebra rewrite resolves: multiply then
comultiply.  Its matrix EQUALS the resolved bialgebra RIGHT leg `(mu (x) mu).(1 (x) sigma (x) 1).(delta (x)
delta)` matrix (both `[[1,1],[1,1]]`) — the matrix side of the width-2 collision resolution. -/
theorem bunchedBimonoidWidthTwoCollisionMatrix :
    bunchedBimonoidEvalCell (CellExpr.vcomp bunchedBimonoidAddMuGen bunchedBimonoidAddDeltaGen)
      = { rows := 2, cols := 2, entries := [[1, 1], [1, 1]] } := rfl

/-- ★ **The `1 x 1` collision `delta_a ; mu_a` evaluates to the scalar `[[2]]`** — `evalCell (spiderScalar 2) =
[[2]]`, the fan-then-fold multiplicity.  The degenerate `(m,n)=(1,1)` case of the collision recursion (self-attack
#1: `spiderScalar 2 = vcomp delta_a mu_a`, matrix-witnessed here). -/
theorem bunchedBimonoidScalarCollisionMatrix :
    bunchedBimonoidEvalCell (bunchedBimonoidSpiderScalar 2)
      = { rows := 1, cols := 1, entries := [[2]] } := rfl

/-- ★★ **ESTABLISHED (B3) — the width-2 vcomp collision is matrix-witnessed.**  `= true` records the semantic
side of the collision resolution: the `2 x 2` bialgebra collision `mu_a ; delta_a` and the resolved bialgebra RHS
both evaluate to `[[1,1],[1,1]]`; the `1 x 1` collision `delta_a ; mu_a` to the scalar `[[2]]`.  The
CONVERTIBILITY-level resolution (firing `bialgebraProduct` on the adjacent `(mu, delta)` pair) is the single
width-2 brick; its wide generalization is the r6 residual below. -/
def fxBunchedBimonoid_widthTwoCollisionMatrixWitnessed : Bool := true

/-! # =========================================================================================
    # B4 — THE HONEST r6 RESIDUAL LEDGER (the star assembly, NOT flipped)
    # =========================================================================================

★ **The star (the full retraction) does NOT close in r5.  Two genuine research residuals remain, each NAMED with
its exact goal.  No star marker flips.** -/

/-- ★ **r6 RESIDUAL (1) — the WIDE vcomp collision recursion is NOT shipped.**  `= false` records the exact goal:
a double induction on the collision-grid dimensions `(m, n)` proving `muFold m ; deltaFan n` convertible (over
`bunchedBimonoidStarCongruenceScope`) to `deltaStage(m,n) ; wideSwap(m,n) ; muStage(m,n)`, where each induction
step fires ONE width-2 `bialgebraProduct` brick and threads the elementary `sigma` it generates across the
remaining `mu`/`delta` via the hexagon naturality rows (`muNaturality` / `deltaNaturality`) + whisker congruence,
recursing on the reduced `(m-1, n)` / `(m, n-1)` sub-grid.  The width-2 base (`m,n <= 2`) is
matrix-witnessed (`fxBunchedBimonoid_widthTwoCollisionMatrixWitnessed`); the wide recursion is the genuine work. -/
def fxBunchedBimonoid_r6WideCollisionRecursion : Bool := false

/-- ★ **r6 RESIDUAL (2) — the middle-determinism double-coset canonicalization is NOT shipped.**  `= false`
records the exact goal: the perm-stage word of a staged spider is determined by its matrix ONLY UP TO the
fan/fold (co)commutativity — the Young double coset `S_{col-sums} x S_{row-sums}` — so any two perm-stage
representatives of the same matrix are convertible via the hexagon (Yang-Baxter / Coxeter) rows + the
commutativity / cocommutativity rows.  This is Node C's HONEST replacement (a Coxeter word-problem, NOT a
transpose): the recon's Job-2 verdict is that the general routing transpose is NEVER built — the routing lives in
the perm-word, generated locally by the collision recursion.  The delta-stage (column-sum fan) and mu-stage
(row-sum fold) ARE matrix-determined; only the perm middle needs the double-coset lemma. -/
def fxBunchedBimonoid_r6MiddleDeterminismDoubleCoset : Bool := false

/-- ★ **THE STAR (the retraction) STAYS r6 — no flip.**  `= false` records that
`bunchedBimonoidStarStatementAdditive` (the corrected, honestly-scoped star) is NOT proven in r5: it needs both
r6 residuals (the wide vcomp collision recursion + the middle-determinism double-coset canonicalization) composed
with the shipped Node A matrix laws (`bunchedBimonoidMatMulAssoc` + `bunchedBimonoidIdentity{Right,Left}Unit`, B1)
and the r4 hexagon soundness.  The upstream star markers
(`fxBunchedBimonoid_spiderNormalFormStarNamedRThree`, `...propGeneralCompletenessStarReached`,
`...nfInductionStarStillRFive`) all stay `= false` byte-intact — NO fake flip. -/
def fxBunchedBimonoid_correctedStarStaysRSix : Bool := false

/-- ★★★ **ESTABLISHED (B4) — the WP-PROP r5 grand ledger (the honest scoreboard).**  `= true` records the
complete r5 advance: B1 the reconstruction + Fubini kit + BOTH Node A residuals at full generality (general
`matMul` associativity + general-`n` identity units, zero-axiom); B2 the NF-induction base + generator + whisker
census matrix-witnessed; the star-statement CORRECTION to its honest additive-colour scope (the r4 unrestricted
star named refutable, the corrected `bunchedBimonoidStarStatementAdditive` its replacement); B3 the width-2 vcomp
collision matrix-witnessed; B4 the two genuine r6 residuals NAMED with exact goals (the wide vcomp collision
recursion + the middle-determinism double-coset canonicalization), the corrected star NOT flipped
(`fxBunchedBimonoid_correctedStarStaysRSix = false`).  Every upstream `= false` marker byte-intact; additive-only;
Node C (the transpose) never built (recon Job-2). -/
def fxBunchedBimonoid_roundFiveGrandLedgerShipped : Bool := true

end FX1Poly.Polygraph.Omega
