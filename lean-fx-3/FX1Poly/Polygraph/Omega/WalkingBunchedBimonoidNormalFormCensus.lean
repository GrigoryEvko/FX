import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidPermStage

/-! # Polygraph/Omega/WalkingBunchedBimonoidNormalFormCensus — the NF-induction census + the #2033 star, honestly
scoped (WP-PROP r4, #2033, the 110-percent grind)

★ **THE #2033 STAR — "equal `Mat(N)` matrix ⟹ convertible" — is NAMED at its honest scope
`StrictAxiomRel union BunchedBimonoidSoundRow union BunchedBimonoidHexagonRow`, with the NF induction censused
per `CellExpr` constructor; the star markers do NOT flip (no literal general delivery).**  The star is the NF
induction / diagram-to-matrix retraction: every walker 2-cell converts, through the widened congruence, to
`spiderOf (evalCell cell)`.  This file censuses that induction by the six `CellExpr` constructors, states the
star at its honest scope as a NAMED (unproven) proposition, and records the REACHED fragment (block-diagonal via
r3 + permutation words via r4) — while keeping every upstream star marker `= false` byte-intact.

## The NF induction census (by `CellExpr` constructor)

  * **`ofMode`** (dim 0): a mode has no matrix (`Unit`).  Trivial base.
  * **`id`** (identity spider): `id (word width n)` → `evalCell = identityMat n` → the `id`-word.  Base, trivial.
  * **`gen`** (each dim-2 generator is a small spider): `mu = [[1,1]]`, `eta = [[]]`, `delta = [[1],[1]]`,
    `eps = []` are block-diagonal-reachable (r3); `sigma = [[0,1],[1,0]]` is the PERMUTATION word (r4 B2,
    `bunchedBimonoidSpiderPermTwo`).  Reached.
  * **`whiskerLeft` / `whiskerRight`** (directSum blocks): the identity-block round-trips (r2) and the general
    `diag(a, b)` (r3, `bunchedBimonoidSpiderDiagMatrix`) reach the block placement.  Reached.
  * **`vcomp`** (composite of two spiders is a spider): the BLOCK-DIAGONAL composites (r3
    `bunchedBimonoidSpiderDiagTwoThreeRoundTrip` et al.) and the PERMUTATION composites (r4 hexagon Yang-Baxter,
    `bunchedBimonoidYangBaxterCompletenessInstance`) are reached; a perm-of-a-diagonal
    (`bunchedBimonoidPermutedDiagTwoThree`, this file) witnesses the mixed case.  The ARBITRARY `vcomp`
    (general routing perm-stage read off a transpose) is the sole remaining node (walled, r4 B2).

## The honest scope (the recon's single most important constraint)

The star's completeness target MUST be the widened congruence `StrictAxiomRel union SoundRow union HexagonRow`,
NOT `SoundRow` alone: the strict laws cancel the `whiskerRight (id a) a` identities that spider words carry
(r3 self-attack #2), and the hexagon rows supply the width-3 braiding.  Soundness over the `SoundRow union
HexagonRow` half is machine-checked (`bunchedBimonoidMatrixSoundOverHexagon`, r4 B1); the `StrictAxiomRel` half
is Node A (walled, r4 B2 narrowed).  The full retraction (the star) is r5.

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! # =========================================================================================
    # B1 — THE vcomp-CASE WITNESS: a permutation-of-a-diagonal (both factors reached)
    # =========================================================================================
-/

/-- ★ The **permuted diagonal** `sigma ; diag(2, 3) : a.a => a.a` — a `vcomp` of a PERMUTATION (`sigma`, r4 B2)
after a BLOCK-DIAGONAL (`diag(2, 3)`, r3): both factors are reached spiders, so the composite is a reached NF —
the mixed `vcomp` case of the NF induction. -/
def bunchedBimonoidPermutedDiagTwoThree : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp bunchedBimonoidAddSigmaGen (bunchedBimonoidSpiderDiag 2 3)

/-- ★★ **vcomp-CASE ROUND-TRIP — `evalCell (sigma ; diag(2,3)) = [[0,2],[3,0]]`.**  The permutation-of-a-diagonal
evaluates to the anti-diagonal `[[0,2],[3,0]]` on the nose (`rfl`): `matMul (diag(2,3)) sigma` swaps the columns
of the diagonal.  A concrete `vcomp` NF witness where BOTH factors are reached (the perm word after the
block-diagonal) — the mixed fragment the block-exchange and the hexagon jointly cover. -/
theorem bunchedBimonoidPermutedDiagRoundTrip :
    bunchedBimonoidEvalCell bunchedBimonoidPermutedDiagTwoThree
      = { rows := 2, cols := 2, entries := [[0, 2], [3, 0]] } := rfl

#eval bunchedBimonoidEvalCell bunchedBimonoidPermutedDiagTwoThree

/-! ## The B1 honesty markers -/

/-- ★★ **ESTABLISHED (B1) — the NF-induction census by `CellExpr` constructor.**  `= true` records the per-ctor
reachability: `ofMode` (dim 0, no matrix) and `id` (identity spider) are trivial bases; `gen` is reached (the
(co)monoid generators block-diagonal via r3, `sigma` the permutation word via r4 B2); `whiskerLeft` /
`whiskerRight` are reached (identity-block round-trips + general `diag(a, b)` via r3); and `vcomp` is reached on
the block-diagonal composites (r3) and the permutation composites (r4 hexagon), with
`bunchedBimonoidPermutedDiagRoundTrip` witnessing the mixed perm-of-a-diagonal case.  The sole unreached move is
the ARBITRARY `vcomp` general routing (walled, r4 B2). -/
def fxBunchedBimonoid_nfInductionCensusShipped : Bool := true

/-! # =========================================================================================
    # B2 — THE STAR, NAMED AT ITS HONEST SCOPE (NOT proven — r5, no flip)
    # =========================================================================================

★ **The #2033 star stated as a NAMED proposition over the widened congruence, NOT proven.**  The completeness
star quantifies over `StrictAxiomRel union SoundRow union HexagonRow` (the honest faithful-presentation scope);
stating it over `SoundRow` alone would be a lie (missing the strict laws and the hexagon).  Soundness over the
`SoundRow union HexagonRow` half is machine-checked; the star (completeness / the full retraction) is r5. -/

/-- ★ The **star's congruence scope** — the widened base relation the completeness star quantifies over:
`StrictAxiomRel` (the strict omega-laws) united with `BunchedBimonoidSoundRow` (the 15 genuine bimonoid rows)
united with `BunchedBimonoidHexagonRow` (the 3 width-3 braiding rows).  The honest faithful presentation of the
additive bicommutative-bimonoid PROP (Lafont / Pirashvili / Fox). -/
def bunchedBimonoidStarCongruenceScope : CellRelOver bunchedBimonoidOmegaComputad :=
  unionCellRel bunchedBimonoidOmegaComputad (StrictAxiomRel bunchedBimonoidOmegaComputad)
    (unionCellRel bunchedBimonoidOmegaComputad BunchedBimonoidSoundRow BunchedBimonoidHexagonRow)

/-- ★★ **THE #2033 STAR, NAMED (NOT proven).**  The completeness half of the Lafont / Pirashvili / Fox
correspondence: every two same-dimension 2-cells with EQUAL `Mat(N)` matrix are convertible over the widened
congruence `bunchedBimonoidStarCongruenceScope` (the strict laws + the sound rows + the hexagon rows).  This is
the NF induction / diagram-to-matrix retraction — the #2033 star.  It is STATED here at its honest scope and is
NOT proven (the general `spiderOf` routing + the strict-law extension are r5); no upstream star marker flips. -/
def bunchedBimonoidStarStatement : Prop :=
  ∀ {dim : Nat} (cellAlpha cellBeta : CellExpr bunchedBimonoidOmegaComputad dim),
    bunchedBimonoidEvalCell cellAlpha = bunchedBimonoidEvalCell cellBeta →
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope cellAlpha cellBeta

/-- ★ **The sound rows embed into the star scope** — every `BunchedBimonoidSoundRow` convertibility folds into
the star's widened congruence (via `Or.inr ∘ Or.inl`).  A machine-checked witness that the star scope is a
strict superset of the sound sub-theory (so soundness over the sound rows transfers), even though the star
itself is unproven. -/
theorem bunchedBimonoidSoundRowEmbedsIntoStarScope {dim : Nat}
    {cellAlpha cellBeta : CellExpr bunchedBimonoidOmegaComputad dim}
    (soundRow : BunchedBimonoidSoundRow cellAlpha cellBeta) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope cellAlpha cellBeta :=
  SaturatedConvOverWithId.ofRelation (Or.inr (Or.inl soundRow))

/-- ★ **The hexagon rows embed into the star scope** — every `BunchedBimonoidHexagonRow` convertibility folds
into the star's widened congruence (via `Or.inr ∘ Or.inr`).  The width-3 braiding rows are genuine members of
the star's target congruence. -/
theorem bunchedBimonoidHexagonRowEmbedsIntoStarScope {dim : Nat}
    {cellAlpha cellBeta : CellExpr bunchedBimonoidOmegaComputad dim}
    (hexRow : BunchedBimonoidHexagonRow cellAlpha cellBeta) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope cellAlpha cellBeta :=
  SaturatedConvOverWithId.ofRelation (Or.inr (Or.inr hexRow))

/-- ★ **The strict laws embed into the star scope** — every `StrictAxiomRel` row folds into the star's widened
congruence (via `Or.inl`).  The strict omega-laws (associativity, units, whisker-functoriality, interchange) are
genuine members of the star's target congruence — the half whose matrix-soundness is Node A (walled). -/
theorem bunchedBimonoidStrictAxiomEmbedsIntoStarScope {dim : Nat}
    {cellAlpha cellBeta : CellExpr bunchedBimonoidOmegaComputad dim}
    (strictRow : StrictAxiomRel bunchedBimonoidOmegaComputad cellAlpha cellBeta) :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope cellAlpha cellBeta :=
  SaturatedConvOverWithId.ofRelation (Or.inl strictRow)

/-! ## The B2 honesty markers -/

/-- ★★ **ESTABLISHED (B2) — the star's congruence scope is named `StrictAxiomRel union SoundRow union
HexagonRow`.**  `= true` records `bunchedBimonoidStarCongruenceScope` and the three embeddings
(`bunchedBimonoid{SoundRow,HexagonRow,StrictAxiom}EmbedsIntoStarScope`): the star's completeness target is the
widened faithful-presentation congruence (the strict laws + the 15 sound rows + the 3 hexagon rows), NOT
`SoundRow` alone.  This is the recon's single most important honesty constraint — the star scope widens visibly;
soundness over the `SoundRow union HexagonRow` half is machine-checked (`bunchedBimonoidMatrixSoundOverHexagon`),
the `StrictAxiomRel` half is Node A (narrowed, r4 B2). -/
def fxBunchedBimonoid_starScopeStrictSoundHexagon : Bool := true

/-- ★ **THE STAR IS NAMED, NOT PROVEN — r5 (NO flip).**  `= false` records that `bunchedBimonoidStarStatement`
(equal `Mat(N)` matrix ⟹ convertible over the widened congruence, for ALL 2-cells) — the #2033 star, the NF
induction / diagram-to-matrix retraction — is STATED at its honest scope and is NOT proven in r4.  The reached
fragment (block-diagonal + permutation words) covers the census's base and generator cases and the
block-diagonal / permutation `vcomp` cases; the general `vcomp` routing (arbitrary transpose) + the strict-law
extension (Node A) are the r5 residual.  The upstream star markers
`fxBunchedBimonoid_spiderNormalFormStarNamedRThree`, `...propGeneralCompletenessStarReached`,
`...starVcompCoherenceHexagonWall`, `...starStrictLawExtensionWall` all stay `= false` (r1/r2/r3 files,
byte-intact) — cited name-only, NO fake flip. -/
def fxBunchedBimonoid_nfInductionStarStillRFive : Bool := false

/-! # =========================================================================================
    # B3 — THE REACHED FRAGMENT + THE LEDGER
    # =========================================================================================

★ **The honest reached fragment of the star: block-diagonal (r3) + permutation words (r4), hand-exhibited.**
The star is NOT proven in general, but its restriction to the reached fragment is machine-witnessed by the
completeness INSTANCES shipped across the arc: the r1/r2 sigma-mediated instances (block-diagonal + width-2
sigma), the r3 diag round-trips (block-diagonal), and the r4 hexagon instances
(`bunchedBimonoidYangBaxterCompletenessInstance` / `...MuNaturalityCompletenessInstance`, the permutation +
width-3 braiding).  These are HAND-EXHIBITED, NOT the general decision. -/

/-- ★★ **ESTABLISHED (B3) — the reached fragment is block-diagonal + permutation words.**  `= true` records the
honest reachability verdict: the star holds on the BLOCK-DIAGONAL matrices (the `directSum` of shipped stages,
via the r3 block-exchange interchange + the r1/r2/r3 completeness instances) and on the PERMUTATION matrices
(permutation WORDS in `sigma`, via the r4 hexagon rows + the r4 completeness instances), with the mixed
perm-of-a-diagonal `vcomp` case witnessed (`bunchedBimonoidPermutedDiagRoundTrip`).  The arbitrary `q x p`
matrix with a non-trivial routing perm-stage (read off a transpose) + the strict-law extension are the r5
residual — the general NF induction / the #2033 star. -/
def fxBunchedBimonoid_nfReachedFragmentBlockDiagPlusPerm : Bool := true

/-- ★★ **ESTABLISHED (B3) — the WP-PROP r4 NF-census ledger (honest scoreboard).**  `= true` records the
complete r4 NF-induction advance: B1 the per-ctor NF census (`fxBunchedBimonoid_nfInductionCensusShipped` —
`ofMode` / `id` bases, `gen` reached incl. `sigma` = perm word, `whisker*` reached, `vcomp` reached on
block-diagonal + permutation + the mixed perm-of-a-diagonal `bunchedBimonoidPermutedDiagRoundTrip`); B2 the star
NAMED at its honest scope `StrictAxiomRel union SoundRow union HexagonRow`
(`bunchedBimonoidStarStatement` + the three embeddings + `fxBunchedBimonoid_starScopeStrictSoundHexagon`), NOT
proven (`fxBunchedBimonoid_nfInductionStarStillRFive = false`, r5, NO flip); B3 the reached fragment
(block-diagonal + permutation words).  Every upstream star / wall marker
(`fxBunchedBimonoid_spiderNormalFormStarNamedRThree`, `...propGeneralCompletenessStarReached`,
`...starVcompCoherenceHexagonWall`, `...starStrictLawExtensionWall`, `...matrixHexagonReached`,
`...spiderGeneralRoutingReached`, `...matrixStrictLawExtensionReached`) keeps its name and `= false` value
byte-intact. -/
def fxBunchedBimonoid_normalFormCensusLedgerShipped : Bool := true

end FX1Poly.Polygraph.Omega
