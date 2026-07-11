import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidMiddleDeterminism

/-! # Polygraph/Omega/WalkingBunchedBimonoidCoxeterUniqueness — the perm-middle Coxeter word-problem advanced: the
DISTANT commutation is DERIVED from the Godement interchange (no new row), and the complete set of Coxeter /
double-coset moves is machine-witnessed in scope, with the general `CoxeterWordUnique` bubble-sort honestly walled
(WP-PROP r7, #2033, the 110-percent grind)

★ **The recon's Job-2 decisive finding, machine-witnessed.**  The r6 `MiddleDeterminism` adjudicated the
perm-middle determinism as a Coxeter word-problem (NOT free) and shipped its two decidable ends (the width-2
involution `s_1 s_1 = e` and the width-3 Yang-Baxter braid `s_1 s_2 s_1 = s_2 s_1 s_2`).  The recon's explicit ask
on `StrictAxiomRel` was whether the DISTANT commutation `s_i s_j = s_j s_i` (`|i-j| >= 2`) needs a NEW row.  The
answer is NO: it is DERIVABLE from the Godement `interchange` row.  This file proves exactly that.

## Distant commutation IS the Godement interchange (no new row)

Two whiskered `sigma`s on DISJOINT strand ranges commute: `(sigma |> a.a) ; (a.a <| sigma) ~ (a.a <| sigma) ;
(sigma |> a.a)` on `a.a.a.a` (swap the first pair, then the last pair, vs. the reverse).  This is EXACTLY the
`StrictAxiomRel.interchange` row instantiated at `alpha = beta = sigma_a` (both boundaries `a.a`), fired through
the star scope's `Or.inl` selector.  `bunchedBimonoidDistantSwapCommuteViaInterchange` is a ONE-STEP fire; both
legs share the `4 x 4` permutation matrix `[[0,1,0,0],[1,0,0,0],[0,0,0,1],[0,0,1,0]]`.  So the disjoint-range
`s_1 s_3 = s_3 s_1` needs NO new row family.

## The complete Coxeter / double-coset move set is in scope

`bunchedBimonoidCoxeterMovesAllInScope` bundles the FIVE move families the bubble-sort `CoxeterWordUnique` needs,
each a convertibility over the star scope: DISTANT commutation (interchange, this file), the ADJACENT braid
(Yang-Baxter, r6), the INVOLUTION `s^2 = e` (r6), and the two DOUBLE-COSET generators commutativity `mu.sigma =
mu` / cocommutativity `sigma.delta = delta` (sound rows).  Every move is already a member of
`bunchedBimonoidStarCongruenceScope` — no new row family is needed for r7 (the recon's decisive verdict).

## The sorted-form verdict + the walled general lemma

The perm middle lives only up to the Young double coset `S_{col-sums} x S_{row-sums}`, so there is NO unique
canonical sorted perm WORD; the honest target is CONVERTIBILITY to a COMMON word (an equivalence), proved by a
STRUCTURAL bubble-sort fuel on the inversion count.  That general induction is the r6/r7 residual, walled
byte-intact — the moves are all in scope but their fuel-recursive assembly is the genuine work.

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! The width-4 permutation `rfl` matrix reductions exceed the default heartbeat budget; the raise is a compute
allowance only, the proof terms stay `Eq.refl`, axiom-free (uniform with the r6 `MiddleDeterminism`). -/
set_option maxHeartbeats 4000000

/-! # =========================================================================================
    # B2 — DISTANT COMMUTATION IS THE GODEMENT INTERCHANGE (no new row)
    # =========================================================================================
-/

/-- The **distant-swap LEFT leg** `(sigma |> a.a) ; (a.a <| sigma) : a.a.a.a => a.a.a.a` — swap the first pair of
strands, then the last pair (two swaps on DISJOINT ranges, `s_1 s_3`). -/
def bunchedBimonoidDistantSwapLeftLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen bunchedBimonoidAaWord)
    (CellExpr.whiskerLeft bunchedBimonoidAaWord bunchedBimonoidAddSigmaGen)

/-- The **distant-swap RIGHT leg** `(a.a <| sigma) ; (sigma |> a.a) : a.a.a.a => a.a.a.a` — the reverse order
(`s_3 s_1`). -/
def bunchedBimonoidDistantSwapRightLeg : CellExpr bunchedBimonoidOmegaComputad 2 :=
  CellExpr.vcomp (CellExpr.whiskerLeft bunchedBimonoidAaWord bunchedBimonoidAddSigmaGen)
    (CellExpr.whiskerRight bunchedBimonoidAddSigmaGen bunchedBimonoidAaWord)

/-! ## B2 truth-probe outputs (both distant-swap orders share their matrix) -/

#eval bunchedBimonoidEvalCell bunchedBimonoidDistantSwapLeftLeg
#eval bunchedBimonoidEvalCell bunchedBimonoidDistantSwapRightLeg

/-- ★★★ **DISTANT COMMUTATION IS THE GODEMENT INTERCHANGE — no new row.**  The two disjoint-range swaps `s_1 s_3`
and `s_3 s_1` are convertible over the star scope by a SINGLE `StrictAxiomRel.interchange` fire at
`alpha = beta = sigma_a` (both boundaries `a.a`, so the row's `whiskerRight alpha (src beta)` / `whiskerLeft (tgt
alpha) beta` shapes are exactly the two whiskered `sigma`s).  This machine-witnesses the recon's decisive Job-2
verdict: distant commutation `s_i s_j = s_j s_i` (`|i-j| >= 2`) is DERIVABLE from the interchange, NOT a new row
family. -/
theorem bunchedBimonoidDistantSwapCommuteViaInterchange :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      bunchedBimonoidDistantSwapLeftLeg bunchedBimonoidDistantSwapRightLeg :=
  SaturatedConvOverWithId.ofRelation
    (Or.inl (StrictAxiomRel.interchange bunchedBimonoidAddSigmaGen bunchedBimonoidAddSigmaGen))

/-- ★ **The distant-swap legs share their matrix** — both evaluate to the `4 x 4` permutation
`[[0,1,0,0],[1,0,0,0],[0,0,0,1],[0,0,1,0]]` (swap strands 0-1 and 2-3).  So the interchange conv above genuinely
relates two REPRESENTATIVES of the same permutation — the determinism content at width 4. -/
theorem bunchedBimonoidDistantSwapMatrixShared :
    bunchedBimonoidEvalCell bunchedBimonoidDistantSwapLeftLeg
      = bunchedBimonoidEvalCell bunchedBimonoidDistantSwapRightLeg := rfl

/-! # =========================================================================================
    # B2 — THE COMPLETE COXETER / DOUBLE-COSET MOVE SET IS IN SCOPE
    # =========================================================================================
-/

/-- ★ **The commutativity double-coset move `mu.sigma = mu` is in scope** — fired through the star scope's sound
sub-theory (`Or.inr (Or.inl commutativity)`).  One of the two double-coset generators that absorb intra-block
strand permutations in the bubble-sort. -/
theorem bunchedBimonoidCommutativityOverStar :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      bunchedBimonoidCommutativityLeftLeg bunchedBimonoidCommutativityRightLeg :=
  SaturatedConvOverWithId.ofRelation (Or.inr (Or.inl BunchedBimonoidSoundRow.commutativity))

/-- ★ **The cocommutativity double-coset move `sigma.delta = delta` is in scope** — the dual double-coset
generator (`Or.inr (Or.inl cocommutativity)`). -/
theorem bunchedBimonoidCocommutativityOverStar :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      bunchedBimonoidCocommutativityLeftLeg bunchedBimonoidCocommutativityRightLeg :=
  SaturatedConvOverWithId.ofRelation (Or.inr (Or.inl BunchedBimonoidSoundRow.cocommutativity))

/-- ★★★ **ALL FIVE COXETER / DOUBLE-COSET MOVES ARE IN SCOPE (no new row family).**  The bundle the bubble-sort
`CoxeterWordUnique` needs, each a convertibility over `bunchedBimonoidStarCongruenceScope`: (1) DISTANT commutation
`s_1 s_3 = s_3 s_1` via the Godement interchange (this file); (2) the ADJACENT braid `s_1 s_2 s_1 = s_2 s_1 s_2`
via Yang-Baxter (r6 `bunchedBimonoidYangBaxterDeterminismOverStar`); (3) the INVOLUTION `s^2 = e` via
sigma-involution (r6 `bunchedBimonoidInvolutionDeterminismOverStar`); (4) commutativity `mu.sigma = mu` and (5)
cocommutativity `sigma.delta = delta`, the two double-coset generators.  Every move is already a member of the
star scope — the recon's decisive verdict that NO new row family is needed for r7, machine-checked. -/
theorem bunchedBimonoidCoxeterMovesAllInScope :
    (SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
        bunchedBimonoidDistantSwapLeftLeg bunchedBimonoidDistantSwapRightLeg)
    ∧ (SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
        bunchedBimonoidYangBaxterLeftLeg bunchedBimonoidYangBaxterRightLeg)
    ∧ (SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
        bunchedBimonoidSigmaInvolutionLeftLeg bunchedBimonoidSigmaInvolutionRightLeg)
    ∧ (SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
        bunchedBimonoidCommutativityLeftLeg bunchedBimonoidCommutativityRightLeg)
    ∧ (SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
        bunchedBimonoidCocommutativityLeftLeg bunchedBimonoidCocommutativityRightLeg) :=
  ⟨bunchedBimonoidDistantSwapCommuteViaInterchange,
    bunchedBimonoidYangBaxterDeterminismOverStar,
    bunchedBimonoidInvolutionDeterminismOverStar,
    bunchedBimonoidCommutativityOverStar,
    bunchedBimonoidCocommutativityOverStar⟩

/-! ## The B2 markers -/

/-- ★★ **ESTABLISHED (B2) — distant commutation is the Godement interchange (no new row).**  `= true` records
`bunchedBimonoidDistantSwapCommuteViaInterchange` (the disjoint-range swaps `s_1 s_3` / `s_3 s_1` convertible by a
single `StrictAxiomRel.interchange` fire) with the shared `4 x 4` matrix witness.  The recon's explicit
`StrictAxiomRel` question answered: distant commutation `|i-j| >= 2` needs NO new row family. -/
def fxBunchedBimonoid_distantCommutationIsInterchange : Bool := true

/-- ★★ **ESTABLISHED (B2) — the complete Coxeter / double-coset move set is in scope.**  `= true` records
`bunchedBimonoidCoxeterMovesAllInScope`: all five move families the bubble-sort `CoxeterWordUnique` needs (distant
commutation via interchange, adjacent braid via Yang-Baxter, involution `s^2 = e`, and the two double-coset
generators commutativity / cocommutativity) are convertibilities over the star scope.  No new row family is needed
for r7 — the recon's decisive verdict, machine-checked. -/
def fxBunchedBimonoid_coxeterMovesAllInScope : Bool := true

/-- ★ **THE SORTED-FORM VERDICT — convertibility to a COMMON word, NOT a unique normal form.**  `= true` records
the recon's adjudication: the perm middle lives only up to the Young double coset `S_{col-sums} x S_{row-sums}`, so
there is NO total invariant "canonical sorted perm word"; the honest target of `CoxeterWordUnique` is
CONVERTIBILITY to a common word (an equivalence), proved by a STRUCTURAL bubble-sort fuel on the inversion count
using the five in-scope moves.  Confluence, not a normal form. -/
def fxBunchedBimonoid_sortedFormIsConfluenceNotNormalForm : Bool := true

/-! # =========================================================================================
    # B2 — THE HONEST RESIDUAL (the general CoxeterWordUnique bubble-sort, walled)
    # =========================================================================================
-/

/-- ★ **THE GENERAL `CoxeterWordUnique` BUBBLE-SORT STAYS UNBUILT — no flip.**  `= false` records that the general
lemma (two `sigma`-words of the same permutation matrix are convertible over the star scope, by STRUCTURAL
bubble-sort fuel on the inversion count) is NOT shipped: its two decidable ends are shipped (r6
`bunchedBimonoidPermMiddleDeterminismDecidableEnds`), and ALL FIVE of its moves are now witnessed in scope
(`bunchedBimonoidCoxeterMovesAllInScope`), but the fuel-recursive assembly of those moves into the general
confluence is the genuine work.  Byte-intact with the r6
`fxBunchedBimonoid_coxeterWordUniqueMinimalLemmaUnbuilt`. -/
def fxBunchedBimonoid_coxeterWordUniqueBubbleSortStillUnbuilt : Bool := false

/-- ★★ **ESTABLISHED (B2) — the WP-PROP r7 Coxeter-uniqueness ledger (honest scoreboard).**  `= true` records the
r7 B2 advance: distant commutation IS the Godement interchange
(`fxBunchedBimonoid_distantCommutationIsInterchange` — no new row, the recon's decisive `StrictAxiomRel` finding);
the complete five-move Coxeter / double-coset set in scope (`fxBunchedBimonoid_coxeterMovesAllInScope`); the
sorted-form verdict (`fxBunchedBimonoid_sortedFormIsConfluenceNotNormalForm` — confluence, not a normal form).  The
general `CoxeterWordUnique` bubble-sort stays walled byte-intact
(`fxBunchedBimonoid_coxeterWordUniqueBubbleSortStillUnbuilt = false`) with the r6
`fxBunchedBimonoid_coxeterWordUniqueMinimalLemmaUnbuilt`.  No star marker flips; zero-axiom. -/
def fxBunchedBimonoid_coxeterUniquenessRoundSevenLedgerShipped : Bool := true

end FX1Poly.Polygraph.Omega
