import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidStarRetractionCensus

/-! # Polygraph/Omega/WalkingBunchedBimonoidMiddleDeterminism — the perm-middle determinism adjudicated: NOT free,
but bounded to a Coxeter word-problem, with the width-2 involution + width-3 Yang-Baxter determinism instances
lifted to the star scope and the general double-coset lemma walled (WP-PROP r6, #2033, the 110-percent grind)

★ **The recon's Job-2 verdict, machine-witnessed at its two decidable ends.**  The staged spider normal form is
`spiderStaged (deltaStage) (permStage) (muStage)`.  The delta-stage (column-sum fan) and mu-stage (row-sum fold)
are MATRIX-FORCED — `bunchedBimonoidDeltaFanMatrix` / `bunchedBimonoidMuFoldMatrix` make them functions of the
matrix alone.  The only freedom is the PERM stage: two perm-stage representatives of the same permutation matrix
differ by the Young double coset `S_{col-sums} x S_{row-sums}` — a Coxeter word-problem, NOT a transpose.

## The determinism is NOT free; it is the Coxeter word-problem, bounded

The minimal sufficient lemma is `CoxeterWordUnique`: two `sigma`-words of the same permutation matrix are
convertible over the hexagon rows, proved by induction on permutation length (bubble-sort to the canonical
riffle), each swap step a `yangBaxter` / `interchange` fire.  Its two decidable ends are shipped here, lifted to
the star scope:

  * **Width-2 base — the identity permutation has two words.**  `sigma_a ; sigma_a` and `id (a.a)` both realize
    the `2 x 2` identity matrix; they are convertible over the star scope by the `sigmaInvolution` sound row.  The
    length-2 Coxeter relation `s_1 s_1 = e`.
  * **Width-3 base — the reversal permutation has two words.**  `s_1 s_2 s_1` and `s_2 s_1 s_2` both realize the
    reversal matrix; they are convertible over the star scope by the `yangBaxter` hexagon row.  The braid relation
    (the length-3 Coxeter generator), the recon's cited base case of `CoxeterWordUnique`.

## The verdict (free / minimal / walled)

The retraction CAN be engineered to always emit the canonical riffle `wideSwap`, in which case gen / whisker / id
are FREE and the double coset is needed ONLY at vcomp reassembly (two canonical sub-middles compose to a
non-canonical product).  So: determinism is FREE at the elementary constructors, requires the MINIMAL lemma
`CoxeterWordUnique` at vcomp reassembly, and Node C (the general routing transpose) is NEVER built.  The general
double-coset lemma stays the r6 residual (`fxBunchedBimonoid_r6MiddleDeterminismDoubleCoset = false`, byte-intact).

Raw Lean 4 + Init; STRUCTURAL only; ASCII-only.  Per-declaration `#assert_no_axioms` gated in the audit twin. -/

namespace FX1Poly.Polygraph.Omega

/-! The width-3 permutation `rfl` matrix reductions exceed the default heartbeat budget; the raise is a compute
allowance only, the proof terms stay `Eq.refl`, axiom-free (uniform with the r4 `PermStage` / `Hexagon`). -/
set_option maxHeartbeats 4000000

/-! # =========================================================================================
    # B2 — THE TWO DECIDABLE ENDS OF THE COXETER WORD-PROBLEM (lifted to the star scope)
    # =========================================================================================
-/

/-- ★★ **THE WIDTH-2 DETERMINISM INSTANCE (the identity permutation's two words).**  `sigma_a ; sigma_a` and
`id (a.a)` — two distinct words both realizing the `2 x 2` identity permutation matrix — are convertible over the
STAR scope, by firing the `sigmaInvolution` sound row through the scope's `Or.inr (Or.inl ...)` selector.  The
length-2 Coxeter relation `s_1 s_1 = e`, the base of the perm-middle determinism at width 2. -/
theorem bunchedBimonoidInvolutionDeterminismOverStar :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      bunchedBimonoidSigmaInvolutionLeftLeg bunchedBimonoidSigmaInvolutionRightLeg :=
  SaturatedConvOverWithId.ofRelation (Or.inr (Or.inl BunchedBimonoidSoundRow.sigmaInvolution))

/-- ★ **The width-2 determinism legs share their matrix (both the `2 x 2` identity)** — `evalCell (sigma;sigma) =
evalCell (id (a.a))`, on the nose (`rfl`).  So the involution instance is genuinely two REPRESENTATIVES of the
SAME permutation matrix, converted syntactically above — the determinism content, not a triviality. -/
theorem bunchedBimonoidInvolutionDeterminismMatrixShared :
    bunchedBimonoidEvalCell bunchedBimonoidSigmaInvolutionLeftLeg
      = bunchedBimonoidEvalCell bunchedBimonoidSigmaInvolutionRightLeg := rfl

/-- ★★ **THE WIDTH-3 DETERMINISM INSTANCE (the reversal permutation's two words).**  `s_1 s_2 s_1` and
`s_2 s_1 s_2` (`bunchedBimonoidYangBaxter{Left,Right}Leg`) — two structurally-distinct Coxeter words both
realizing the reversal permutation matrix `[[0,0,1],[0,1,0],[1,0,0]]` — are convertible over the STAR scope, by
firing the `yangBaxter` hexagon row through the scope's `Or.inr (Or.inr ...)` selector.  The braid relation, the
recon's cited base case of `CoxeterWordUnique`. -/
theorem bunchedBimonoidYangBaxterDeterminismOverStar :
    SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
      bunchedBimonoidYangBaxterLeftLeg bunchedBimonoidYangBaxterRightLeg :=
  SaturatedConvOverWithId.ofRelation (Or.inr (Or.inr BunchedBimonoidHexagonRow.yangBaxter))

/-- ★ **The width-3 determinism legs share their matrix (both the reversal)** — `evalCell (s_1 s_2 s_1) =
evalCell (s_2 s_1 s_2)`, DERIVED from the star-scope convertibility (not assumed).  The two reversal words are
genuinely two representatives of the same permutation matrix. -/
theorem bunchedBimonoidYangBaxterDeterminismMatrixShared :
    bunchedBimonoidEvalCell bunchedBimonoidYangBaxterLeftLeg
      = bunchedBimonoidEvalCell bunchedBimonoidYangBaxterRightLeg :=
  bunchedBimonoidYangBaxterMatrixSharedOverHexagon

/-- ★★ **THE DECIDABLE-ENDS BUNDLE — the perm-middle determinism at width 2 and width 3.**  Both ends packaged: at
width 2 the identity permutation's two words converge (`involutionDeterminismOverStar`, matrix shared); at width 3
the reversal permutation's two words converge (`yangBaxterDeterminismOverStar`, matrix shared).  These are the two
concrete instances of "two perm-words of the same matrix are convertible" — the Coxeter word-problem's base
cases, both lifted to the star scope. -/
theorem bunchedBimonoidPermMiddleDeterminismDecidableEnds :
    (SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
        bunchedBimonoidSigmaInvolutionLeftLeg bunchedBimonoidSigmaInvolutionRightLeg
      ∧ bunchedBimonoidEvalCell bunchedBimonoidSigmaInvolutionLeftLeg
        = bunchedBimonoidEvalCell bunchedBimonoidSigmaInvolutionRightLeg)
    ∧ (SaturatedConvOverWithId bunchedBimonoidOmegaComputad bunchedBimonoidStarCongruenceScope
        bunchedBimonoidYangBaxterLeftLeg bunchedBimonoidYangBaxterRightLeg
      ∧ bunchedBimonoidEvalCell bunchedBimonoidYangBaxterLeftLeg
        = bunchedBimonoidEvalCell bunchedBimonoidYangBaxterRightLeg) :=
  ⟨⟨bunchedBimonoidInvolutionDeterminismOverStar, bunchedBimonoidInvolutionDeterminismMatrixShared⟩,
    ⟨bunchedBimonoidYangBaxterDeterminismOverStar, bunchedBimonoidYangBaxterDeterminismMatrixShared⟩⟩

/-! ## The B2 honesty markers -/

/-- ★★ **ESTABLISHED (B2) — the perm-middle determinism holds at its two decidable ends (over the star scope).**
`= true` records `bunchedBimonoidPermMiddleDeterminismDecidableEnds`: at width 2 the identity permutation's two
words (`sigma;sigma` vs `id`) converge via the `sigmaInvolution` sound row; at width 3 the reversal's two Coxeter
words (`s_1 s_2 s_1` vs `s_2 s_1 s_2`) converge via the `yangBaxter` hexagon row — both lifted to the star scope,
both with the shared matrix witnessed / derived.  The Coxeter word-problem's base cases, machine-checked. -/
def fxBunchedBimonoid_permMiddleDeterminismDecidableEnds : Bool := true

/-! # =========================================================================================
    # B2 — THE ADJUDICATION: free at the elementary constructors, minimal-lemma at vcomp, walled at Node C
    # =========================================================================================
-/

/-- ★ **ADJUDICATED — the delta-stage and mu-stage are MATRIX-FORCED (determinism is free there).**  `= true`
records the recon's Job-2 verdict on the non-perm stages: the delta-stage (`deltaFan` = column-sum fan) and the
mu-stage (`muFold` = row-sum fold) are FUNCTIONS OF THE MATRIX ALONE (`bunchedBimonoidDeltaFanMatrix` /
`bunchedBimonoidMuFoldMatrix` pin them to the all-ones column / row of the matrix's dimensions).  So the
determinism freedom is confined ENTIRELY to the perm middle — the fan / fold stages carry no double-coset
ambiguity. -/
def fxBunchedBimonoid_deltaMuStagesMatrixForced : Bool := true

/-- ★ **ADJUDICATED — determinism is FREE at gen / whisker / id (canonical-riffle emission).**  `= true` records
that IF the retraction is engineered to always emit the CANONICAL riffle `wideSwap` at each generator / whisker /
identity constructor, then those constructors carry no perm-word choice — the canonical form is emitted directly,
so determinism is free at the elementary constructors.  The double coset resurfaces ONLY where two canonical
sub-middles COMPOSE (the vcomp-reassembly node below). -/
def fxBunchedBimonoid_determinismFreeAtElementaryConstructors : Bool := true

/-- ★ **r6 RESIDUAL (2), the MINIMAL lemma — `CoxeterWordUnique` is NOT shipped (the vcomp-reassembly node).**
`= false` records the exact remaining node: `CoxeterWordUnique` — two `sigma`-words of the SAME permutation matrix
are convertible over the hexagon rows — proved by induction on permutation length (a STRUCTURAL bubble-sort fuel
`Nat`, NOT `WellFounded.fix`), each swap step a `yangBaxter` / `interchange` fire, the double-coset generators
(`S_{col-sums} x S_{row-sums}`) killed by the `commutativity` / `cocommutativity` rows.  The width-2 and width-3
BASE cases are shipped (`bunchedBimonoidPermMiddleDeterminismDecidableEnds`); the general induction on `ell(perm)`
is the genuine work.  This surfaces at vcomp reassembly (two canonical sub-middles compose to a non-canonical
product).  Cited byte-intact from `fxBunchedBimonoid_r6MiddleDeterminismDoubleCoset` (r5 StarRetractionCensus). -/
def fxBunchedBimonoid_coxeterWordUniqueMinimalLemmaUnbuilt : Bool := false

/-- ★ **ADJUDICATED — Node C (the general routing transpose) is NEVER built.**  `= false` records the recon's
Job-2 self-verdict: the general `spiderOf : Mat -> CellExpr` routing perm-stage read off a
row-major-to-column-sum TRANSPOSE (Node C) is NOT the residual and is deliberately NEVER built — the routing
lives in the perm-WORD, generated LOCALLY by the collision recursion (B1) and canonicalized by the minimal
`CoxeterWordUnique` lemma, so the determinism is a Coxeter word-problem, not a transpose.  Cited byte-intact from
`fxBunchedBimonoid_permStageGeneralRoutingTransposeWall` (r4 PermStage). -/
def fxBunchedBimonoid_nodeCTransposeNeverBuilt : Bool := false

/-- ★★ **ESTABLISHED (B2) — the WP-PROP r6 determinism adjudication (honest scoreboard).**  `= true` records the
complete r6 determinism verdict: the two decidable ends of the Coxeter word-problem lifted to the star scope
(`fxBunchedBimonoid_permMiddleDeterminismDecidableEnds` — width-2 involution + width-3 Yang-Baxter); the
adjudication that the delta / mu stages are matrix-forced (`...deltaMuStagesMatrixForced`) so determinism freedom
is confined to the perm middle; that determinism is FREE at gen / whisker / id under canonical-riffle emission
(`...determinismFreeAtElementaryConstructors`); the MINIMAL lemma `CoxeterWordUnique` walled at the
vcomp-reassembly node (`...coxeterWordUniqueMinimalLemmaUnbuilt = false`, byte-intact with the r5
`fxBunchedBimonoid_r6MiddleDeterminismDoubleCoset`); and Node C never built
(`...nodeCTransposeNeverBuilt = false`, byte-intact with the r4 transpose wall).  Determinism is NOT free, but
bounded to a Coxeter word-problem — the smaller of the two r6 residuals.  NO star marker flips. -/
def fxBunchedBimonoid_determinismRoundSixAdjudicationShipped : Bool := true

end FX1Poly.Polygraph.Omega
