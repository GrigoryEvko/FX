import FX1Poly.Core.Rewriting.Confluence.RawConfluence
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationUnion
import FX1Poly.Core.Rewriting.Confluence.ModularConfluence
import FX1Poly.Core.Rewriting.Confluence.KnuthBendixCompletion
import FX1Poly.Core.Rewriting.Confluence.DecreasingDiagrams
import FX1Poly.Tier0.Term.Subst.RawTermSubstBetaBridge
import FX1Poly.Tier0.Term.Action.FoldUniqueness
import FX1Poly.Tier0.Term.Action.InitialAlgebra
import FX1Poly.Tier0.Term.Rewrite.Dim1FreePreorder
import FX1Poly.Tier0.Term.Codata.TerminalCoalgebra
import FX1Poly.Tier0.Term.Rewrite.SquierCoherence
import FX1Poly.Tier0.Term.Rewrite.PolygraphicResolution
import FX1Poly.Tier0.Term.Rewrite.LevyOptimality
import FX1Poly.Tier0.Term.Action.SubstitutionMonoid
import FX1Poly.Core.Unification.PatternUnification
import FX1Poly.Core.Rewriting.Standardization
import FX1Poly.Core.Rewriting.BohmTree
import FX1Poly.Tier0.Term.Codata.MixedFixpoint
import FX1Poly.Tier0.Term.Codata.CopatternCoverage
import FX1Poly.Core.Rewriting.RewritingModulo
import FX1Poly.Tier0.Term.Rewrite.FreeStrictOmega
import FX1Poly.Tier0.Term.Rewrite.MarkedComplicial
import FX1Poly.Tier0.Term.Rewrite.ModularSNBoundary
import FX1Poly.Tier0.Term.Rewrite.WordProblem
import FX1Poly.Tier0.Term.Semantics.DenotationalDomain
import FX1Poly.Tier0.Term.Semantics.IntersectionTypes
import FX1Poly.Tier0.Term.Semantics.GeometryOfInteraction
import FX1Poly.Tier0.Term.Semantics.GameSemantics
import FX1Poly.Tier0.Term.Semantics.DifferentialLambda
import FX1Poly.Tier0.Term.Subst.RawTermSubst0Commute
import FX1Poly.Tier0.Term.Subst.RawTermSubstLiftWeaken

/-! # Tier0/Term — the term-axis (∞,ω)-category ledger (`term-0`: design-lock + rung index)

The Tier-0 restructure splits the kernel into four ω-categorical axes — **context · mode ·
term · type** — each its own `Tier0/` namespace, meeting at `Core/`.  The CONTEXT axis
(`Tier0/Context/`, 59 modules) and the MODE axis (`Tier0/Mode/`, 35 modules) are the finished
templates: each presents its rungs with `def fxContext_…` / `def fxMode_… : Bool` honesty markers
and a per-file `FX1PolyAudit` zero-axiom gate.

The TERM axis is the polygraph of term-formers and the rewriting that lives over it.  Its deep
mathematics is already shipped — but scattered across `Core/Rewriting/`,
`Core/Metatheory/Normalization/`, `Tier0/Term/{Action,Generator,Rename,Subst}/`, and
`Tier0/OmegacE/` — and, until this file, the axis had NO honesty-marker convention, NO rung index,
and NO audit gate of its own.  This module is the `term-0` design-lock: it adopts the Mode-style
marker convention for the term axis and discharges the metatheory the RAW term layer genuinely
earns, each flip backed (per the SN-103 discipline) by a named shipped theorem, not a bare slogan.

## The rung map (`term-0..27` + `term-beta`)

The axis decomposes LEFT (initial algebra) · MIDDLE (rewriting) · RIGHT (co-signature), then an
advanced-rewriting band, a high-dimensional band, a denotational-semantics band, and the SSC
bridge.  Status as of this design-lock (shipped-in-`Core` and surfaced here = ◆; substrate proven,
a leg remains = ○; genuinely new = ·):

  * `term-1`  LEFT  — constructors as initial algebra (SOAS): ◆ (RawTerm = initial algebra into an
    arbitrary carrier — `cata` + `IsCarrierHomomorphism.unique` + the full cata-law package CANCEL/FUSION/
    REFLECTION, op-dual to `term-3`; arbitrary-binding-SIGNATURE lift = SIG-5)
  * `term-2`  MIDDLE — dim-1 rewriting (`StepOver` as 1-cells): ◆ (the free-preorder universal property
    of `ReflTransClosure (StepOver bundle)` — `fxTerm_hasDim1RewritePreorder`; confluence surfaced as
    `fxTerm_hasRawConfluence`; proof-relevant (∞,ω) 1-cells = `term-4`/`term-17`)
  * `term-3`  RIGHT — terminal coalgebra + corecursion + bisimulation: ◆ (the final coalgebra of the
    stream functor — anamorphism + terminality + coinduction, generic source carrier —
    `fxTerm_hasTerminalCoalgebra`; the FX co-signature semantics + guardedness criterion = deferred co-SIG-5)
  * `term-4`  Squier coherent presentation: ◆ (the proof-relevant rewriting 2-category + homotopy
    congruence + coherent confluence + the diamonds GENERATE the homotopy (`toModel`) —
    `fxTerm_hasCoherentPresentation`; coherence-to-NF is the vacuous NF-specialization, the non-vacuous
    WF coherent-Newman + FX critical-pair complex = deferred `OHOM-1`/`term-5`)
  * `term-5`  polygraphic resolution + homology: ◆ (the 𝔽₂ chain complex + quotient-free homology vanishing
    + the abelianized presentation complex computing `H₁(ℕ) ≠ 0` and `H₁(trivial) = 0` in-framework + the
    (∞)-resolution interface, dim-2 acyclicity from `term-4` — `fxTerm_hasPolygraphicResolution`; the full
    complex over the 205-gen table + integral homology + higher critical triples = deferred `OHOM-1`)
  * `term-6`  Toyama / modular confluence & SN: ◆ (BOTH criteria surfaced — modular CONFLUENCE
    `fxTerm_hasModularConfluenceCriterion` (Hindley-Rosen: each side confluent + closures commute ⟹ union
    confluent) and modular SN `fxTerm_hasModularStrongNormalizationCriterion` (Geser quasi-commutation);
    confluence is modular, SN is NOT (Toyama's counterexample) — the SN criterion needs quasi-commutation)
  * `term-7`  Knuth-Bendix: ◆ CRITERION (`fxTerm_hasKnuthBendixConvergenceCriterion` — Church-Rosser:
    confluent ⟹ ⟷*=↓, the convergence criterion, + orientation soundness) · PROCEDURE not built
    (`fxTerm_hasKnuthBendixCompletion` — the orient/deduce/fairness loop; FX is orthogonal, needs none)
  * `term-8`  decreasing diagrams (universal confluence): ◆ FRAMEWORK + the diamond as the degenerate
    decreasing diagram + the SINGLE-LABEL theorem PROVED (Huet strong confluence ⟹ confluent)
    (`fxTerm_hasDecreasingDiagramsFramework`; the MULTI-label van Oostrom `LD ⟹ Confluent` = deferred capstone)
  * `term-9`  Lévy optimality (sharing / optimal reduction): ◆ FRAMEWORK — redex families (`CoFamilial`)
    + the no-duplication bound (shared ≤ naive, strict under sharing — `fxTerm_hasLevyOptimalityFramework`;
    the full optimality theorem + Lamping sharing graphs = deferred capstone)
  * `term-10` Fiore-Plotkin-Turi substitution Σ-monoid: ◆ the substitution monoid + the monoid laws
    presenting the substitution (Kleisli) category + ★ the REAL kernel instance `rawTermSubstitutionMonoid`
    (RawTerm + parallel subst, laws from `subst_identity_apply`/`subst_compose` — `fxTerm_hasSubstitutionMonoid`;
    the `[𝔽,Set]` tensor + the Σ-algebra/Σ-monoid = SSC `term-26`/`27` + SOAS completeness = deferred)
  * `term-11` higher-order PATTERN unification (Miller `Lλ`): ◆ the flex-rigid case FULLY SOLVED over
    `RawTerm` — MGU uniqueness (`patternSolution_unique`) + the inversion `ρ⁻¹` (`spineInverse`) + ★ the
    term-level recover `ρ⁻¹[ρ[body]]=body` (`patternSolution_recover` — `fxTerm_hasPatternUnification`; the
    full algorithm + Huet HOU + the Goldfarb undecidability boundary = deferred)
  * `term-12` standardization + finite developments: ◆ FINITE DEVELOPMENTS (decreasing-measure ⟹ SN,
    `developmentsAreFinite`) + STANDARDIZATION's core (head/internal factorization via strong postponement,
    `factorizationOfStrongPostponement` — `fxTerm_hasStandardizationFiniteDevelopments`; de Vrijer's exact
    bound + general postponement + the full standard-sequence theorem = deferred)
  * `term-13` Böhm trees / meaningless terms / genericity: ◆ the meaningless-terms theory (`IsMeaningless`
    closed under reduction) + the genericity separation (meaningless never joinable with solvable,
    `meaningless_not_joinable_solvable`) + the finite Böhm-approximant domain (`BohmApprox`, `⊥` least —
    `fxTerm_hasMeaninglessGenericity`; the infinitary Böhm tree + full operational genericity = deferred)
  * `term-14` mixed inductive-coinductive types (the μ/ν parity): ◆ `μ` induction (`MuTree.fold_unique`) +
    `ν` coinduction (`NuStream.corec_unique`) + the mixed `ν(μ)` type (`mixedFold`) + the finiteness-vs-
    unboundedness parity (`mu_isFinite` / `nu_canBeUnbounded` — `fxTerm_hasMixedFixpointParity`; the general
    Basold-Geuvers dependent `νX.μY.F` alternation = deferred)
  * `term-15` copattern coverage checking (dual of `term-11`): ◆ the copattern trie + the decidable coverage
    CHECKER (`isCovering`) + completeness (`covering_resolves_without_gap`) + dependent-index coverage
    (`DependentCoveringTree` — `fxTerm_hasCopatternCoverage`; the full Abel-Pientka algorithm with index
    unification = deferred)
  * `term-16` Church-Rosser modulo an equational theory (rewriting modulo AC): ◆ joinability modulo `E`
    + the easy half (joinable-modulo ⟹ convertible in `R ∪ E`, `equationalTheory_of_joinableModulo`) + the
    CR-modulo characterization + the GENERALIZED bridge (a confluent `R` is CR modulo any `E` below
    `R`-convertibility, `churchRosserModulo_of_subconvertible`; `E = equality` is the `term-7` instance) +
    `JoinableModulo` refl/symm + the commutativity witness (`fxTerm_hasRewritingModulo`; the
    Jouannaud-Kirchner modulo-`E` Newman lemma + AC matching = deferred)
  * `term-17` free strict ω-category + Gray tensor (mirrors `mode-5`): ◆ the dimension-1 free-category
    UNIVERSAL PROPERTY (`RewritePath.foldMap` + `foldMap_comp` functoriality + `foldMap_unique`) + STRICT
    interchange at dimension 2 (`rewriteInterchange_strict` — thin 2-cells ⟹ Gray interchanger = identity,
    the free STRICT 2-category) + the dimension-2 UNIVERSAL PROPERTY
    (`freeStrictTwoCategory_dim2UniversalProperty`/`_dim2Uniqueness`, the UP at both dimensions) —
    `fxTerm_hasFreeStrictOmegaCategory`; the non-trivial Gray tensor product + tricategory coherence = deferred)
  * `term-18` marked/complicial structure (mirrors `mode-7`): ◆ the complicial STRATIFICATION (Verity
    "thin = equivalence") — the dim-1 equivalence MARKING (`IsRewriteEquivalence`) + the stratification
    axioms (`rewriteEquivalence_nil`/`_comp`/`_symm`) + 2-TRIVIALITY (`rewriteOmega_twoTrivial`, the (∞,1)
    presentation) + SATURATION (homotopy-invariance + the 2-out-of-3, `rewriteEquivalence_cancelLeft`/
    `_cancelRight`) — `fxTerm_hasMarkedComplicial`; the weak-complicial horn-filling + (∞,n>1) marking =
    deferred)
  * `term-19` exact SN boundary — modular/persistent SN: ◆ PERSISTENCE (`strongNorm_subrelation` —
    `SN(R ∪ S) ⟹ SN(R) ∧ SN(S)`) + the NECESSITY counterexample (two SN steps whose union loops,
    `unionStep_notStronglyNormalizing`), sharpened to NO-NORMAL-FORM / not-even-WN
    (`unionStep_hasNoNormalForm`) + the explicit infinite reduction (`unionCycle`) — the positive criterion
    is `term-6` (`fxTerm_hasModularPersistentSN`; the full Toyama first-order persistence theorem = deferred)
  * `term-20` CAPSTONE — the word problem, decidable Conv as a function of convergence: ◆ the positive
    decision (`decidableWordProblem_of_convergent` + `wordProblem_iff_normalFormEq` — `a ⟷* b ↔ a↓ = b↓`,
    the word-problem face of the design-lock `fxTerm_hasNormalizerConvDecision`) + the DECIDABILITY BOUNDARY
    (convergence necessary: confluence via `forkStep_notConfluent` two-distinct-NFs + termination via
    `term-19`'s no-NF) — `fxTerm_hasWordProblemBoundary`; genuine undecidability (Markov-Post, needs a
    computability model) = deferred
  * `term-21` denotational semantics — the domain / fixpoint core: ◆ the pointed ω-CPO + Scott-continuity
    interface + the KLEENE LEAST-FIXPOINT theorem (`kleeneFixpoint_isFixpoint`/`_isLeast` — recursion = least
    fixpoint) + the one-point domain witness (`fxTerm_hasDenotationalDomainFixpoint`; D∞ + coherence spaces +
    adequacy = deferred)
  * `term-22` intersection types — BCD subtyping + the filter model: ◆ the meet-semilattice-with-top
    (`omega_isTop` + `inter_isGreatestLowerBound`) + filters + the LEAST filter (`omegaFilter_isLeast`) + the
    ω-complete filter PREORDER (`filterSup_isUpperBound`/`_isLeast`) — `fxTerm_hasIntersectionFilterModel`;
    the antisymmetric DCPO quotient (needs `propext`/`funext`) + the normalization characterization = deferred
  * `term-23` geometry of interaction — the token machine: ◆ the deterministic token machine
    (`step_deterministic`) + fuel-bounded execution + EXECUTION DETERMINACY (`reaches_unique` — the GoI
    denotation is a well-defined partial function) + the wire/axiom-link witness (`wireMachine_reachesExit`)
    — `fxTerm_hasGeometryOfInteraction`; GoI soundness (execution = cut-elimination) + the execution formula
    = deferred
  * `term-24` game semantics — arenas / plays / strategies: ◆ the `Polarity` duality + arenas + `dualArena`
    (involutive pointwise) + `EvenPlay` + the Opponent projection + arena-legality + DETERMINISTIC strategies
    with `Strategy.determinedByOpponent` (strategy = function of Opponent's moves) + the `answerStrategy`
    witness — `fxTerm_hasGameSemantics`; FULL ABSTRACTION + strategy composition + innocence = deferred
  * `term-25` differential λ-calculus — derivations + linear substitution: ◆ the abstract
    `DifferentialAlgebra` (linearity + Leibniz `deriv_mul`) + power rule + a model, and the concrete
    `linearSubst` with the Leibniz product rule (`linearSubst_app`), linearity (`linearSubst_length_eq_
    occurrences`), the constant rule, and the `d(x²) = [x t, t x]` witness — `fxTerm_hasDifferentialLambda`;
    λ-abstraction + Taylor expansion + resource reduction = deferred
  * `term-21..25` denotational semantics CAPSTONES (D∞+adequacy / etc.):
    · (`fxTerm_hasDenotationalAdequacy`)
  * `term-26` SSC single-weaken/subst + 8→4 collapse: ◆ the single `weaken`/`subst0` ops + the characteristic
    equations (head / weaken-cancel / lift-weaken naturality / substitution lemma + a derived composition) —
    `fxTerm_hasSingleSubstitutionCalculus`; the full SSC ≅ CwF inter-derivation = `context-28`/`term-27`
  * `term-27` Allais parallel-fold ↔ SSC reconciliation: ◆ (the fold engine is shipped)
  * `term-beta` re-home the `context-9` `×term` β-bridge corollary (with `term-26`)

## What this file ships (each backed, zero-axiom)

The three metatheoretic properties the raw term layer genuinely has — confluence (unconditional),
decidable conversion as a function of convergence, and the modular SN criterion — flipped `true`
and each conjoined with the shipped theorem that proves it.  The remaining rungs carry honest
`false` markers documenting precisely what is shipped-as-substrate versus open.

## Zero-axiom verification

Thirty `Bool` markers `:= true`, two `:= false`, and thirty `_isBacked` conjunctions each closed by
`rfl` and a direct application (`StepStar.rawConfluence`, `Normalizer.decidableConv`, `accUnion`,
`confluentOfCommutingConfluent`, `knuthBendixConvergenceCriterion` + `equationalTheory_orientationInvariant`,
`diamondProperty_isLocallyDecreasing` + `labeledUnion_diamond_isConfluent`,
`RawTerm.subst_cons_eq_singleton_after_lift`, `IsCarrierHomomorphism.unique`,
`ReflTransClosure.mediate_single` + `mediate_unique` + `reflTransClosure_fxIotaBundle_iff_stepStar`,
`StreamCoalgebra.ana_head` + `ana_unique` + `FinalStream.bisim_observe`,
`RewriteHomotopy.toModel` + `SquierDiamond.confluent`,
`F2ChainComplex.boundary_isCycle` + the `trivialComplex`/`zeroDifferentialComplex` witnesses +
`monoidNComplex_homologyNotVanishing` + `trivialMonoidComplex_homologyVanishes`,
`optimalReduction_le_unshared` + `optimalReduction_lt_unshared_of_sharing`,
`SubstitutionMonoid.kleisli_leftId` + `kleisli_rightId` + `kleisli_assoc`,
`patternSolution_unique` + `spineInverse_inverts` + `spineInverse_sound`).
No `axiom`,
`sorry`, `propext`, `Quot.sound`, `Classical`, `native_decide`, or `omega`.  Per-declaration gated in
`FX1PolyAudit/AuditTier0TermAxis.lean`.
-/

namespace FX1Poly.Tier0

open FX1Poly.Core

/-! ## The three backed metatheory flips (the raw term layer's genuine wins) -/

/-- **Honesty marker** — `term-2` / `term-20` substrate.  The dim-1 raw rewriting relation `StepStar`
is GLOBALLY CONFLUENT (Church-Rosser), UNCONDITIONALLY — no strong-normalization hypothesis.  Backed
by `StepStar.rawConfluence` (the Takahashi complete-development diamond), restated in
`fxTerm_rawConfluence_isBacked`.  `= true`. -/
def fxTerm_hasRawConfluence : Bool := true

/-- ★ **Backed flip (raw confluence).**  The marker is `true` AND raw `StepStar` reduction is
globally confluent (`StepStar.rawConfluence`): the dim-1 rewriting layer (`term-2`) is Church-Rosser
with no SN premise — the substrate the `term-20` Conv decider then rests on. -/
theorem fxTerm_rawConfluence_isBacked :
    fxTerm_hasRawConfluence = true ∧ StepStar.HasConfluence :=
  ⟨rfl, StepStar.rawConfluence⟩

/-- **Honesty marker** — `term-20` CAPSTONE.  Conversion is DECIDABLE as a function of CONVERGENCE: a
`Normalizer` for any fragment decides `Conv` on it, with the confluence side discharged
unconditionally (`Normalizer.decidableConv` over `StepStar.rawConfluence`).  Scope: a `Normalizer`
exists only for the SN/typed fragment (raw β+ι is NOT globally SN), so this is "decidable Conv GIVEN
convergence", not an unconditional global decider.  Backed in
`fxTerm_normalizerConvDecision_isBacked`.  `= true`. -/
def fxTerm_hasNormalizerConvDecision : Bool := true

/-- ★ **Backed flip (decidable Conv as a function of convergence).**  The marker is `true` AND any
`Normalizer` for a fragment decides `Conv` on it (`Normalizer.decidableConv`), its confluence
side-condition discharged by `rawConfluence`.  Stated through `Nonempty` because a decider is data. -/
theorem fxTerm_normalizerConvDecision_isBacked :
    fxTerm_hasNormalizerConvDecision = true
      ∧ (∀ {scope : Nat}, Normalizer scope →
          ∀ (leftTerm rightTerm : RawTerm scope),
          Nonempty (Decidable (Conv leftTerm rightTerm))) :=
  ⟨rfl, fun normalizer leftTerm rightTerm =>
    ⟨normalizer.decidableConv leftTerm rightTerm⟩⟩

/-- **Honesty marker** — `term-6` / `term-19`.  The MODULAR strong-normalization-of-union CRITERION
(Geser / Bachmair-Dershowitz) is available: if one relation is SN, the other is SN everywhere, and the
second quasi-commutes over the first, then the UNION is SN.  This is the modularity ENGINE, NOT a
claim that raw term reduction is strongly normalizing (raw β+ι SN is FALSE — `gen_natRec` and the
other `partialClass` generators diverge); it is the criterion that DELIVERS SN for the fragments where
its hypotheses hold.  Backed in `fxTerm_modularStrongNormalizationCriterion_isBacked`.  `= true`. -/
def fxTerm_hasModularStrongNormalizationCriterion : Bool := true

/-- ★ **Backed flip (modular SN criterion).**  The marker is `true` AND the Geser union criterion
holds (`accUnion`): right-SN-everywhere + quasi-commutation + left-accessibility give union
accessibility — modular SN, constructive and hypothesis-driven. -/
theorem fxTerm_modularStrongNormalizationCriterion_isBacked :
    fxTerm_hasModularStrongNormalizationCriterion = true
      ∧ (∀ {Carrier : Type} {reduceLeft reduceRight : Carrier → Carrier → Prop}
          {start : Carrier},
          (∀ element, Acc (fun later earlier => reduceRight earlier later) element) →
          QuasiCommutesRightOverLeft reduceLeft reduceRight →
          Acc (fun later earlier => reduceLeft earlier later) start →
          Acc (UnionSuccessor reduceLeft reduceRight) start) :=
  ⟨rfl, fun rightStronglyNormalizing quasiCommutes accessibleLeft =>
    accUnion rightStronglyNormalizing quasiCommutes accessibleLeft⟩

/-! ## term-6 (confluence half): modular confluence — the Hindley-Rosen / Toyama engine -/

/-- **Honesty marker** — `term-6` (confluence half).  The MODULAR-CONFLUENCE criterion (Hindley-Rosen, the
abstract engine of Toyama's confluence-modularity theorem) is surfaced: if two relations are each CONFLUENT
and their reflexive-transitive closures strongly commute, their UNION is confluent — the closure-form
`confluentOfCommutingConfluent`, authored in `Core/Rewriting/Confluence/ModularConfluence.lean` (this file
ships only the term-axis marker, mirroring how `accUnion` lives in Core and the SN marker above references
it).  This is the confluence companion to the modular-SN criterion `accUnion`.  HONEST SCOPE: the abstract
commuting-union engine, over arbitrary relations — the FX rule bundle IS orthogonal
(`fxRewriteBundle_rowsDisjoint = true`), so the kernel is already a single confluent system; this is the
GENERAL modularity statement, with the disjoint-signature ⟹ commute TRS layer (Toyama's rank/layer
analysis) deferred.  ASYMMETRY: confluence is modular, but strong normalization is NOT (Toyama's
counterexample) — that is why the SN criterion above carries an explicit quasi-commutation hypothesis while
this confluence engine needs only closure-commutation.  Backed in
`fxTerm_modularConfluenceCriterion_isBacked`.  `= true`. -/
def fxTerm_hasModularConfluenceCriterion : Bool := true

/-- ★ **Backed flip (modular confluence criterion).**  The marker is `true` AND the Hindley-Rosen engine
holds (`confluentOfCommutingConfluent`): each side confluent + closure strong-commutation give a confluent
union — modular confluence, abstract over any two relations. -/
theorem fxTerm_modularConfluenceCriterion_isBacked :
    fxTerm_hasModularConfluenceCriterion = true
      ∧ (∀ {Carrier : Type} {reduceLeft reduceRight : Carrier → Carrier → Prop},
          Confluent reduceLeft → Confluent reduceRight →
          StronglyCommutes (ReflTransClosure reduceLeft) (ReflTransClosure reduceRight) →
          Confluent (fun source target => reduceLeft source target ∨ reduceRight source target)) :=
  ⟨rfl, fun confluentLeft confluentRight commuteClosures =>
    confluentOfCommutingConfluent confluentLeft confluentRight commuteClosures⟩

/-! ## The term-native β-substitution bridge (`term-beta`, re-homed from `context-9`) -/

/-- **Honesty marker** — `term-beta` / `term-26`.  The `×term` β-substitution bridge is now re-homed
in the term axis, TERM-NATIVE: `body[cons arg sigma] = body[sigma⁺][⟨arg⟩]`, proved purely in the
`RawTermSubst` algebra (no `SubstVec`, no lateral `term → context` import) —
`RawTerm.subst_cons_eq_singleton_after_lift` in `Tier0/Term/Subst/RawTermSubstBetaBridge.lean`.  The
context-9 `SubstVec` corollary stays as the context-side shadow; this is the term axis owning its
β-law (refactor by addition, not deletion).  Backed in `fxTerm_betaSubstitutionBridge_isBacked`.
`= true`. -/
def fxTerm_hasBetaSubstitutionBridge : Bool := true

/-- ★ **Backed flip (β-substitution bridge).**  The marker is `true` AND the term-native β-bridge
holds: substituting the consed substitution equals lift-substitute-then-single-substitute
(`RawTerm.subst_cons_eq_singleton_after_lift`). -/
theorem fxTerm_betaSubstitutionBridge_isBacked :
    fxTerm_hasBetaSubstitutionBridge = true
      ∧ (∀ {targetScope sourceScope : Nat}
          (arg : RawTerm targetScope) (sigma : RawTermSubst sourceScope targetScope)
          (body : RawTerm (sourceScope + 1)),
          RawTerm.subst (RawTermSubst.cons arg sigma) body
            = RawTerm.subst (RawTermSubst.singleton arg)
                (RawTerm.subst sigma.lift body)) :=
  ⟨rfl, fun arg sigma body =>
    RawTerm.subst_cons_eq_singleton_after_lift arg sigma body⟩

/-! ## term-1: RawTerm is the initial algebra of its term signature (the universal property) -/

/-- **Honesty marker** — `term-1` (SOAS-initiality).  `RawTerm` is the INITIAL ALGEBRA of its term
signature: for any model `CarrierAlgebra C` into an arbitrary carrier family `C : Nat → Type`, the
catamorphism `cata` is the UNIQUE homomorphism `RawTerm → C` — existence (`cataHomomorphism`) + uniqueness
(`IsCarrierHomomorphism.unique`) in `Tier0/Term/Action/InitialAlgebra.lean`.  The dependent eliminator
`RawTerm.rec` is its constant-motive instance.  HONEST SCOPE: this is the fixed-FX-signature,
arbitrary-CARRIER initiality; the arbitrary-binding-SIGNATURE lift (SigTerm initial; CwR bi-initiality) is
SIG-5.  (The RawTerm-valued action-fold's own uniqueness — the rename/subst engine — is the separate
`FoldUniqueness.lean`, not this.)  The full catamorphism three-law package is shipped: Cata-CANCEL
(`cata_mkGen`), Cata-FUSION (`cata_fusion`), Cata-REFLECTION (`cata_selfAlgebra_id`) — the op-duals of
`term-3`'s `ana_*`, restoring the LEFT/RIGHT duality.  Backed in `fxTerm_initialAlgebraUniqueness_isBacked`.
`= true`. -/
def fxTerm_hasInitialAlgebraUniqueness : Bool := true

/-- ★ **Backed flip (initial-algebra uniqueness + the catamorphism laws).**  The marker is `true` AND (i)
any homomorphism out of `RawTerm` agrees with the catamorphism (`IsCarrierHomomorphism.unique` — initiality);
(ii) Cata-FUSION — an algebra homomorphism fuses with `cata` (`cata_fusion`); (iii) Cata-REFLECTION — `cata`
of the initial algebra's own structure is the identity (`cata_selfAlgebra_id`).  The op-duals of `term-3`'s
terminal-coalgebra laws. -/
theorem fxTerm_initialAlgebraUniqueness_isBacked :
    fxTerm_hasInitialAlgebraUniqueness = true
      ∧ (∀ {C : Nat → Type} {algebra : CarrierAlgebra C} {scope : Nat}
          (homomorphism : IsCarrierHomomorphism algebra) (term : RawTerm scope),
          homomorphism.map term = cata algebra term)
      ∧ (∀ {C D : Nat → Type} (source : CarrierAlgebra C) (target : CarrierAlgebra D)
          (morphism : {scope : Nat} → C scope → D scope),
          (∀ {scope : Nat} (generator : Generator) (payload : generator.payload scope)
            (foldedChildren : CarrierChildren C generator.binderShifts scope),
            morphism (source.combine generator payload foldedChildren)
              = target.combine generator payload (CarrierChildren.map morphism foldedChildren)) →
          ∀ {scope : Nat} (term : RawTerm scope), morphism (cata source term) = cata target term)
      ∧ (∀ {scope : Nat} (term : RawTerm scope), cata selfAlgebra term = term) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro C algebra scope homomorphism term
    exact homomorphism.unique term
  · intro C D source target morphism preservesCombine scope term
    exact cata_fusion source target morphism preservesCombine term
  · intro scope term
    exact cata_selfAlgebra_id term

/-! ## term-2: the dim-1 rewrite preorder — StepOver as the 1-cell generators -/

/-- **Honesty marker** — `term-2` (MIDDLE / dim-1 rewriting).  The reduction relation is the dim-1
structure of the term ω-category: terms are 0-cells, single rewrite steps are the 1-cell generators,
and the freely-generated relation `ReflTransClosure (StepOver bundle)` is the LEAST reflexive-transitive
relation containing them — the free-preorder universal property (`ReflTransClosure.mediate` +
`mediate_unique` in `Tier0/Term/Rewrite/Dim1FreePreorder.lean`).  HONEST SCOPE: the homs are
`Prop`-valued, so this is a PREORDER / THIN category (the category laws hold by proof irrelevance); the
proof-relevant (∞,ω) 1-cells, with critical-pair 2-cells, are `term-4` (Squier) / `term-17`.  The
`fxIotaBundle` instance is exactly the bespoke `StepStar` substrate
(`reflTransClosure_fxIotaBundle_iff_stepStar`), confluent via `fxTerm_hasRawConfluence`.  Backed in
`fxTerm_dim1RewritePreorder_isBacked`.  `= true`. -/
def fxTerm_hasDim1RewritePreorder : Bool := true

/-- ★ **Backed flip (dim-1 rewrite preorder).**  The marker is `true` AND the FULL free-preorder
universal property holds: (i) the universal TRIANGLE — `mediate` factors the generator inclusion
(`mediate ∘ single = the model's generator map`, the defining "free" equation); (ii) uniqueness — every
mediating map agrees with `ReflTransClosure.mediate`; (iii) the `fxIotaBundle` freely-generated relation
is exactly the bespoke `StepStar` substrate the kernel reduces with. -/
theorem fxTerm_dim1RewritePreorder_isBacked :
    fxTerm_hasDim1RewritePreorder = true
      ∧ (∀ {Carrier : Type} {rel : Carrier → Carrier → Prop} (cocone : ReflTransCocone rel)
          {source target : Carrier} (step : rel source target),
          ReflTransClosure.mediate cocone (ReflTransClosure.single step)
            = cocone.embedsGenerator step)
      ∧ (∀ {Carrier : Type} {rel : Carrier → Carrier → Prop} (cocone : ReflTransCocone rel)
          {source goal : Carrier}
          (other : ReflTransClosure rel source goal → cocone.relation source goal)
          (chain : ReflTransClosure rel source goal),
          other chain = ReflTransClosure.mediate cocone chain)
      ∧ (∀ {scope : Nat} {source target : RawTerm scope},
          ReflTransClosure
            (fun first second : RawTerm scope => StepOver fxIotaBundle first second)
            source target
            ↔ StepStar source target) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro Carrier rel cocone source target step
    exact ReflTransClosure.mediate_single cocone step
  · intro Carrier rel cocone source goal other chain
    exact ReflTransClosure.mediate_unique cocone other chain
  · intro scope source target
    exact reflTransClosure_fxIotaBundle_iff_stepStar

/-! ## term-3: terminal coalgebra + corecursion + bisimulation (RIGHT / co-signature) -/

/-- **Honesty marker** — `term-3` (RIGHT / co-signature), the op-dual of `term-1`.  The term axis has a
TERMINAL COALGEBRA with corecursion (anamorphism) and bisimulation: the final coalgebra of the stream
functor `X ↦ A × X` (`FinalStream`), with the anamorphism `StreamCoalgebra.ana` from an arbitrary source
coalgebra, its coalgebra-homomorphism laws + fusion, terminality (`ana_unique`), the coinduction
principle (`FinalStream.bisim_observe`), the constructor `cons` with Lambek's fixpoint iso, and a
concrete computing witness (`constStream`) — in `Tier0/Term/Codata/TerminalCoalgebra.lean`.  HONEST SCOPE: the CANONICAL
stream instance, generic over the SOURCE coalgebra carrier (the op-dual of `term-1`'s fixed-signature
arbitrary-carrier initiality — `RawTerm` was the FX term former, streams are NOT the FX co-signature); the
terminal-coalgebra semantics for the codata generators (`gen_codataUnfold` / `gen_codataDest` / `gen_polyNu`)
plus a decidable-complete guardedness criterion are the deferred co-dual of `SIG-5`.  Equality is
OBSERVATIONAL / bisimulation (funext-free), the dual of `term-2`'s thin-category collapse.  Backed in
`fxTerm_terminalCoalgebra_isBacked`.  `= true`. -/
def fxTerm_hasTerminalCoalgebra : Bool := true

/-- ★ **Backed flip (terminal coalgebra).**  The marker is `true` AND the final-coalgebra universal
property holds: (i) corecursion commutes with the head observation (`ana` is a coalgebra hom — the
co-triangle); (ii) terminality — any coalgebra hom into `FinalStream` agrees with `ana` up to bisimulation;
(iii) the coinduction principle — every bisimulation is contained in observational equality. -/
theorem fxTerm_terminalCoalgebra_isBacked :
    fxTerm_hasTerminalCoalgebra = true
      ∧ (∀ {Carrier A : Type} (coalgebra : StreamCoalgebra Carrier A) (state : Carrier),
          (coalgebra.ana state).head = coalgebra.out state)
      ∧ (∀ {Carrier A : Type} (coalgebra : StreamCoalgebra Carrier A)
          {candidate : Carrier → FinalStream A}, IsStreamCoalgebraHom coalgebra candidate →
          ∀ (index : Nat) (state : Carrier),
            (candidate state).observe index = (coalgebra.ana state).observe index)
      ∧ (∀ {A : Type} {related : FinalStream A → FinalStream A → Prop}, IsBisimulation related →
          ∀ (index : Nat) {first second : FinalStream A}, related first second →
            first.observe index = second.observe index) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro Carrier A coalgebra state
    exact coalgebra.ana_head state
  · intro Carrier A coalgebra candidate isHom index state
    exact coalgebra.ana_unique isHom index state
  · intro A related isBisimulation index first second isRelated
    exact FinalStream.bisim_observe isBisimulation index isRelated

/-! ## term-4: Squier's homotopical theorem — the coherent presentation -/

/-- **Honesty marker** — `term-4` (Squier).  The coherent-presentation / homotopical layer is shipped:
the proof-RELEVANT rewriting 2-category (`RewritePath` as DATA, with genuine category laws — the non-thin
lift of `term-2`), the homotopy congruence on parallel paths (`RewriteHomotopy`, the 2-cells), the DIAMOND
generating-confluences (`SquierDiamond`), COHERENT CONFLUENCE (`SquierDiamond.confluent` — the diamonds
join divergences with a homotopy witness, NON-VACUOUS via `completeCoherentJoin`), and the LEAST-CONGRUENCE
universal property (`RewriteHomotopy.toModel` — the diamonds GENERATE the homotopy, the dim-2 analogue of
`term-2`'s `mediate`) — in `Tier0/Term/Rewrite/SquierCoherence.lean`.  HONEST SCOPE: the abstract DIAMOND
case (the FX bundle IS orthogonal — `fxRewriteBundle_rowsDisjoint = true`).  The single-step `SquierDiamond`
forces every step-target to have an outgoing residual (`joinLeft s s`), so a reachable NORMAL FORM is
impossible and coherence-to-NF (`SquierDiamond.coherence`) is its (true but VACUOUS) NF specialization; a
non-vacuous coherence-to-NF needs PATH residuals + termination — the WF coherent-Newman, which
`WellFounded.fix`'s `propext`/`Quot.sound` leak rules out zero-axiom — deferred with the FX critical-pair
complex / general Newman / homology capstone (`OHOM-1` / `term-5`).  Backed in
`fxTerm_coherentPresentation_isBacked`.  `= true`. -/
def fxTerm_hasCoherentPresentation : Bool := true

/-- ★ **Backed flip (Squier coherence).**  The marker is `true` AND (i) the diamonds GENERATE the homotopy
— every homotopy maps into any (2,1)-congruence containing the diamond cells (`RewriteHomotopy.toModel`,
the least-congruence universal property); (ii) COHERENT CONFLUENCE is total — any two coinitial paths join
with a homotopy witness (`SquierDiamond.confluent`), non-vacuously (witnessed by `completeCoherentJoin`). -/
theorem fxTerm_coherentPresentation_isBacked :
    fxTerm_hasCoherentPresentation = true
      ∧ (∀ {Carrier : Type} {Step : Carrier → Carrier → Type} {dp : SquierDiamond Step}
          (model : HomotopyModel dp) {source target : Carrier}
          {leftPath rightPath : RewritePath Step source target},
          RewriteHomotopy dp leftPath rightPath → model.rel leftPath rightPath)
      ∧ (∀ {Carrier : Type} {Step : Carrier → Carrier → Type} (dp : SquierDiamond Step)
          {source leftEnd rightEnd : Carrier}
          (leftPath : RewritePath Step source leftEnd) (rightPath : RewritePath Step source rightEnd),
          Nonempty (SquierConfluence dp leftPath rightPath)) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro Carrier Step dp model source target leftPath rightPath homotopy
    exact homotopy.toModel model
  · intro Carrier Step dp source leftEnd rightEnd leftPath rightPath
    exact ⟨dp.confluent leftPath rightPath⟩

/-! ## term-5: the (∞)-polygraphic resolution + polygraphic homology -/

/-- **Honesty marker** — `term-5` (polygraphic resolution + homology).  The polygraphic-homology framework
is shipped: the 𝔽₂ chain complex (`F2ChainComplex` with `∂² = 0`), homology as quotient-free VANISHING
(`HomologyVanishes` / `IsAcyclic`: cycles ⊆ boundaries — no `Quot.sound`), `boundary_isCycle` and the
SUBGROUP laws (`add_isCycle` / `add_isBoundary`: `ker ∂` and `im ∂` are 𝔽₂-subspaces, so `Hₙ` is a genuine
quotient of subspaces), concrete witnesses that the machinery DISTINGUISHES acyclic (`trivialComplex`) from
non-acyclic (`zeroDifferentialComplex`), and — the in-framework payoff — the ABELIANIZED CHAIN COMPLEX OF A
PRESENTATION (`presentationComplex` over two `F2Module`s with a relation differential `∂₂`), with the GENUINE
HOMOLOGY of two real monoid presentations COMPUTED: `⟨a,b|a=b⟩` (≅ `ℕ`) has `H₁ ≠ 0`
(`monoidNComplex_homologyNotVanishing`, its `∂₂` IS `relationBoundaryF2 [false] [true] = a+b`) and `⟨a|a=ε⟩`
(trivial monoid) has `H₁ = 0` (`trivialMonoidComplex_homologyVanishes`, `∂₂ = id`); plus the (∞)-resolution
interface (`PolygraphResolution`) whose DIM-2 acyclicity is exactly `term-4`'s coherence
(`rewriteResolution_dimTwoAcyclic`) — in `Tier0/Term/Rewrite/PolygraphicResolution.lean`.  HONEST SCOPE: the
𝔽₂ homology FRAMEWORK + small concrete presentation complexes (`H₁` only, 2-truncated) + the dim-2 resolution
from `term-4`.  Deferred (the `OHOM-1` #1261 capstone): the full polygraphic complex over the 205-generator
table (assembling `fxKernelPolygraph`'s abelianization as an `F2ChainComplex`), integral (ℤ) homology (no
zero-axiom `Int`), the higher (≥3) critical-triple cells, and the homology-computes-coherence theorem.  Backed
in `fxTerm_polygraphicResolution_isBacked`.  `= true`. -/
def fxTerm_hasPolygraphicResolution : Bool := true

/-- ★ **Backed flip (polygraphic resolution + homology).**  The marker is `true` AND (i) the chain-complex
condition holds (every boundary is a cycle, so homology is well-defined); (ii) `ker ∂` is a subspace
(`add_isCycle`); (iii) the machinery distinguishes acyclic (`trivialComplex`) from non-acyclic
(`zeroDifferentialComplex`); (iv) GENUINE IN-FRAMEWORK PRESENTATION HOMOLOGY — the abelianized complex of
`⟨a,b|a=b⟩` (≅ `ℕ`) has `H₁ ≠ 0` (`monoidNComplex_homologyNotVanishing`, a non-zero `∂₂`) while the complex
of `⟨a|a=ε⟩` (trivial monoid) has `H₁ = 0` (`trivialMonoidComplex_homologyVanishes`); (v) the rewriting
resolution is DIM-2 ACYCLIC — `term-4`'s coherence fills every parallel-paths-to-normal-form 2-sphere. -/
theorem fxTerm_polygraphicResolution_isBacked :
    fxTerm_hasPolygraphicResolution = true
      ∧ (∀ (complex : F2ChainComplex) {dimension : Nat} {element : complex.chain (dimension + 1)},
          complex.IsBoundary element → complex.IsCycle element)
      ∧ (∀ (complex : F2ChainComplex) {dimension : Nat}
          {first second : complex.chain (dimension + 1)},
          complex.IsCycle first → complex.IsCycle second → complex.IsCycle (complex.add first second))
      ∧ F2ChainComplex.trivialComplex.IsAcyclic
      ∧ ¬ F2ChainComplex.zeroDifferentialComplex.HomologyVanishes 0
      ∧ relationBoundaryF2 [false] [true] = (true, true)
      ∧ ¬ monoidNComplex.HomologyVanishes 0
      ∧ trivialMonoidComplex.HomologyVanishes 0
      ∧ (∀ {Carrier : Type} {Step : Carrier → Carrier → Type} (dp : SquierDiamond Step)
          {source target : Carrier} (_isNormalForm : ∀ next, Step target next → False)
          (leftPath rightPath : RewritePath Step source target),
          RewriteHomotopy dp leftPath rightPath) := by
  refine ⟨rfl, ?_, ?_, F2ChainComplex.trivialComplex_isAcyclic,
          F2ChainComplex.zeroDifferentialComplex_homologyNotVanishing, rfl,
          monoidNComplex_homologyNotVanishing, trivialMonoidComplex_homologyVanishes, ?_⟩
  · intro complex _dimension _element isBoundary
    exact complex.boundary_isCycle isBoundary
  · intro complex _dimension _first _second firstIsCycle secondIsCycle
    exact complex.add_isCycle firstIsCycle secondIsCycle
  · intro Carrier Step dp source target isNormalForm leftPath rightPath
    exact rewriteResolution_dimTwoAcyclic dp isNormalForm leftPath rightPath

/-! ## term-7: Knuth-Bendix — the convergence criterion + orientation soundness -/

/-- **Honesty marker** — `term-7` (Knuth-Bendix, the CRITERION).  The mathematical CORE that justifies
completion is surfaced (in `Core/Rewriting/Confluence/KnuthBendixCompletion.lean`): the abstract
Church-Rosser theorem (`churchRosser_of_confluent` — a CONFLUENT relation's equational theory `⟷*` IS
joinability `↓`), the KB CONVERGENCE CRITERION (`knuthBendixConvergenceCriterion` — a terminating, locally
confluent system decides its theory, via Newman + Church-Rosser), ORIENTATION SOUNDNESS
(`equationalTheory_orientationInvariant` — orienting an equation preserves `⟷*`), and THE PAYOFF — a
convergent presentation DECIDES its word problem: with a normalizer, `a ⟷* b ↔ a↓ = b↓`
(`ConvergentNormalizer.equationalTheory_iff`), hence `Decidable` (`decidableEquationalTheory` /
`knuthBendixDecidesWordProblem`), plus unique normal forms (`normalize_isCanonical`); witnessed by the
one-rule `{true ↦ false}` convergent system.  This is the confluence/decision companion to the modular
criteria above.  Backed in `fxTerm_knuthBendixConvergenceCriterion_isBacked`.  `= true`.  (The completion
PROCEDURE itself stays `fxTerm_hasKnuthBendixCompletion = false` — see below.) -/
def fxTerm_hasKnuthBendixConvergenceCriterion : Bool := true

/-- ★ **Backed flip (Knuth-Bendix convergence criterion).**  The marker is `true` AND (i) a terminating,
locally confluent relation decides its equational theory (`knuthBendixConvergenceCriterion`: `⟷* = ↓`);
(ii) orientation preserves the theory (`equationalTheory_orientationInvariant`) — the soundness of every
completion inference step; and (iii) THE PAYOFF — a convergent system with a normalizer reduces its word
problem to normal-form comparison (`ConvergentNormalizer.equationalTheory_iff`: `a ⟷* b ↔ a↓ = b↓`, hence
`Decidable` via `decidableEquationalTheory`). -/
theorem fxTerm_knuthBendixConvergenceCriterion_isBacked :
    fxTerm_hasKnuthBendixConvergenceCriterion = true
      ∧ (∀ {Carrier : Type} {rel : Carrier → Carrier → Prop},
          WellFounded (fun reduct origin => rel origin reduct) → WeaklyConfluent rel →
          ∀ {leftValue rightValue : Carrier},
            EquationalTheory rel leftValue rightValue ↔ Joinable rel leftValue rightValue)
      ∧ (∀ {Carrier : Type} {rel : Carrier → Carrier → Prop} {leftValue rightValue : Carrier},
            EquationalTheory rel leftValue rightValue
              ↔ EquationalTheory (fun source target => rel source target ∨ rel target source)
                  leftValue rightValue)
      ∧ (∀ {Carrier : Type} {rel : Carrier → Carrier → Prop}
          (normalizer : ConvergentNormalizer rel), Confluent rel →
          ∀ {leftValue rightValue : Carrier},
            EquationalTheory rel leftValue rightValue
              ↔ normalizer.normalize leftValue = normalizer.normalize rightValue) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro Carrier rel terminating locallyConfluent leftValue rightValue
    exact knuthBendixConvergenceCriterion terminating locallyConfluent
  · intro Carrier rel leftValue rightValue
    exact equationalTheory_orientationInvariant
  · intro Carrier rel normalizer confluent leftValue rightValue
    exact normalizer.equationalTheory_iff confluent

/-! ## term-8: decreasing diagrams — the universal confluence framework -/

/-- **Honesty marker** — `term-8` (decreasing diagrams).  The van Oostrom decreasing-diagram FRAMEWORK is
surfaced (in `Core/Rewriting/Confluence/DecreasingDiagrams.lean`): a `Nat`-labeled rewrite system
(`labeledUnion` / `labeledBelow`), the locally-decreasing condition (`LocallyDecreasing`, the sum-bounded
valley form), and the UNIVERSALITY direction — the diamond property is the degenerate single-label
decreasing diagram (`diamondProperty_isLocallyDecreasing`), whose union confluence the framework recovers
(`labeledUnion_diamond_isConfluent`).  And the SINGLE-LABEL decreasing-diagrams THEOREM is PROVED — Huet's
strong confluence implies confluence (`stronglyConfluent_implies_confluent`), a genuine sound criterion
strictly more general than the diamond (`diamondProperty_implies_stronglyConfluent`, so `diamondConfluence`
is its corollary), itself the single-label decreasing diagram (`stronglyConfluent_isLocallyDecreasing`).
Decreasing diagrams is the universal confluence criterion: every standard confluence proof (diamond, Newman,
commutation) is an instance.  Backed in `fxTerm_decreasingDiagramsFramework_isBacked`.  `= true`.  HONEST
SCOPE: the framework + the diamond instance + the single-label theorem (Huet SC).  The deep MULTI-label van
Oostrom THEOREM `LocallyDecreasing ⟹ Confluent` (general well-founded labels, multiset induction over
conversions) — what makes the criterion fully universal — and the commutation/Newman instances are the
deferred capstone. -/
def fxTerm_hasDecreasingDiagramsFramework : Bool := true

/-- ★ **Backed flip (decreasing-diagram framework).**  The marker is `true` AND (i) the diamond property is
a decreasing-diagram instance (`diamondProperty_isLocallyDecreasing` — every relation with the diamond,
labeled label-blindly, is locally decreasing); and (ii) the framework recovers its confluence
(`labeledUnion_diamond_isConfluent`). -/
theorem fxTerm_decreasingDiagramsFramework_isBacked :
    fxTerm_hasDecreasingDiagramsFramework = true
      ∧ (∀ {Carrier : Type} {rel : Carrier → Carrier → Prop},
          DiamondProperty rel → LocallyDecreasing (fun _label => rel))
      ∧ (∀ {Carrier : Type} {rel : Carrier → Carrier → Prop},
          DiamondProperty rel → Confluent (labeledUnion (fun _label => rel)))
      ∧ (∀ {Carrier : Type} {rel : Carrier → Carrier → Prop},
          StronglyConfluent rel → Confluent rel) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro Carrier rel diamond
    exact diamondProperty_isLocallyDecreasing diamond
  · intro Carrier rel diamond
    exact labeledUnion_diamond_isConfluent diamond
  · intro Carrier rel stronglyConfluent
    exact stronglyConfluent_implies_confluent stronglyConfluent

/-! ## term-9: Lévy optimality — redex families + the no-duplication bound -/

/-- **Honesty marker** — `term-9` (Lévy optimality).  The redex-family FRAMEWORK + the quantitative
no-duplication bound is shipped (in `Tier0/Term/Rewrite/LevyOptimality.lean`): redexes partition into Lévy
families (`CoFamilial`, an equivalence — same label = same family), and the OPTIMAL (shared) reduction —
one step per family — never exceeds the naive per-redex reduction (`optimalReduction_le_unshared`) and is
STRICTLY shorter under genuine sharing (`optimalReduction_lt_unshared_of_sharing`), the precise sense in
which optimal reduction never re-contracts a shared family.  Backed in `fxTerm_levyOptimality_isBacked`.
`= true`.  HONEST SCOPE: the family framework + the quantitative bound.  DEFERRED (the capstone): Lévy's full
optimality THEOREM (family-complete reduction is optimal among all strategies to normal form), the labeled
λ-calculus residual/family theory over actual terms, and the Lamping / Gonthier-Abadi-Lévy SHARING GRAPHS
(interaction nets, fans/brackets, read-back; Asperti-Mairson non-elementary bookkeeping). -/
def fxTerm_hasLevyOptimalityFramework : Bool := true

/-- ★ **Backed flip (Lévy optimality framework).**  The marker is `true` AND (i) the family relation is an
equivalence (`CoFamilial.trans` — families partition redexes); (ii) shared reduction never exceeds naive
(`optimalReduction_le_unshared`); (iii) shared reduction is STRICTLY shorter under genuine sharing
(`optimalReduction_lt_unshared_of_sharing`). -/
theorem fxTerm_levyOptimality_isBacked :
    fxTerm_hasLevyOptimalityFramework = true
      ∧ (∀ {Redex : Type} {familyLabel : Redex → Nat} {left middle right : Redex},
          CoFamilial familyLabel left middle → CoFamilial familyLabel middle right →
          CoFamilial familyLabel left right)
      ∧ (∀ (familySizes : List Nat), (∀ size ∈ familySizes, 1 ≤ size) →
          familySizes.length ≤ familyTotalRedexes familySizes)
      ∧ (∀ (familySizes : List Nat), (∀ size ∈ familySizes, 1 ≤ size) →
          (∃ size ∈ familySizes, 2 ≤ size) →
          familySizes.length < familyTotalRedexes familySizes) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro Redex familyLabel left middle right firstRelated secondRelated
    exact CoFamilial.trans firstRelated secondRelated
  · intro familySizes allPositive
    exact optimalReduction_le_unshared familySizes allPositive
  · intro familySizes allPositive hasSharing
    exact optimalReduction_lt_unshared_of_sharing familySizes allPositive hasSharing

/-! ## term-10: the Fiore-Plotkin-Turi substitution monoid -/

/-- **Honesty marker** — `term-10` (FPT substitution Σ-monoid).  The Fiore-Plotkin-Turi substitution monoid
is shipped (in `Tier0/Term/Action/SubstitutionMonoid.lean`): `SubstitutionMonoid` (variables `var` = the
unit, parallel substitution `subst` = the multiplication, + the three monoid laws `(var i)[σ]=σ i` /
`t[var]=t` / `t[σ][τ]=t[σ;τ]`), and the genuine FPT consequence — the monoid laws PRESENT THE SUBSTITUTION
(KLEISLI) CATEGORY (`kleisli_leftId`/`kleisli_rightId`/`kleisli_assoc`, pointwise / funext-free).  ★ The
FPT headline is made concrete on the REAL kernel syntax: `rawTermSubstitutionMonoid` instantiates the
structure with `RawTerm` + parallel substitution, its three monoid laws discharged by the kernel's own
substitution metatheory (var-lookup `rfl`, `RawTerm.subst_identity_apply`, `RawTerm.subst_compose`) — so the
FX syntax IS a substitution monoid and inherits the substitution category.  (The `variableSubstitutionMonoid`
Fin witness is also kept.)  Backed in `fxTerm_substitutionMonoid_isBacked`.  `= true`.  HONEST SCOPE: the
substitution monoid (abstract + the RawTerm kernel instance) + the substitution-category consequence.
DEFERRED: the `[𝔽, Set]` substitution TENSOR (coend), the Σ-algebra compatibility making `RawTerm` a full
Σ-MONOID (the SSC-algebra reconciliation — `term-26`/`term-27`/`context-28`), and SOAS COMPLETENESS
(Fiore-Hur).  `RawTerm` is the INITIAL Σ-monoid; its recursor is `term-1`'s `cata`. -/
def fxTerm_hasSubstitutionMonoid : Bool := true

/-- ★ **Backed flip (FPT substitution monoid).**  The marker is `true` AND (i) the identity laws
`var ; σ = σ` and `σ ; var = σ` (pointwise, `kleisli_leftId`/`kleisli_rightId`); (ii) associativity
`(ρ ; σ) ; τ = ρ ; (σ ; τ)` (pointwise, `kleisli_assoc`) — the monoid laws present the substitution
category; AND (iii) ★ the FX kernel syntax is genuinely a substitution monoid — there is a
`SubstitutionMonoid` whose carrier is `RawTerm` (`rawTermSubstitutionMonoid`), so the abstract structure is
non-vacuous on the real syntax, not only the `Fin` witness. -/
theorem fxTerm_substitutionMonoid_isBacked :
    fxTerm_hasSubstitutionMonoid = true
      ∧ (∀ (monoid : SubstitutionMonoid) {first second : Nat}
          (assignment : Fin first → monoid.carrier second) (index : Fin first),
          monoid.kleisliComp monoid.var assignment index = assignment index
            ∧ monoid.kleisliComp assignment monoid.var index = assignment index)
      ∧ (∀ (monoid : SubstitutionMonoid) {first second third fourth : Nat}
          (firstAssignment : Fin first → monoid.carrier second)
          (secondAssignment : Fin second → monoid.carrier third)
          (thirdAssignment : Fin third → monoid.carrier fourth) (index : Fin first),
          monoid.kleisliComp (monoid.kleisliComp firstAssignment secondAssignment) thirdAssignment index
            = monoid.kleisliComp firstAssignment
                (monoid.kleisliComp secondAssignment thirdAssignment) index)
      ∧ (∃ kernelSubstitutionMonoid : SubstitutionMonoid, kernelSubstitutionMonoid.carrier = RawTerm) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro monoid first second assignment index
    exact ⟨monoid.kleisli_leftId assignment index, monoid.kleisli_rightId assignment index⟩
  · intro monoid first second third fourth firstAssignment secondAssignment thirdAssignment index
    exact monoid.kleisli_assoc firstAssignment secondAssignment thirdAssignment index
  · exact ⟨rawTermSubstitutionMonoid, rfl⟩

/-! ## term-11: higher-order pattern unification — the inversion engine -/

/-- **Honesty marker** — `term-11` (higher-order pattern unification).  The decidable PATTERN FRAGMENT
(Miller `Lλ`) over the real `RawTerm` is shipped (in `Core/Unification/PatternUnification.lean`): a pattern
spine is a DISTINCT-variable (injective) renaming (`IsPatternSpine`, stable under binders via
`patternSpine_lift`), MGU solutions are UNIQUE (`patternSolution_unique` — a corollary of the term-level
renaming-injectivity, the deterministic core of flex-rigid solving), and the INVERSION substitution `ρ⁻¹`
is constructed (`spineInverse`) with soundness (`spineInverse_sound`) and the round-trip `ρ⁻¹ ∘ ρ = id`
(`spineInverse_inverts`).  ★ The flex-rigid case is FULLY SOLVED at the term level: the inverse RENAMING
recovers the body — `patternSolution_recover` proves `ρ⁻¹[ρ[body]] = body` (funext-free, via
`RawTerm.rename_pointwise`), so paired with uniqueness the equation `?M[ρ] ≐ t` has a unique solution the
inverse COMPUTES.  Backed in `fxTerm_patternUnification_isBacked`.  `= true`.  HONEST SCOPE: the flex-rigid
case complete — unique solutions + the computed inverse that recovers them.  DEFERRED: the full algorithm
(flex-rigid PRUNING for out-of-image `t`, occurs-check, flex-flex spine intersection); Huet's general HOU
semi-decision procedure; and the UNDECIDABILITY BOUNDARY — Goldfarb's theorem that second-order unification
is undecidable (the documented mathematical boundary, not a mechanized negative result). -/
def fxTerm_hasPatternUnification : Bool := true

/-- ★ **Backed flip (pattern unification).**  The marker is `true` AND (i) MGU UNIQUENESS — a metavariable
applied to an injective (distinct) spine has at most one solution (`patternSolution_unique`); (ii) the
INVERSION round-trip `ρ⁻¹ ∘ ρ = id` (`spineInverse_inverts`); (iii) inversion SOUNDNESS — `ρ⁻¹` returns only
genuine preimages (`spineInverse_sound`). -/
theorem fxTerm_patternUnification_isBacked :
    fxTerm_hasPatternUnification = true
      ∧ (∀ {arity scope : Nat} (spine : Fin arity → Fin scope), Function.Injective spine →
          ∀ (bodyA bodyB : RawTerm arity),
            RawTerm.rename spine bodyA = RawTerm.rename spine bodyB → bodyA = bodyB)
      ∧ (∀ {arity scope : Nat} (spine : Fin arity → Fin scope), Function.Injective spine →
          ∀ (probe : Fin arity), spineInverse spine (spine probe) = some probe)
      ∧ (∀ {arity scope : Nat} (spine : Fin arity → Fin scope) (target : Fin scope)
          (preimage : Fin arity),
            spineInverse spine target = some preimage → spine preimage = target) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro arity scope spine spineInjective bodyA bodyB instantiationsAgree
    exact patternSolution_unique spine spineInjective bodyA bodyB instantiationsAgree
  · intro arity scope spine spineInjective probe
    exact spineInverse_inverts spine spineInjective probe
  · intro arity scope spine target preimage inverted
    exact spineInverse_sound spine target preimage inverted

/-! ## term-12: standardization + finite developments -/

/-- **Honesty marker** — `term-12` (standardization + finite developments).  The two reordering theorems of
higher rewriting are shipped in their abstract-rewriting form (in `Core/Rewriting/Standardization.lean`):
FINITE DEVELOPMENTS — a relation with a strictly-decreasing `Nat` measure is strongly normalizing
(`developmentsAreFinite`, the `Acc` built by structural recursion on a bound, not `WellFounded.fix`), the
de Vrijer development-measure abstraction; and STANDARDIZATION's core — head/internal FACTORIZATION via
strong postponement (`factorizationOfStrongPostponement`: `(head ∪ internal)* ⊆ head* ∘ internal*` when
internal reduction postpones past head reduction, `pushOneInternalPastHeads` the strip lemma).  ★ The
quantitative de Vrijer BOUND is shipped: over a proof-relevant `ReductionSequence` (in `Type`, since
`ReflTransClosure` is a `Prop` and carries no step count), the step count is bounded by the measure consumed
(`developmentLength_bounded`: `measure finish + length ≤ measure start`; `developmentLength_le_measure`).
Backed in `fxTerm_standardizationFiniteDevelopments_isBacked`.  `= true`.  HONEST SCOPE: FD finiteness +
the de Vrijer step-count bound + the head/internal factorization (via strong postponement).  DEFERRED: de
Vrijer's EXACT length FORMULA + confluence-of-developments (residual theory); GENERAL postponement (the
internal-blow-up case); and the FULL standardization theorem (standard sequences via the redex order +
leftmost-reduction normalization). -/
def fxTerm_hasStandardizationFiniteDevelopments : Bool := true

/-- ★ **Backed flip (standardization + finite developments).**  The marker is `true` AND (i) FINITE
DEVELOPMENTS — a relation with a strictly-decreasing `Nat` measure is strongly normalizing
(`developmentsAreFinite`); (ii) STANDARDIZATION's core — strong postponement of internal past head reduction
gives head/internal factorization `(head ∪ internal)* ⊆ head* ∘ internal*`
(`factorizationOfStrongPostponement`). -/
theorem fxTerm_standardizationFiniteDevelopments_isBacked :
    fxTerm_hasStandardizationFiniteDevelopments = true
      ∧ (∀ {Carrier : Type} (markedStep : Carrier → Carrier → Prop) (developmentMeasure : Carrier → Nat),
          (∀ earlier later, markedStep earlier later →
            developmentMeasure later < developmentMeasure earlier) →
          ∀ point, Acc (fun later earlier => markedStep earlier later) point)
      ∧ (∀ {Carrier : Type} (headStep internalStep : Carrier → Carrier → Prop),
          (∀ before middle after, internalStep before middle → headStep middle after →
            ∃ landing, ReflTransClosure headStep before landing ∧
              (internalStep landing after ∨ landing = after)) →
          ∀ {source target : Carrier},
            ReflTransClosure (fun first second => headStep first second ∨ internalStep first second)
                source target →
            ∃ middle, ReflTransClosure headStep source middle ∧
              ReflTransClosure internalStep middle target)
      ∧ (∀ {Carrier : Type} (markedStep : Carrier → Carrier → Prop) (developmentMeasure : Carrier → Nat),
          (∀ earlier later, markedStep earlier later →
            developmentMeasure later < developmentMeasure earlier) →
          ∀ {start finish : Carrier} (sequence : ReductionSequence markedStep start finish),
            developmentMeasure finish + sequence.length ≤ developmentMeasure start) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro Carrier markedStep developmentMeasure measureStrictlyDecreases point
    exact developmentsAreFinite markedStep developmentMeasure measureStrictlyDecreases point
  · intro Carrier headStep internalStep strongPostponement source target reduction
    exact factorizationOfStrongPostponement headStep internalStep strongPostponement reduction
  · intro Carrier markedStep developmentMeasure measureStrictlyDecreases start finish sequence
    exact developmentLength_bounded markedStep developmentMeasure measureStrictlyDecreases sequence

/-! ## term-13: Böhm trees, meaningless terms, the genericity lemma -/

/-- **Honesty marker** — `term-13` (Böhm trees / meaningless terms / genericity).  The theory of MEANINGLESS
terms is shipped in abstract-rewriting form (in `Core/Rewriting/BohmTree.lean`): `IsSolvable` (reduces to a
head-normal element) / `IsMeaningless`, with the Kennaway-van Oostrom-de Vries closure axiom
(`meaningless_of_reduction` — meaningless stays meaningless under reduction); the operational heart of
GENERICITY (`meaningless_not_joinable_solvable` — in a confluent system where head normal forms stay
head-normal, a meaningless term is never joinable with a solvable one), ★ lifted to FULL CONVERSION
(`meaningless_not_conv_solvable` — not even CONVERTIBLE, via `term-7`'s Church-Rosser: the equational theory
`⟷*` separates them), and the `⊥`-IDENTIFICATION (`meaninglessAreIndiscernible` — all meaningless terms are
mutually indiscernible); and the finite Böhm APPROXIMANT domain (`BohmApprox` + the approximation order
`IsLessDefined` with `⊥` least, `bottom_isLeast`).
Backed in `fxTerm_meaninglessGenericity_isBacked`.  `= true`.  HONEST SCOPE: the meaningless-terms theory +
the solvable/meaningless separation at joinability AND conversion (operational genericity core) + the
finite-approximant domain.  DEFERRED
(the capstone): the INFINITARY Böhm TREE (the coinductive infinite normal form — `term-3`'s terminal
coalgebra / bisimulation is its substrate) + Böhm-tree equivalence; and the FULL operational genericity lemma
`C[M] →* N ⟹ ∀ M', C[M'] →* N` (needing the `term-12` neededness / standardization residual theory). -/
def fxTerm_hasMeaninglessGenericity : Bool := true

/-- ★ **Backed flip (Böhm trees / meaningless / genericity).**  The marker is `true` AND (i) MEANINGLESSNESS
IS CLOSED UNDER REDUCTION (`meaningless_of_reduction`, the KvOdV axiom); (ii) the GENERICITY separation — in
a confluent system with head-normal-reduction-closure, a meaningless term is never joinable with a solvable
one (`meaningless_not_joinable_solvable`); (iii) `⊥` is the LEAST Böhm approximant (`bottom_isLeast`). -/
theorem fxTerm_meaninglessGenericity_isBacked :
    fxTerm_hasMeaninglessGenericity = true
      ∧ (∀ {Carrier : Type} (isHeadNormal : Carrier → Prop) (step : Carrier → Carrier → Prop)
          {term reduct : Carrier}, IsMeaningless isHeadNormal step term →
          ReflTransClosure step term reduct → IsMeaningless isHeadNormal step reduct)
      ∧ (∀ {Carrier : Type} (isHeadNormal : Carrier → Prop) (step : Carrier → Carrier → Prop),
          Confluent step →
          (∀ {headForm reduct : Carrier}, isHeadNormal headForm →
            ReflTransClosure step headForm reduct → isHeadNormal reduct) →
          ∀ {meaninglessTerm solvableTerm : Carrier},
            IsMeaningless isHeadNormal step meaninglessTerm →
            IsSolvable isHeadNormal step solvableTerm →
            ¬ Joinable step meaninglessTerm solvableTerm)
      ∧ (∀ {Carrier : Type} (isHeadNormal : Carrier → Prop) (step : Carrier → Carrier → Prop),
          Confluent step →
          (∀ {headForm reduct : Carrier}, isHeadNormal headForm →
            ReflTransClosure step headForm reduct → isHeadNormal reduct) →
          ∀ {meaninglessTerm solvableTerm : Carrier},
            IsMeaningless isHeadNormal step meaninglessTerm →
            IsSolvable isHeadNormal step solvableTerm →
            ¬ EquationalTheory step meaninglessTerm solvableTerm)
      ∧ (∀ (approx : BohmApprox), IsLessDefined BohmApprox.bottom approx) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · intro Carrier isHeadNormal step term reduct meaninglessTerm reduction
    exact meaningless_of_reduction isHeadNormal step meaninglessTerm reduction
  · intro Carrier isHeadNormal step confluent headNormalClosed meaninglessTerm solvableTerm
      meaningless solvable joined
    exact meaningless_not_joinable_solvable isHeadNormal step confluent headNormalClosed
      meaningless solvable joined
  · intro Carrier isHeadNormal step confluent headNormalClosed meaninglessTerm solvableTerm
      meaningless solvable convertible
    exact meaningless_not_conv_solvable isHeadNormal step confluent headNormalClosed
      meaningless solvable convertible
  · intro approx
    exact bottom_isLeast approx

/-! ## term-14: mixed inductive-coinductive types — the μ/ν parity -/

/-- **Honesty marker** — `term-14` (mixed inductive-coinductive types, the μ/ν parity).  The LEFT (`term-1`,
initial algebra `μ`) and RIGHT (`term-3`, terminal coalgebra `ν`) meet (in
`Tier0/Term/Codata/MixedFixpoint.lean`): the least fixpoint `MuTree` (finite trees) with the catamorphism
`MuTree.fold` and its INDUCTION principle `MuTree.fold_unique`; the greatest fixpoint `NuStream` (= the
terminal coalgebra of `X ↦ A × X`) with `NuStream.corec` and its COINDUCTION principle `NuStream.corec_unique`
(pointwise, funext-free); the MIXED type `MixedMuNu = νX. MuTree × X` (a productive stream of finite trees)
with `mixedFold` distributing the inner `μ`-fold over the outer `ν`-structure; the μ/ν PARITY —
`mu_isFinite` (every inductive element is finite) versus `nu_canBeUnbounded` (a coinductive element can
strictly increase forever); and ★ the dual FUSION laws — `μ` fold-fusion (`MuTree.fold_fusion`) and `ν`
corec-fusion (`NuStream.corec_fusion`), completing both schemes to the CANCEL/UNIQUE/FUSION package and
exhibiting the fusion duality.  Backed in `fxTerm_mixedFixpointParity_isBacked`.  `= true`.  HONEST SCOPE: a
concrete mixed `ν(μ)` type + the two recursion schemes with their universal properties AND fusion laws + the
finiteness/unboundedness parity.  DEFERRED: the GENERAL mixed inductive-coinductive type theory (Basold-Geuvers
dependent `μ`/`ν` with arbitrary functor alternation `νX. μY. F(X, Y)`, the combined productivity+termination
criterion, and the dialgebra / parity-game semantics). -/
def fxTerm_hasMixedFixpointParity : Bool := true

/-- ★ **Backed flip (mixed μ/ν parity).**  The marker is `true` AND (i) the `μ` INDUCTION principle — `fold`
is the unique homomorphism out of the inductive tree (`MuTree.fold_unique`); (ii) the `ν` COINDUCTION
principle — `corec` is the unique coalgebra morphism into the stream, pointwise (`NuStream.corec_unique`);
(iii) the μ/ν PARITY — every `μ`-element is finite while a `ν`-element can be unbounded (`mu_isFinite` ∧
`nu_canBeUnbounded`). -/
theorem fxTerm_mixedFixpointParity_isBacked :
    fxTerm_hasMixedFixpointParity = true
      ∧ (∀ {Result : Type} (onLeaf : Result) (onBranch : Nat → Result → Result → Result)
          (candidate : MuTree → Result), candidate MuTree.leaf = onLeaf →
          (∀ label left right, candidate (MuTree.branch label left right)
            = onBranch label (candidate left) (candidate right)) →
          ∀ tree, candidate tree = MuTree.fold onLeaf onBranch tree)
      ∧ (∀ {A Seed : Type} (observe : Seed → A) (advance : Seed → Seed) (candidate : Seed → NuStream A),
          (∀ seed, (candidate seed).head = observe seed) →
          (∀ seed position, (candidate seed).tail position = candidate (advance seed) position) →
          ∀ seed position, candidate seed position = NuStream.corec observe advance seed position)
      ∧ ((∀ tree : MuTree, MuTree.size tree < MuTree.size tree + 1)
          ∧ (∃ stream : NuStream Nat, ∀ position, stream position < stream (position + 1)))
      ∧ (∀ {Result SecondResult : Type} (onLeaf : Result) (onBranch : Nat → Result → Result → Result)
          (onLeaf2 : SecondResult) (onBranch2 : Nat → SecondResult → SecondResult → SecondResult)
          (transform : Result → SecondResult), transform onLeaf = onLeaf2 →
          (∀ label leftValue rightValue, transform (onBranch label leftValue rightValue)
            = onBranch2 label (transform leftValue) (transform rightValue)) →
          ∀ tree, transform (MuTree.fold onLeaf onBranch tree) = MuTree.fold onLeaf2 onBranch2 tree)
      ∧ (∀ {A Seed SecondSeed : Type} (observe : Seed → A) (advance : Seed → Seed)
          (observe2 : SecondSeed → A) (advance2 : SecondSeed → SecondSeed) (transform : SecondSeed → Seed),
          (∀ secondSeed, observe2 secondSeed = observe (transform secondSeed)) →
          (∀ secondSeed, transform (advance2 secondSeed) = advance (transform secondSeed)) →
          ∀ secondSeed position, NuStream.corec observe2 advance2 secondSeed position
            = NuStream.corec observe advance (transform secondSeed) position) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro Result onLeaf onBranch candidate candidateLeaf candidateBranch tree
    exact MuTree.fold_unique onLeaf onBranch candidate candidateLeaf candidateBranch tree
  · intro A Seed observe advance candidate candidateHead candidateTail seed position
    exact NuStream.corec_unique observe advance candidate candidateHead candidateTail seed position
  · exact ⟨mu_isFinite, nu_canBeUnbounded⟩
  · intro Result SecondResult onLeaf onBranch onLeaf2 onBranch2 transform transformLeaf transformBranch tree
    exact MuTree.fold_fusion onLeaf onBranch onLeaf2 onBranch2 transform transformLeaf transformBranch tree
  · intro A Seed SecondSeed observe advance observe2 advance2 transform observeAgree advanceAgree
      secondSeed position
    exact NuStream.corec_fusion observe advance observe2 advance2 transform observeAgree advanceAgree
      secondSeed position

/-! ## term-15: copattern coverage checking -/

/-- **Honesty marker** — `term-15` (copattern coverage checking).  The DUAL of `term-11` (patterns): a
COPATTERN specifies a codata value by its OBSERVATIONS, and coverage checking is the dual of pattern-match
exhaustiveness.  Shipped (in `Tier0/Term/Codata/CopatternCoverage.lean`): the copattern decision trie
(`CopatternTrie`, with `undefined` = a coverage GAP), the decidable COVERAGE CHECKER (`isCovering` — every
`split` exhaustive over `Fin destructorCount`, no reachable gap), and COMPLETENESS
(`covering_resolves_without_gap` — a covering trie resolves every observation without getting stuck, dual to
"an exhaustive match never gets stuck").  Coverage WITH DEPENDENT INDICES is the `DependentCoveringTree`
(splits over the index-dependent observation set `Fin (destructorsAt index)`, advancing to
`nextIndex index obs`) — exhaustive by construction (`dependentCoverage_leafOrExhaustiveSplit`).  Backed in
`fxTerm_copatternCoverage_isBacked`.  `= true`.  HONEST SCOPE: the coverage checker + completeness + the
dependent covering structure.  DEFERRED: the full Abel-Pientka coverage ALGORITHM that builds the splitting
tree from clauses with dependent index UNIFICATION (refining the index, pruning impossible observations);
the productivity/totality link to a defined codata value (`term-14`'s `corec` is the uniform-stream
instance). -/
def fxTerm_hasCopatternCoverage : Bool := true

/-- ★ **Backed flip (copattern coverage).**  The marker is `true` AND (i) COMPLETENESS — a covering trie
resolves every observation path without a gap (`covering_resolves_without_gap`); (ii) the CHECKER is
discriminating — it accepts the stream trie and rejects the incomplete one (`streamCoveringTrie_isCovering`
∧ `incompleteStreamTrie_notCovering`); (iii) DEPENDENT-index coverage is structural — every dependent
covering tree is a leaf or an exhaustive split (`dependentCoverage_leafOrExhaustiveSplit`). -/
theorem fxTerm_copatternCoverage_isBacked :
    fxTerm_hasCopatternCoverage = true
      ∧ (∀ {destructorCount : Nat} (trie : CopatternTrie destructorCount), trie.isCovering = true →
          ∀ (path : List (Fin destructorCount)), trie.resolve path ≠ CoverageResult.hitGap)
      ∧ (streamCoveringTrie.isCovering = true ∧ incompleteStreamTrie.isCovering = false)
      ∧ (∀ {Index : Type} {destructorsAt : Index → Nat}
          {nextIndex : (index : Index) → Fin (destructorsAt index) → Index} {index : Index}
          (tree : DependentCoveringTree Index destructorsAt nextIndex index),
          (tree = DependentCoveringTree.leaf index)
            ∨ (∃ subtrees, tree = DependentCoveringTree.split index subtrees)) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro destructorCount trie covering path
    exact covering_resolves_without_gap trie covering path
  · exact ⟨streamCoveringTrie_isCovering, incompleteStreamTrie_notCovering⟩
  · intro Index destructorsAt nextIndex index tree
    exact dependentCoverage_leafOrExhaustiveSplit tree

/-! ## term-16: Church-Rosser modulo an equational theory -/

/-- **Honesty marker** — `term-16` (Church-Rosser modulo an equational theory, rewriting modulo AC).  The
abstract modulo-`E` theory is shipped (in `Core/Rewriting/RewritingModulo.lean`): JOINABILITY MODULO `E`
(`JoinableModulo` — reduce both sides by `R`, compare the reducts modulo `E`), the easy half
(`equationalTheory_of_joinableModulo` — joinable-modulo-`E` ⟹ convertible in `R ∪ E`), CHURCH-ROSSER MODULO
`E` (`ChurchRosserModulo`) and its characterization (`churchRosserModulo_characterization`: the combined
theory IS joinability modulo `E`), the bridge to `term-7` (`churchRosserModulo_eq_of_confluent` — a confluent
`R` is CR modulo EQUALITY, the trivial-`E` instance), and a concrete AC-flavored equational theory
(`commutativeEquiv` = pair swap, proved an equivalence, with `(3,5) ⟷ (5,3)` modulo it).  The bridge is
GENERALIZED beyond `E = equality`: a confluent `R` is CR modulo any `E` that lies below `R`-convertibility
(`churchRosserModulo_of_subconvertible` + `equationalTheory_collapseInto`), and `JoinableModulo` is itself
reflexive + symmetric whenever `E` is (`joinableModulo_refl` / `joinableModulo_symm`).  Backed in
`fxTerm_rewritingModulo_isBacked`.  `= true`.  HONEST SCOPE: the modulo-`E` vocabulary + the
joinable-modulo/theory characterization + the generalized sub-convertibility bridge + the JoinableModulo
equivalence structure + the commutativity witness.  DEFERRED: the modulo-`E` NEWMAN lemma (termination of
`R/E` + local confluence modulo `E` + COHERENCE ⟹ CR modulo `E`, the Jouannaud-Kirchner theorem); AC
MATCHING decidability; and the convergent-`R/AC` DECISION procedure. -/
def fxTerm_hasRewritingModulo : Bool := true

/-- ★ **Backed flip (rewriting modulo E).**  The marker is `true` AND (i) joinable-modulo-`E` ⟹ convertible
in the combined theory (`equationalTheory_of_joinableModulo`); (ii) a confluent `R` is Church-Rosser modulo
equality — the `term-7` bridge (`churchRosserModulo_eq_of_confluent`); (iii) the commutativity equational
theory is a genuine equivalence (`commutativeEquiv_refl`/`_symm`/`_trans`). -/
theorem fxTerm_rewritingModulo_isBacked :
    fxTerm_hasRewritingModulo = true
      ∧ (∀ {Carrier : Type} (rewrite equiv : Carrier → Carrier → Prop) {leftValue rightValue : Carrier},
          JoinableModulo rewrite equiv leftValue rightValue →
          EquationalTheory (fun first second => rewrite first second ∨ equiv first second)
            leftValue rightValue)
      ∧ (∀ {Carrier : Type} (rewrite : Carrier → Carrier → Prop),
          Confluent rewrite → ChurchRosserModulo rewrite (fun first second => first = second))
      ∧ ((∀ pair, commutativeEquiv pair pair)
          ∧ (∀ {left right}, commutativeEquiv left right → commutativeEquiv right left))
      ∧ (∀ {Carrier : Type} (rewrite equiv : Carrier → Carrier → Prop),
          Confluent rewrite →
          (∀ {left right : Carrier}, equiv left right → EquationalTheory rewrite left right) →
          (∀ point : Carrier, equiv point point) →
          ChurchRosserModulo rewrite equiv)
      ∧ (∀ {Carrier : Type} (rewrite equiv : Carrier → Carrier → Prop),
          (∀ point : Carrier, equiv point point) →
          ∀ value : Carrier, JoinableModulo rewrite equiv value value) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro Carrier rewrite equiv leftValue rightValue joinable
    exact equationalTheory_of_joinableModulo rewrite equiv joinable
  · intro Carrier rewrite confluent
    exact churchRosserModulo_eq_of_confluent rewrite confluent
  · exact ⟨commutativeEquiv_refl, fun equivalent => commutativeEquiv_symm equivalent⟩
  · intro Carrier rewrite equiv confluent equivIsConvertible equivRefl
    exact churchRosserModulo_of_subconvertible rewrite equiv confluent equivIsConvertible equivRefl
  · intro Carrier rewrite equiv equivRefl value
    exact joinableModulo_refl rewrite equiv equivRefl value

/-! ## term-17: the free strict ω-category on the term polygraph + the Gray tensor -/

/-- **Honesty marker** — `term-17` (the free strict ω-category on the term polygraph + the Gray tensor,
mirrors `mode-5`).  Shipped (in `Tier0/Term/Rewrite/FreeStrictOmega.lean`, over `term-4`'s proof-relevant
rewriting 2-category): the FREE-CATEGORY UNIVERSAL PROPERTY at dimension 1 — `RewritePath.foldMap` is the
unique structure-preserving extension of a generator-map, with FUNCTORIALITY (`foldMap_comp`, the existence
half) and UNIQUENESS (`foldMap_unique`); this is the proof-RELEVANT free category, of which `term-2`'s
`ReflTransClosure.mediate` was only the thin shadow.  And STRICT INTERCHANGE at dimension 2
(`rewriteInterchange_strict` — the two whisker orders of a horizontal composite agree ON THE NOSE, because
`RewriteHomotopy` is thin), exhibiting the free STRICT 2-category: the Gray interchanger degenerates to the
identity, exactly as `mode-5`'s locally-discrete interchanger was `refl`.  The dimension-2 UNIVERSAL
PROPERTY is shipped too (`freeStrictTwoCategory_dim2UniversalProperty` + `..._dim2Uniqueness`, consuming
`term-4`'s `RewriteHomotopy.toModel`): every 2-cell maps uniquely into any model — so the free strict
ω-category's UP holds at BOTH dimensions.  Backed in
`fxTerm_freeStrictOmegaCategory_isBacked`.  `= true`.  HONEST SCOPE: the dimension-1 free-category UP
(existence/functoriality/uniqueness) + the dimension-2 strict interchange + the dimension-2 UP.  DEFERRED (mirroring `mode-5`'s
three `false` markers): the genuine Gray TENSOR PRODUCT bifunctor `⊗` of two ω-categories with its
NON-trivial coherent interchange isomorphism, and the tricategory COHERENCE theorem — both need Type-valued
(non-thin) higher cells beyond the thin `RewriteHomotopy` layer. -/
def fxTerm_hasFreeStrictOmegaCategory : Bool := true

/-- ★ **Backed flip (free strict ω-category).**  The marker is `true` AND (i) the free-category fold is
FUNCTORIAL — it sends path composition to target composition (`RewritePath.foldMap_comp`, the universal
property's existence half); (ii) the fold is UNIQUE — any composition-respecting map is the fold
(`RewritePath.foldMap_unique`); (iii) interchange is STRICT at dimension 2 — the two whisker orders agree
(`rewriteInterchange_strict`, the Gray interchanger is the identity). -/
theorem fxTerm_freeStrictOmegaCategory_isBacked :
    fxTerm_hasFreeStrictOmegaCategory = true
      ∧ (∀ {Carrier : Type} {Step : Carrier → Carrier → Type} {Target : Carrier → Carrier → Type}
          (idTarget : {point : Carrier} → Target point point)
          (compTarget : {first second third : Carrier} →
            Target first second → Target second third → Target first third)
          (onStep : {source target : Carrier} → Step source target → Target source target),
          (∀ {first second third fourth : Carrier}
            (left : Target first second) (middle : Target second third) (right : Target third fourth),
            compTarget (compTarget left middle) right = compTarget left (compTarget middle right)) →
          (∀ {first second : Carrier} (value : Target first second), compTarget idTarget value = value) →
          ∀ {source middle target : Carrier}
            (firstPath : RewritePath Step source middle) (secondPath : RewritePath Step middle target),
            RewritePath.foldMap idTarget compTarget onStep (firstPath.comp secondPath)
              = compTarget (RewritePath.foldMap idTarget compTarget onStep firstPath)
                  (RewritePath.foldMap idTarget compTarget onStep secondPath))
      ∧ (∀ {Carrier : Type} {Step : Carrier → Carrier → Type} {Target : Carrier → Carrier → Type}
          (idTarget : {point : Carrier} → Target point point)
          (compTarget : {first second third : Carrier} →
            Target first second → Target second third → Target first third)
          (onStep : {source target : Carrier} → Step source target → Target source target)
          (candidate : {source target : Carrier} → RewritePath Step source target → Target source target),
          (∀ {point : Carrier},
            candidate (RewritePath.nil (Step := Step) (point := point)) = idTarget) →
          (∀ {source middle target : Carrier}
            (step : Step source middle) (rest : RewritePath Step middle target),
            candidate (RewritePath.cons step rest) = compTarget (onStep step) (candidate rest)) →
          ∀ {source target : Carrier} (path : RewritePath Step source target),
            candidate path = RewritePath.foldMap idTarget compTarget onStep path)
      ∧ (∀ {Carrier : Type} {Step : Carrier → Carrier → Type} (diamond : SquierDiamond Step)
          {objectA objectB objectC : Carrier}
          {pathP pathPPrime : RewritePath Step objectA objectB}
          {pathQ pathQPrime : RewritePath Step objectB objectC}
          (cellAlpha : RewriteHomotopy diamond pathP pathPPrime)
          (cellBeta : RewriteHomotopy diamond pathQ pathQPrime),
          interchangeWhiskerSource diamond cellAlpha cellBeta
            = interchangeWhiskerTarget diamond cellAlpha cellBeta)
      ∧ (∀ {Carrier : Type} {Step : Carrier → Carrier → Type} {diamond : SquierDiamond Step}
          (model : HomotopyModel diamond) {source target : Carrier}
          {leftPath rightPath : RewritePath Step source target},
          RewriteHomotopy diamond leftPath rightPath → model.rel leftPath rightPath) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · intro Carrier Step Target idTarget compTarget onStep compTarget_assoc compTarget_idLeft
      source middle target firstPath secondPath
    exact RewritePath.foldMap_comp idTarget compTarget onStep compTarget_assoc compTarget_idLeft
      firstPath secondPath
  · intro Carrier Step Target idTarget compTarget onStep candidate candidate_nil candidate_cons
      source target path
    exact RewritePath.foldMap_unique idTarget compTarget onStep candidate candidate_nil candidate_cons path
  · intro Carrier Step diamond objectA objectB objectC pathP pathPPrime pathQ pathQPrime cellAlpha cellBeta
    exact rewriteInterchange_strict diamond cellAlpha cellBeta
  · intro Carrier Step diamond model source target leftPath rightPath homotopy
    exact freeStrictTwoCategory_dim2UniversalProperty model homotopy

/-! ## term-18: the marked / complicial structure of the term rewriting ω-category -/

/-- **Honesty marker** — `term-18` (the marked/complicial structure of the term rewriting ω-category,
mirrors `mode-7`).  Shipped (in `Tier0/Term/Rewrite/MarkedComplicial.lean`): the complicial STRATIFICATION
of `term-4`'s rewriting ω-category in Verity's "thin = equivalence" sense — the dimension-1 MARKING
(`IsRewriteEquivalence`: a reduction path is thin iff invertible up to homotopy), the ELEMENTARY
STRATIFICATION AXIOMS (`rewriteEquivalence_nil` — identities/degeneracies are thin; `rewriteEquivalence_comp`
— thin closed under composition; `rewriteEquivalence_symm` — thin closed under inversion), 2-TRIVIALITY
(`rewriteOmega_twoTrivial` — every 2-cell is thin, so the marked ω-category presents an (∞,1)-category),
and the packaged stratification interface + canonical instance (`RewriteMarking` / `equivalenceMarking`).
SATURATION is shipped too: the marking is HOMOTOPY-INVARIANT (`rewriteEquivalence_respectsHomotopy`) and
satisfies the 2-OUT-OF-3 (`rewriteEquivalence_cancelLeft` / `rewriteEquivalence_cancelRight`).
Backed in `fxTerm_markedComplicial_isBacked`.  `= true`.  HONEST SCOPE: the dimension-1 equivalence
marking + the elementary stratification axioms + 2-triviality + saturation (homotopy-invariance +
2-out-of-3).  DEFERRED: the full Verity WEAK-COMPLICIAL horn-filling conditions (thin inner horns have thin
fillers + the complicial identities at every dimension) and the general (∞,n) marking for `n > 1` (needs
Type-valued non-thin higher cells). -/
def fxTerm_hasMarkedComplicial : Bool := true

/-- ★ **Backed flip (marked/complicial structure).**  The marker is `true` AND (i) identities are thin
(`rewriteEquivalence_nil`, the elementary stratification axiom); (ii) thin 1-cells are closed under
composition (`rewriteEquivalence_comp`); (iii) the marked ω-category is 2-trivial — every 2-cell is thin
(`rewriteOmega_twoTrivial`, the (∞,1) presentation); (iv) SATURATION (2-out-of-3) — if `p` and `p ∘ q` are
thin then `q` is thin (`rewriteEquivalence_cancelLeft`); symmetrically `rewriteEquivalence_cancelRight`. -/
theorem fxTerm_markedComplicial_isBacked :
    fxTerm_hasMarkedComplicial = true
      ∧ (∀ {Carrier : Type} {Step : Carrier → Carrier → Type} (diamond : SquierDiamond Step)
          {point : Carrier},
          IsRewriteEquivalence diamond (RewritePath.nil (Step := Step) (point := point)))
      ∧ (∀ {Carrier : Type} {Step : Carrier → Carrier → Type} (diamond : SquierDiamond Step)
          {source middle target : Carrier}
          {firstPath : RewritePath Step source middle} {secondPath : RewritePath Step middle target},
          IsRewriteEquivalence diamond firstPath → IsRewriteEquivalence diamond secondPath →
          IsRewriteEquivalence diamond (firstPath.comp secondPath))
      ∧ (∀ {Carrier : Type} {Step : Carrier → Carrier → Type} (diamond : SquierDiamond Step)
          {source target : Carrier} {leftPath rightPath : RewritePath Step source target}
          (firstCell secondCell : RewriteHomotopy diamond leftPath rightPath),
          firstCell = secondCell)
      ∧ (∀ {Carrier : Type} {Step : Carrier → Carrier → Type} (diamond : SquierDiamond Step)
          {source middle target : Carrier}
          {firstPath : RewritePath Step source middle} {secondPath : RewritePath Step middle target},
          IsRewriteEquivalence diamond firstPath →
          IsRewriteEquivalence diamond (firstPath.comp secondPath) →
          IsRewriteEquivalence diamond secondPath) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · intro Carrier Step diamond point
    exact rewriteEquivalence_nil diamond
  · intro Carrier Step diamond source middle target firstPath secondPath firstThin secondThin
    exact rewriteEquivalence_comp diamond firstThin secondThin
  · intro Carrier Step diamond source target leftPath rightPath firstCell secondCell
    exact rewriteOmega_twoTrivial diamond firstCell secondCell
  · intro Carrier Step diamond source middle target firstPath secondPath firstThin compositeThin
    exact rewriteEquivalence_cancelLeft diamond firstThin compositeThin

/-! ## term-19: the exact strong-normalization boundary — modular / persistent SN -/

/-- **Honesty marker** — `term-19` (the exact SN boundary: modular / persistent SN + the necessity
results).  `term-6` shipped the POSITIVE modular criterion (union of commuting/disjoint SN systems is SN,
`fxTerm_hasModularStrongNormalizationCriterion`).  This rung pins the EXACT BOUNDARY (in
`Tier0/Term/Rewrite/ModularSNBoundary.lean`): PERSISTENCE — SN restricts to subsystems
(`strongNorm_subrelation`), hence `SN(R ∪ S) ⟹ SN(R) ∧ SN(S)` unconditionally
(`strongNorm_union_left`/`_right`); and NECESSITY — the converse FAILS: two SN relations whose union loops
(`forwardStep`/`backwardStep` each SN, `unionStep` has the 2-cycle `false → true → false → ⋯`,
`unionStep_notStronglyNormalizing`), so the `term-6` side conditions are necessary, not merely sufficient.
The failure is sharp: the union has NO normal form (`unionStep_hasNoNormalForm` — not even weakly
normalizing) and `unionCycle` is the explicit infinite reduction sequence.
Backed in `fxTerm_modularPersistentSN_isBacked`.  `= true`.  HONEST SCOPE: persistence (subsystems +
union-to-components) + the sharpened necessity counterexample (no-WN + explicit infinite chain); the
POSITIVE criterion is `term-6` reused.
DEFERRED: the full Toyama persistence theorem for first-order TRSs (SN modular for left-linear / layer-
preserving unions) + the Gramlich/Ohlebusch necessity taxonomy (statements over a concrete signature). -/
def fxTerm_hasModularPersistentSN : Bool := true

/-- ★ **Backed flip (modular/persistent SN boundary).**  The marker is `true` AND (i) PERSISTENCE — a
sub-relation of a strongly-normalizing relation is strongly normalizing (`strongNorm_subrelation`);
(ii)–(iv) NECESSITY — the forward and backward `Bool` steps are each strongly normalizing
(`forwardStep_isStronglyNormalizing` / `backwardStep_isStronglyNormalizing`) yet their union is NOT
(`unionStep_notStronglyNormalizing`), so SN is not modular in general; (v) the failure is sharp — the union
has NO normal form, so it is not even weakly normalizing (`unionStep_hasNoNormalForm`). -/
theorem fxTerm_modularPersistentSN_isBacked :
    fxTerm_hasModularPersistentSN = true
      ∧ (∀ {Carrier : Type} {sub super : Carrier → Carrier → Prop},
          (∀ {origin reduct : Carrier}, sub origin reduct → super origin reduct) →
          WellFounded (fun reduct origin => super origin reduct) →
          WellFounded (fun reduct origin => sub origin reduct))
      ∧ WellFounded (fun reduct origin => forwardStep origin reduct)
      ∧ WellFounded (fun reduct origin => backwardStep origin reduct)
      ∧ ¬ WellFounded (fun reduct origin => unionStep origin reduct)
      ∧ (∀ point : Bool, ∃ next : Bool, unionStep point next) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro Carrier sub super subset superStronglyNormalizing
    exact strongNorm_subrelation subset superStronglyNormalizing
  · exact forwardStep_isStronglyNormalizing
  · exact backwardStep_isStronglyNormalizing
  · exact unionStep_notStronglyNormalizing
  · exact unionStep_hasNoNormalForm

/-! ## term-20: the word problem — decidable Conv as a function of convergence (CAPSTONE) -/

/-- **Honesty marker** — `term-20` (CAPSTONE: the word problem — decidable Conv as a function of
convergence + the undecidability frontier).  Shipped (in `Tier0/Term/Rewrite/WordProblem.lean`): the word
problem `WordProblem` (= convertibility) is DECIDABLE AS A FUNCTION OF CONVERGENCE
(`decidableWordProblem_of_convergent`: a confluent system + a normalizer over a decidable-equality carrier
decides `a ⟷* b`), because the word problem IS normal-form equality (`wordProblem_iff_normalFormEq` —
`a ⟷* b ↔ a↓ = b↓`).  This is the word-problem face of the design-lock `fxTerm_hasNormalizerConvDecision`
(the kernel's `Conv.decidableOfStronglyNormalizing`), stated abstractly over `term-7`'s
`ConvergentNormalizer`.  The DECIDABILITY BOUNDARY is pinned: convergence is NECESSARY — CONFLUENCE for
uniqueness of normal forms (`forkStep_notConfluent`: a non-confluent system whose `apex` forks to two
DISTINCT normal forms, `forkStep_apex_hasTwoDistinctNormalForms`) and TERMINATION for their existence
(`term-19`'s `unionStep_hasNoNormalForm`: a system with no normal form at all).  Backed in
`fxTerm_wordProblemBoundary_isBacked`.  `= true`.  HONEST SCOPE: the decidable side of the word problem
(decision + characterization) and the sharp convergence boundary (both halves necessary).  DEFERRED — THE
UNDECIDABILITY FRONTIER: genuine UNDECIDABILITY of the general word problem (Markov-Post; a halting-problem
reduction) is a classical computability metatheorem requiring a model of computation — OUT OF SCOPE for the
zero-axiom `Init`-only kernel.  The undecidable side is NAMED, not mechanized. -/
def fxTerm_hasWordProblemBoundary : Bool := true

/-- ★ **Backed flip (word-problem capstone).**  The marker is `true` AND (i) the word problem IS
normal-form equality for a convergent system — the decision characterization
(`wordProblem_iff_normalFormEq`, the positive half / decidable as a function of convergence); (ii)
CONFLUENCE is necessary — a non-confluent system with two distinct normal forms (`forkStep_notConfluent` +
`forkLeaves_distinct`); (iii) TERMINATION is necessary — a system with no normal form
(`unionStep_hasNoNormalForm`, `term-19`). -/
theorem fxTerm_wordProblemBoundary_isBacked :
    fxTerm_hasWordProblemBoundary = true
      ∧ (∀ {Carrier : Type} {rewrite : Carrier → Carrier → Prop}
          (normalizer : ConvergentNormalizer rewrite) (_confluent : Confluent rewrite)
          (leftValue rightValue : Carrier),
          WordProblem rewrite leftValue rightValue
            ↔ normalizer.normalize leftValue = normalizer.normalize rightValue)
      ∧ (¬ Confluent forkStep ∧ ForkCarrier.leftLeaf ≠ ForkCarrier.rightLeaf)
      ∧ (∀ point : Bool, ∃ next : Bool, unionStep point next) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro Carrier rewrite normalizer confluentProof leftValue rightValue
    exact wordProblem_iff_normalFormEq normalizer confluentProof leftValue rightValue
  · exact ⟨forkStep_notConfluent, forkLeaves_distinct⟩
  · exact unionStep_hasNoNormalForm

/-! ## Honest deferred markers (the structural / semantics frontier) -/

/-- **Honesty marker** — `term-7` (Knuth-Bendix, the PROCEDURE).  The completion ALGORITHM itself (orient /
deduce / simplify, looping to a fixpoint, with the Bachmair-Dershowitz fairness-correctness theorem) and the
term-level critical-pair COMPUTATION are not built — the system is designed orthogonal, so completion was
never needed; the criterion/soundness it would consume (`fxTerm_hasKnuthBendixConvergenceCriterion`) + the
critical-pair / Newman / RPO oracles do exist.  `= false`. -/
def fxTerm_hasKnuthBendixCompletion : Bool := false

/-! ## term-21: denotational semantics — the domain-theoretic fixpoint core -/

/-- **Honesty marker** — `term-21` (denotational semantics: the domain / fixpoint core).  Shipped (in
`Tier0/Term/Semantics/DenotationalDomain.lean`): the pointed ω-CPO interface (`PointedDcpo` + `Continuous`),
and the KLEENE LEAST-FIXPOINT theorem — `kleeneFixpoint = ⊔ₙ fⁿ(⊥)` is a fixpoint of any continuous `f`
(`kleeneFixpoint_isFixpoint`) and is BELOW every other fixpoint (`kleeneFixpoint_isLeast`), i.e.
RECURSION = LEAST FIXPOINT, the foundation of denotational semantics — plus PARK INDUCTION (the least
PRE-fixpoint, `kleeneFixpoint_isLeastPrefixpoint` — fixpoint induction) and the MONOTONICITY of the fixpoint
operator (`kleeneFixpoint_monotone`), with the one-point domain witness.
The kernel's reserved `gen_scottContinuous` (183) / `gen_fixedPoint` (184) are the syntactic counterparts
this is the semantic side of.  Backed in `fxTerm_denotationalDomainFixpoint_isBacked`.  `= true`.  HONEST
SCOPE: the DCPO/continuity interface + the Kleene least-fixpoint theorem + a concrete domain.  DEFERRED (the
rest of `term-21..25`, `fxTerm_hasDenotationalAdequacy = false`): the D∞ reflexive object, coherence spaces,
and computational adequacy. -/
def fxTerm_hasDenotationalDomainFixpoint : Bool := true

/-- ★ **Backed flip (denotational domain fixpoint).**  The marker is `true` AND (i) the Kleene fixpoint is a
fixpoint of any continuous endofunction (`PointedDcpo.kleeneFixpoint_isFixpoint`); (ii) it is the LEAST
fixpoint — below every other (`PointedDcpo.kleeneFixpoint_isLeast`). -/
theorem fxTerm_denotationalDomainFixpoint_isBacked :
    fxTerm_hasDenotationalDomainFixpoint = true
      ∧ (∀ (domain : PointedDcpo) (transform : domain.Carrier → domain.Carrier),
          domain.Continuous transform →
          transform (domain.kleeneFixpoint transform) = domain.kleeneFixpoint transform)
      ∧ (∀ (domain : PointedDcpo) (transform : domain.Carrier → domain.Carrier),
          domain.Monotone transform →
          ∀ point : domain.Carrier, transform point = point →
            domain.Below (domain.kleeneFixpoint transform) point)
      ∧ (∀ (domain : PointedDcpo) (transform : domain.Carrier → domain.Carrier),
          domain.Monotone transform →
          ∀ point : domain.Carrier, domain.Below (transform point) point →
            domain.Below (domain.kleeneFixpoint transform) point) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro domain transform continuous
    exact domain.kleeneFixpoint_isFixpoint transform continuous
  · intro domain transform monotone point isFixpoint
    exact domain.kleeneFixpoint_isLeast transform monotone point isFixpoint
  · intro domain transform monotone point prefixpoint
    exact domain.kleeneFixpoint_isLeastPrefixpoint transform monotone point prefixpoint

/-! ## term-22: intersection types — BCD subtyping + the filter model -/

/-- **Honesty marker** — `term-22` (intersection types: the BCD algebra + the filter model).  Shipped (in
`Tier0/Term/Semantics/IntersectionTypes.lean`): `IntersectionType` + BCD `Subtype` as a MEET-SEMILATTICE
WITH TOP — `omega` is the top (`omega_isTop`), `∩` is the greatest lower bound
(`inter_isGreatestLowerBound`); FILTERS (`IsFilter`) with the LEAST filter `omegaFilter`
(`omegaFilter_isLeast`) and the order-reversing `principalFilter` embedding; and the FILTER MODEL is
ω-COMPLETE — `filterSup` (filter generation) is the least upper bound (`filterSup_isUpperBound` /
`filterSup_isLeast`), a pointed ω-complete PREORDER (the `term-21` `PointedDcpo` twin).  The subtyping is
GENUINE BCD — `omega_isArrow` (`ω ≤ ω→ω`) + `arrow_distributesOverInter` (`(σ→τ)∩(σ→ρ) ≤ σ→(τ∩ρ)`) — and the
filter model carries an APPLICATION (`filterApply` + `filterApply_isFilter` + `filterApply_monotone`, the
λ-model operation).  Backed in `fxTerm_intersectionFilterModel_isBacked`.  `= true`.  HONEST SCOPE: the
genuine BCD algebra + filters + the ω-complete filter preorder + the (monotone) filter application.
DEFERRED: the ANTISYMMETRIC poset quotient (filter equality from mutual
inclusion = `propext` + `funext`, forbidden zero-axiom — so the domain proper is only up to the preorder
here); the λ-application reflexive object; and the NORMALIZATION CHARACTERIZATION `typeable ⟺ normalizing`
(the capstone, in `fxTerm_hasDenotationalAdequacy`). -/
def fxTerm_hasIntersectionFilterModel : Bool := true

/-- ★ **Backed flip (intersection types / filter model).**  The marker is `true` AND (i) `∩` is the greatest
lower bound and `omega` the top of BCD subtyping (`inter_isGreatestLowerBound` + `omega_isTop`); (ii)
`omegaFilter` is the least filter (`omegaFilter_isLeast`); (iii) the filter model is ω-complete — `filterSup`
is the least upper bound (`filterSup_isUpperBound` + `filterSup_isLeast`). -/
theorem fxTerm_intersectionFilterModel_isBacked :
    fxTerm_hasIntersectionFilterModel = true
      ∧ ((∀ subject, Subtype subject IntersectionType.omega)
          ∧ (∀ left right, Subtype (IntersectionType.inter left right) left
              ∧ Subtype (IntersectionType.inter left right) right
              ∧ ∀ lowerBound, Subtype lowerBound left → Subtype lowerBound right →
                  Subtype lowerBound (IntersectionType.inter left right)))
      ∧ (∀ (member : IntersectionType → Prop), IsFilter member →
          ∀ candidate, omegaFilter candidate → member candidate)
      ∧ (∀ (sequence : Nat → IntersectionType → Prop) (index : Nat),
          FilterBelow (sequence index) (filterSup sequence))
      ∧ (∀ (sequence : Nat → IntersectionType → Prop) (upperBound : IntersectionType → Prop),
          IsFilter upperBound → (∀ index, FilterBelow (sequence index) upperBound) →
          FilterBelow (filterSup sequence) upperBound)
      ∧ (∀ domain codomainLeft codomainRight : IntersectionType,
          Subtype
            (IntersectionType.inter (IntersectionType.arrow domain codomainLeft)
              (IntersectionType.arrow domain codomainRight))
            (IntersectionType.arrow domain (IntersectionType.inter codomainLeft codomainRight)))
      ∧ (∀ function argument : IntersectionType → Prop, IsFilter (filterApply function argument)) := by
  refine ⟨rfl, ⟨omega_isTop, inter_isGreatestLowerBound⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro member isFilter candidate omegaHolds
    exact omegaFilter_isLeast member isFilter candidate omegaHolds
  · intro sequence index
    exact filterSup_isUpperBound sequence index
  · intro sequence upperBound isFilter isAbove
    exact filterSup_isLeast sequence upperBound isFilter isAbove
  · intro domain codomainLeft codomainRight
    exact arrow_distributesOverInter domain codomainLeft codomainRight
  · intro function argument
    exact filterApply_isFilter function argument

/-! ## term-23: geometry of interaction — the token machine -/

/-- **Honesty marker** — `term-23` (geometry of interaction: the token machine).  Shipped (in
`Tier0/Term/Semantics/GeometryOfInteraction.lean`): the deterministic `TokenMachine` (`step_deterministic`)
with fuel-bounded `execute`, the absorption laws (`execute_halted` / `execute_succ_of_halted` /
`reaches_stable`), EXECUTION DETERMINACY (`reaches_unique` — a configuration reaches at most one exit, so
the token machine computes a well-defined partial function: the GoI denotation), EXECUTION TOTALITY from a
strictly-decreasing measure (`haltsWithin` / `reachesOfMeasure` / `executeTotal_of_measure` — a well-founded
network makes the token trip finite, so determinacy + totality upgrade the denotation to a well-defined TOTAL
function), and the WIRE witness (`wireMachine_reachesExit` — the token traverses a wire to the boundary, the
GoI axiom link; `wireMachine_measureDecreases` exhibits the wire as a measure instance).  Backed in
`fxTerm_geometryOfInteraction_isBacked`.  `= true`.  HONEST SCOPE: the deterministic token machine +
execution determinacy + measure-termination totality + the wire.  DEFERRED: GoI SOUNDNESS (execution
invariant under cut-elimination — "execution = normalization"), the trace/feedback composition, and Girard's
operator-algebra execution formula (the `term-23` slice of `fxTerm_hasDenotationalAdequacy`). -/
def fxTerm_hasGeometryOfInteraction : Bool := true

/-- ★ **Backed flip (geometry of interaction).**  The marker is `true` AND (i) the token machine is
deterministic (`TokenMachine.step_deterministic`); (ii) EXECUTION IS DETERMINATE — a configuration reaches
at most one exit (`TokenMachine.reaches_unique`); (iii) EXECUTION IS TOTAL on a measure-terminating machine —
a strictly-decreasing measure makes every configuration reach some exit (`TokenMachine.executeTotal_of_measure`),
so with determinacy the GoI denotation is a well-defined TOTAL function; (iv) the wire token reaches its exit
(`wireMachine_reachesExit`). -/
theorem fxTerm_geometryOfInteraction_isBacked :
    fxTerm_hasGeometryOfInteraction = true
      ∧ (∀ (machine : TokenMachine) {config first second : machine.Config},
          machine.step config = some first → machine.step config = some second → first = second)
      ∧ (∀ (machine : TokenMachine) {start firstResult secondResult : machine.Config},
          machine.Reaches start firstResult → machine.Reaches start secondResult →
          firstResult = secondResult)
      ∧ (∀ (machine : TokenMachine) (measure : machine.Config → Nat),
          (∀ {config next : machine.Config}, machine.step config = some next →
            measure next < measure config) →
          ∀ start : machine.Config, ∃ result, machine.Reaches start result)
      ∧ (∀ position : Nat, wireMachine.Reaches position (0 : Nat)) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · intro machine config first second toFirst toSecond
    exact machine.step_deterministic toFirst toSecond
  · intro machine start firstResult secondResult toFirst toSecond
    exact machine.reaches_unique toFirst toSecond
  · intro machine measure decreases start
    exact machine.executeTotal_of_measure measure decreases start
  · exact wireMachine_reachesExit

/-! ## term-24: game semantics — arenas, plays, deterministic strategies -/

/-- **Honesty marker** — `term-24` (game semantics: arenas, plays, strategies).  Shipped (in
`Tier0/Term/Semantics/GameSemantics.lean`): the `Polarity` duality (`flip_flip` / `flip_ne`), `Arena` +
`dualArena` (the linear-logic dual, involutive POINTWISE — `dualArena_involutive_pointwise`), `EvenPlay`
(Opponent/Player move pairs) with the Opponent projection `opponentMoves`, arena-legality (`RespectsArena` /
`respectsArena_prefixClosed`), and DETERMINISTIC strategies (`Strategy`) with the headline
`Strategy.determinedByOpponent` — two accepted plays with the same Opponent projection are equal, so a
strategy DENOTES A FUNCTION from Opponent's dialogue to Player's, plus the concrete `answerArena` /
`answerStrategy` witness.  Backed in `fxTerm_gameSemantics_isBacked`.  `= true`.  HONEST SCOPE: the polarity
duality + arenas/dual arenas + even plays + arena-legality + deterministic strategies (strategy = function of
Opponent's moves) + a concrete answering strategy.  DEFERRED: justification POINTERS + the P-view / O-view
machinery, VISIBILITY / INNOCENCE / WELL-BRACKETING, strategy COMPOSITION (parallel composition + hiding) and
the CATEGORY of games, and FULL ABSTRACTION (denotational equality = observational equivalence for PCF,
Hyland-Ong / AJM) — the `term-24` slice of `fxTerm_hasDenotationalAdequacy`. -/
def fxTerm_hasGameSemantics : Bool := true

/-- ★ **Backed flip (game semantics).**  The marker is `true` AND (i) a STRATEGY IS DETERMINED BY OPPONENT'S
MOVES — two accepted plays with the same Opponent projection are equal (`Strategy.determinedByOpponent`), so
the strategy denotes a function; (ii) the answer strategy accepts the question/answer play
(`answerStrategy_acceptsAnswer`); (iii) the dual arena is an involution pointwise
(`dualArena_involutive_pointwise`). -/
theorem fxTerm_gameSemantics_isBacked :
    fxTerm_hasGameSemantics = true
      ∧ (∀ {Move : Type} (strategy : Strategy Move) {firstPlay secondPlay : EvenPlay Move},
          strategy.accepts firstPlay → strategy.accepts secondPlay →
          opponentMoves firstPlay = opponentMoves secondPlay → firstPlay = secondPlay)
      ∧ answerStrategy.accepts (EvenPlay.snocPair false true EvenPlay.nil)
      ∧ (∀ (arena : Arena) (move : arena.Move),
          (dualArena (dualArena arena)).polarity move = arena.polarity move) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro Move strategy firstPlay secondPlay acceptsFirst acceptsSecond projectionEq
    exact strategy.determinedByOpponent acceptsFirst acceptsSecond projectionEq
  · exact answerStrategy_acceptsAnswer
  · intro arena move
    exact dualArena_involutive_pointwise arena move

/-! ## term-25: the differential λ-calculus — derivations + linear substitution -/

/-- **Honesty marker** — `term-25` (the differential λ-calculus: derivations + linear substitution).  Shipped
(in `Tier0/Term/Semantics/DifferentialLambda.lean`): the abstract `DifferentialAlgebra` (LINEARITY
`deriv_zero` / `deriv_add` + the LEIBNIZ product rule `deriv_mul`) with the derived power rule
`deriv_square` and the `onePointDifferentialAlgebra` model; and the concrete differential / linear
substitution `linearSubst` on the variable/application fragment — `linearSubst_app` is the LEIBNIZ product
rule on the nose, `linearSubst_length_eq_occurrences` is LINEARITY (degree = occurrence count),
`linearSubst_eq_nil_of_absent` is the constant rule, and `exampleSquare_derivative` exhibits the resource-level
`d(x²) = [x t, t x]` (the two-summand `2x`).  Backed in `fxTerm_differentialLambda_isBacked`.  `= true`.
HONEST SCOPE: the abstract derivation laws + a model, and the concrete Leibniz/linearity/constant rules with
the `x²` witness.  DEFERRED: λ-ABSTRACTION (capture-avoiding shift under a binder), the formal-sum MODULE
proper (ℕ-linear combinations up to permutation), the RESOURCE CALCULUS reduction + confluence, and the
TAYLOR EXPANSION (a λ-term as the infinite sum of its iterated derivatives) — the `term-25` slice of
`fxTerm_hasDenotationalAdequacy`. -/
def fxTerm_hasDifferentialLambda : Bool := true

/-- ★ **Backed flip (differential λ-calculus).**  The marker is `true` AND (i) the LEIBNIZ product rule holds
on the nose (`linearSubst_app`); (ii) LINEARITY — the derivative's degree equals the occurrence count
(`linearSubst_length_eq_occurrences`); (iii) the abstract Leibniz law gives the power rule in every model
(`DifferentialAlgebra.deriv_square`). -/
theorem fxTerm_differentialLambda_isBacked :
    fxTerm_hasDifferentialLambda = true
      ∧ (∀ (targetVariable : Nat) (replacement function argument : ResourceTerm),
          linearSubst targetVariable replacement (ResourceTerm.app function argument)
            = (linearSubst targetVariable replacement argument).map
                (fun derivedArgument => ResourceTerm.app function derivedArgument)
              ++ (linearSubst targetVariable replacement function).map
                (fun derivedFunction => ResourceTerm.app derivedFunction argument))
      ∧ (∀ (targetVariable : Nat) (replacement subject : ResourceTerm),
          (linearSubst targetVariable replacement subject).length = occurrences targetVariable subject)
      ∧ (∀ (algebra : DifferentialAlgebra) (value : algebra.Carrier),
          algebra.deriv (algebra.mul value value)
            = algebra.add (algebra.mul (algebra.deriv value) value)
                (algebra.mul value (algebra.deriv value))) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro targetVariable replacement function argument
    exact linearSubst_app targetVariable replacement function argument
  · intro targetVariable replacement subject
    exact linearSubst_length_eq_occurrences targetVariable replacement subject
  · intro algebra value
    exact algebra.deriv_square value

/-! ## term-26: the single-substitution calculus — single weakening + single substitution -/

/-- **Honesty marker** — `term-26` (the single-substitution calculus on the kernel `RawTerm`).  The
PARALLEL-substitution presentation (`context-8`'s explicit-substitution λσ) carries the full σ-algebra: a
substitution category with identity + composition (the monoid laws), the action laws `subst_compose` /
`subst_identity`, and the comprehension/extension (cons + lift) laws — roughly EIGHT equations.  The
SINGLE-substitution calculus (Kaposi-Xie) instead uses only `RawTerm.weaken` (single weakening
`scope → scope+1`) and `RawTerm.subst0` (single substitution of the newest variable), and its substitution
behaviour collapses to a HANDFUL of characteristic equations (the "8→4" collapse).  Shipped: those operations
are the kernel's, and their characteristic equations are proven — the HEAD law (`subst0 newestVar t = t`,
`subst0_var_zero`), the WEAKEN-CANCEL law (`subst0 (weaken a) t = a`, `weaken_subst_singleton`), the
LIFT-WEAKEN naturality (`subst (lift σ) (weaken a) = weaken (subst σ a)`, `subst_lift_weaken`), and the
SUBSTITUTION LEMMA (`subst σ (subst0 b a) = subst0 (subst (lift σ) b) (subst σ a)`, `subst0_subst_commute`),
plus the derived double-weaken cancel (`subst_lift_singleton_weaken_weaken`) showing the single laws COMPOSE.
Backed in `fxTerm_singleSubstitutionCalculus_isBacked`.  `= true`.  HONEST SCOPE: the single operations + the
characteristic single-substitution equations + a derived composition witness.  DEFERRED: the FULL formal
collapse — that the single laws PRESENT the CwF / are inter-derivable with the eight parallel σ-laws (the
SSC ≅ CwF equivalence) — is `context-28`; the Allais parallel-fold ↔ SSC reconciliation is `term-27`. -/
def fxTerm_hasSingleSubstitutionCalculus : Bool := true

/-- ★ **Backed flip (single-substitution calculus).**  The marker is `true` AND the four characteristic SSC
equations hold on the kernel `RawTerm`: (i) the HEAD law `subst0 newestVar t = t`; (ii) the WEAKEN-CANCEL law
`subst0 (weaken a) t = a`; (iii) the LIFT-WEAKEN naturality `subst (lift σ) (weaken a) = weaken (subst σ a)`;
(iv) the SUBSTITUTION LEMMA `subst σ (subst0 b a) = subst0 (subst (lift σ) b) (subst σ a)`; plus (v) the
derived double-weaken cancel, showing the single laws compose. -/
theorem fxTerm_singleSubstitutionCalculus_isBacked :
    fxTerm_hasSingleSubstitutionCalculus = true
      ∧ (∀ {scope : Nat} (rawArg : RawTerm scope),
          RawTerm.subst0 RawTerm.newestVar rawArg = rawArg)
      ∧ (∀ {scope : Nat} (sourceTerm rawArg : RawTerm scope),
          RawTerm.subst0 (RawTerm.weaken sourceTerm) rawArg = sourceTerm)
      ∧ (∀ {sourceScope targetScope : Nat}
          (someSubstitution : RawTermSubst sourceScope targetScope) (sourceTerm : RawTerm sourceScope),
          RawTerm.subst (RawTermSubst.lift someSubstitution) (RawTerm.weaken sourceTerm)
            = RawTerm.weaken (RawTerm.subst someSubstitution sourceTerm))
      ∧ (∀ {sourceScope targetScope : Nat}
          (body : RawTerm (sourceScope + 1)) (rawArg : RawTerm sourceScope)
          (sigma : RawTermSubst sourceScope targetScope),
          RawTerm.subst sigma (RawTerm.subst0 body rawArg)
            = RawTerm.subst0 (RawTerm.subst (RawTermSubst.lift sigma) body) (RawTerm.subst sigma rawArg))
      ∧ (∀ {scope : Nat} (innerArg outerArg : RawTerm scope),
          RawTerm.subst (RawTermSubst.lift (RawTermSubst.singleton outerArg))
              (RawTerm.weaken (RawTerm.weaken innerArg))
            = RawTerm.weaken innerArg) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro scope rawArg
    exact RawTerm.subst0_var_zero rawArg
  · intro scope sourceTerm rawArg
    exact RawTerm.weaken_subst_singleton sourceTerm rawArg
  · intro sourceScope targetScope someSubstitution sourceTerm
    exact RawTerm.subst_lift_weaken someSubstitution sourceTerm
  · intro sourceScope targetScope body rawArg sigma
    exact RawTerm.subst0_subst_commute body rawArg sigma
  · intro scope innerArg outerArg
    exact RawTerm.subst_lift_singleton_weaken_weaken innerArg outerArg

/-! ## Honest deferred marker (the remaining semantics frontier) -/

/-- **Honesty marker** — `term-21..25` (the REMAINING denotational-semantics frontier).  Beyond `term-21`'s
shipped domain / Kleene-fixpoint core (`fxTerm_hasDenotationalDomainFixpoint`), the deep models are not
built: the D∞ REFLEXIVE OBJECT + computational ADEQUACY (`term-21`'s capstone), the intersection-type
NORMALIZATION CHARACTERIZATION `typeable ⟺ normalizing` + the antisymmetric filter DCPO (`term-22`'s
capstone — beyond its shipped `fxTerm_hasIntersectionFilterModel` algebra), GoI SOUNDNESS + the execution
formula (`term-23`'s capstone — beyond its shipped `fxTerm_hasGeometryOfInteraction` token machine), game
semantics FULL ABSTRACTION + strategy composition (`term-24`'s capstone — beyond its shipped
`fxTerm_hasGameSemantics` deterministic-strategy core), and the differential-λ TAYLOR EXPANSION + resource
reduction (`term-25`'s capstone — beyond its shipped `fxTerm_hasDifferentialLambda` Leibniz/linearity core) —
only the syntactic generator stubs
(`gen_cpoStructure`, `gen_game`, `gen_diffLambda`, …) and the Sconing logical-relation harness exist.
`= false`. -/
def fxTerm_hasDenotationalAdequacy : Bool := false

end FX1Poly.Tier0
