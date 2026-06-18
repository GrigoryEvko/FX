import FX1Poly.Core.Rewriting.Confluence.RawConfluence
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationUnion
import FX1Poly.Core.Rewriting.Confluence.ModularConfluence
import FX1Poly.Tier0.Term.Subst.RawTermSubstBetaBridge
import FX1Poly.Tier0.Term.Action.FoldUniqueness
import FX1Poly.Tier0.Term.Action.InitialAlgebra
import FX1Poly.Tier0.Term.Rewrite.Dim1FreePreorder
import FX1Poly.Tier0.Term.Codata.TerminalCoalgebra
import FX1Poly.Tier0.Term.Rewrite.SquierCoherence
import FX1Poly.Tier0.Term.Rewrite.PolygraphicResolution

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
    arbitrary carrier — `cata` + `IsCarrierHomomorphism.unique`; arbitrary-binding-SIGNATURE lift = SIG-5)
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
  * `term-7`  Knuth-Bendix completion: · (`fxTerm_hasKnuthBendixCompletion`)
  * `term-8..16` advanced rewriting (decreasing diagrams, Lévy optimality, Fiore Σ-monoid,
    HO unification, standardization, Böhm trees, mixed μ/ν, copattern coverage, CR-mod-AC)
  * `term-17` free strict ω-category + Gray tensor (mirrors `mode-5`)
  * `term-18` marked/complicial structure (mirrors `mode-7`)
  * `term-19` exact SN boundary — modular/persistent SN: ◆ (criterion as `term-6`)
  * `term-20` CAPSTONE — decidable Conv as a function of convergence: ◆
    (`fxTerm_hasNormalizerConvDecision`)
  * `term-21..25` denotational semantics frontier (D∞ / intersection / GoI / games / differential-λ): ·
    (`fxTerm_hasDenotationalAdequacy`)
  * `term-26` SSC single-weaken/subst + 8→4 collapse: ○ (atomic ops in `Rename`/`Subst`; equations open)
  * `term-27` Allais parallel-fold ↔ SSC reconciliation: ◆ (the fold engine is shipped)
  * `term-beta` re-home the `context-9` `×term` β-bridge corollary (with `term-26`)

## What this file ships (each backed, zero-axiom)

The three metatheoretic properties the raw term layer genuinely has — confluence (unconditional),
decidable conversion as a function of convergence, and the modular SN criterion — flipped `true`
and each conjoined with the shipped theorem that proves it.  The remaining rungs carry honest
`false` markers documenting precisely what is shipped-as-substrate versus open.

## Zero-axiom verification

Ten `Bool` markers `:= true`, two `:= false`, and ten `_isBacked` conjunctions each closed by
`rfl` and a direct application (`StepStar.rawConfluence`, `Normalizer.decidableConv`, `accUnion`,
`confluentOfCommutingConfluent`,
`RawTerm.subst_cons_eq_singleton_after_lift`, `IsCarrierHomomorphism.unique`,
`ReflTransClosure.mediate_single` + `mediate_unique` + `reflTransClosure_fxIotaBundle_iff_stepStar`,
`StreamCoalgebra.ana_head` + `ana_unique` + `FinalStream.bisim_observe`,
`RewriteHomotopy.toModel` + `SquierDiamond.confluent`,
`F2ChainComplex.boundary_isCycle` + the `trivialComplex`/`zeroDifferentialComplex` witnesses +
`monoidNComplex_homologyNotVanishing` + `trivialMonoidComplex_homologyVanishes`).
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
`FoldUniqueness.lean`, not this.)  Backed in `fxTerm_initialAlgebraUniqueness_isBacked`.  `= true`. -/
def fxTerm_hasInitialAlgebraUniqueness : Bool := true

/-- ★ **Backed flip (initial-algebra uniqueness).**  The marker is `true` AND any homomorphism out of
`RawTerm` into a model agrees with the catamorphism (`IsCarrierHomomorphism.unique`) — `cata` is the unique
homomorphism, so `RawTerm` is the initial algebra of its signature. -/
theorem fxTerm_initialAlgebraUniqueness_isBacked :
    fxTerm_hasInitialAlgebraUniqueness = true
      ∧ (∀ {C : Nat → Type} {algebra : CarrierAlgebra C} {scope : Nat}
          (homomorphism : IsCarrierHomomorphism algebra) (term : RawTerm scope),
          homomorphism.map term = cata algebra term) :=
  ⟨rfl, fun homomorphism term => homomorphism.unique term⟩

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

/-! ## Honest deferred markers (the structural / semantics frontier) -/

/-- **Honesty marker** — `term-7` (Knuth-Bendix).  A completion procedure (orient / deduce /
superpose) for the term system is not built — the system is designed orthogonal, so completion was
never needed; the critical-pair / Newman / RPO oracles it would consume do exist.  `= false`. -/
def fxTerm_hasKnuthBendixCompletion : Bool := false

/-- **Honesty marker** — `term-21..25` (the denotational-semantics frontier).  Denotational /
intersection-type / geometry-of-interaction / game / differential-λ models with adequacy or
full-abstraction are not built — only the syntactic generator stubs (`gen_cpoStructure`, `gen_game`,
`gen_diffLambda`, …) and the Sconing logical-relation harness exist.  `= false`. -/
def fxTerm_hasDenotationalAdequacy : Bool := false

end FX1Poly.Tier0
