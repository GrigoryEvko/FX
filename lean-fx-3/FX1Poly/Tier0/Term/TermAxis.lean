import FX1Poly.Core.Rewriting.Confluence.RawConfluence
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationUnion
import FX1Poly.Tier0.Term.Subst.RawTermSubstBetaBridge
import FX1Poly.Tier0.Term.Action.FoldUniqueness
import FX1Poly.Tier0.Term.Action.InitialAlgebra
import FX1Poly.Tier0.Term.Rewrite.Dim1FreePreorder

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
  * `term-3`  RIGHT — terminal coalgebra + corecursion + bisimulation: · (`fxTerm_hasTerminalCoalgebra`)
  * `term-4`  Squier coherent presentation: ○ (`fxTerm_hasCoherentPresentation`)
  * `term-5`  polygraphic resolution + homology: ○
  * `term-6`  Toyama / modular confluence & SN: ◆ (criterion surfaced — `fxTerm_hasModularStrongNormalizationCriterion`)
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

Six `Bool` markers `:= true`, four `:= false`, and six `_isBacked` conjunctions each closed by
`rfl` and a direct application (`StepStar.rawConfluence`, `Normalizer.decidableConv`, `accUnion`,
`RawTerm.subst_cons_eq_singleton_after_lift`, `IsCarrierHomomorphism.unique`,
`ReflTransClosure.mediate_unique` + `reflTransClosure_fxIotaBundle_iff_stepStar`).  No `axiom`,
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

/-- ★ **Backed flip (dim-1 rewrite preorder).**  The marker is `true` AND (i) every mediating map out
of the free reflexive-transitive closure agrees with `ReflTransClosure.mediate` — the free-preorder
universal property (uniqueness leg) — AND (ii) the `fxIotaBundle` freely-generated relation is exactly
the bespoke `StepStar` substrate. -/
theorem fxTerm_dim1RewritePreorder_isBacked :
    fxTerm_hasDim1RewritePreorder = true
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
  refine ⟨rfl, ?_, ?_⟩
  · intro Carrier rel cocone source goal other chain
    exact ReflTransClosure.mediate_unique cocone other chain
  · intro scope source target
    exact reflTransClosure_fxIotaBundle_iff_stepStar

/-! ## Honest deferred markers (the structural / coinductive / semantics frontier) -/

/-- **Honesty marker** — `term-3` (co-signature).  A terminal-coalgebra / corecursion / bisimulation
layer over the codata generators (`gen_codataUnfold`, `gen_polyNu`, classified `productiveClass`) is
not yet built — only the syntactic tags plus the `mode-15` guarded-recursion substrate exist.
`= false`. -/
def fxTerm_hasTerminalCoalgebra : Bool := false

/-- **Honesty marker** — `term-4` (Squier).  The coherent-presentation / homotopical layer (3-cells
filling critical-pair branchings) is not yet built; the rewriting substrate (orthogonality, critical
pairs, Newman) is shipped but the coherence theorem on top of it is not.  `= false`. -/
def fxTerm_hasCoherentPresentation : Bool := false

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
