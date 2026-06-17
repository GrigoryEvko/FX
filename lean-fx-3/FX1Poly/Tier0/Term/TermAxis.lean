import FX1Poly.Core.Rewriting.Confluence.RawConfluence
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationUnion
import FX1Poly.Tier0.Term.Subst.RawTermSubstBetaBridge

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

  * `term-1`  LEFT  — constructors as initial algebra (SOAS): ○ (the generic fold is shipped in
    `Action/Fold.lean`; fold-uniqueness for `RawTerm` is the open leg — `fxTerm_hasInitialAlgebraUniqueness`)
  * `term-2`  MIDDLE — dim-1 rewriting (`StepOver` as 1-cells): ◆ (`Core/Rewriting/RuleTables/StepOver/*`;
    confluence surfaced here — `fxTerm_hasRawConfluence`)
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

Four `Bool` markers `:= true`, five `:= false`, and four `_isBacked` conjunctions each closed by
`rfl` and a direct application of a `Core` theorem (`StepStar.rawConfluence`,
`Normalizer.decidableConv`, `accUnion`, `RawTerm.subst_cons_eq_singleton_after_lift`).  No `axiom`,
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

/-! ## Honest deferred markers (the structural / coinductive / semantics frontier) -/

/-- **Honesty marker** — `term-1` (SOAS-initiality).  The generic fold OPERATION over the generator
algebra is shipped (`Tier0/Term/Action/Fold.lean` + `Generator/GenAlgebra.lean`), but the
fold-UNIQUENESS / initial-algebra universal property for `RawTerm` is not yet packaged (only the
dim-1 word monoid's `foldOut_unique` and the context-side `Initiality` exist).  `= false`. -/
def fxTerm_hasInitialAlgebraUniqueness : Bool := false

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
