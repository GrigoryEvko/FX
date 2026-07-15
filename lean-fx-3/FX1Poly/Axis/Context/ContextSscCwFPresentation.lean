import FX1Poly.Axis.Context.SubstitutionFree
import FX1Poly.Axis.Context.Instances.Subst.FxBaseSubstColimits

/-! # context-28 — the single-substitution calculus PRESENTS the CwF (`SSC ≅ CwF`, strict residue)

`context-28` (★, on the fib-* arc, context structure) asks: does the single-substitution-calculus (SSC)
algebra — `term-26`'s single weakening `p` and single substitution `⟨a⟩` over the kernel `RawTerm`
(Kaposi–Xie, arXiv:2510.12303) — PRESENT the base substitution category / CwF structure
(`fxBaseSubstCategory`)?  That is: do the explicit single-substitution operations GENERATE the
substitution category, and do the CwF laws (substitution composition, the comprehension/projection
equations) hold STRICTLY at the term-algebra level?

This rung is the PRESENTATION ASSEMBLY: it gathers the CwF structure already earned across the context
arc (`context-1` the comprehension v/p/η laws + `cons_compose` Σ-introduction naturality; `context-7`
the strict lift functoriality; `context-9` the substitution-free factorization) and the SSC algebra of
`term-26`/`term-27`, and certifies — as ONE citable object — that the single-substitution operations
constitute a STRICT presentation of the CwF `fxBaseSubstCategory`.

## What lands here (all zero-axiom)

  * **`sscSubstitutionCategory`** — the named carrier: the substitution category `fxBaseSubstCategory`
    viewed as the object the SSC presentation generates (objects = scopes/contexts, morphisms `source ⟶
    target` = SSC substitution vectors `SubstVec target source`).  The morphism type IS the SSC
    substitution (`sscSubstitutionCategory_morphism_eq_substVec`, `rfl`).
  * **`SubstVec.IsGeneratedBySsc`** + **`SubstVec.isGeneratedBySsc_complete`** — ★ the GENUINELY-NEW
    content: the ITERATED generation/spanning theorem.  Every substitution `vec : SubstVec target
    source` is built from the comprehension generators — the empty substitution (the base, the unique
    morphism out of the initial context `0`) and iterated context extension (`cons`).  This is the
    "the SSC operations GENERATE every morphism" half of "presents", proved by structural recursion on
    the scope (product eta at each successor).  It complements `context-9`'s ONE-LEVEL factorization
    `factor_lift_singleton` (which factors a single extended-context substitution through `lift` + a
    single substitution) with the full ITERATED spanning down to the initial object.
  * **`SscCwFPresentation`** + **`sscPresentsCwF`** — ★ the packaged STRICT CwF-presentation datum:
    the category/functor laws (the `term-26` substitution-action collapse `subst id = id` /
    `subst (σ∘τ) = subst τ ∘ subst σ`, plus the three category laws), the CwF comprehension structure
    (projection `p`-law, variable `v`-law, Σ-introduction `cons_compose` naturality, the η /
    surjective-pairing law, and the comprehension universal property), the comprehension-functor
    (`lift`) functoriality + the display-map Beck–Chevalley naturality, and the SSC single-substitution
    generators (the display section `p ∘ ⟨a⟩ = id`, the β bridge `subst ⟨a⟩ = subst0`, extension from
    `lift` + single substitution, the one-level factorization, and the iterated spanning).  Every field
    is filled by a shipped zero-axiom lemma or the new spanning theorem — a genuine certificate, not a
    marker bundle.

## What is deferred (the honest wall)

  * The FULL up-to-iso BIEQUIVALENCE — that this CwF is biequivalent to the natural model (Awodey), the
    representable map category (Uemura), the category with attributes (Cartmell), and the contextual
    category / C-system — is `context-6`'s `×type+term` core (`fib-8`): it packages the TYPE/TERM
    presheaves fibred over the base, and the comparison functors' coherences need a
    substitution-coherence QUOTIENT (`Quot.sound`) and up-to-iso natural-transformation naturality
    (`funext`), both off-limits zero-axiom.  Shipped here is the STRICT term-algebra residue: the laws
    hold on the nose (`Eq`), so `fxContextSscCwF_hasStrictSubstitutionCategory = true` and
    `fxContextSscCwF_hasFullBiequivalence = false`.
  * This is the SELF-CONTAINED Axis presentation residue, NOT a Core `StepOverTable` iota row
    (`fxContextSscCwF_isOverCoreIotaTable = false`).

Imports only its context-arc siblings (`SubstitutionFree` — `context-9`, transitively the comprehension
laws / strictification / singleton bricks — and `FxBaseSubstColimits` — the initial object).  A Axis
design-lock must not import up into `Core/` / `Typed/`.  Zero external dependencies — raw Lean 4 + Init
only.

Reference: Kaposi & Xie, "A Syntax for Single-Substitution Calculi" (arXiv:2510.12303); Castellan–Clairambault–Dybjer,
"Categories with Families: Unityped, Simply Typed, and Dependently Typed"; Ahrens–Lumsdaine–North and Newstead
(the CwF / natural-model / RMC / CwA / C-system biequivalence, `context-6`); the `term-26`/`term-27` SSC
algebra (`Axis/Term/TermAxis.lean`); the comprehension laws (`context-1` `ComprehensionLaws.lean`), the
strictification (`context-7` `Strictification.lean`), and the substitution-free completeness (`context-9`
`SubstitutionFree.lean`).
-/

namespace FX1Poly.Axis
open FX1Poly.Polygraph

open FX1Poly.Core

/-! ## The named carrier: the SSC substitution category -/

/-- The **SSC substitution category** — the substitution category `fxBaseSubstCategory` viewed as the
object the single-substitution-calculus presentation generates: objects are scopes/contexts (`Nat`),
morphisms `source ⟶ target` are the SSC substitution vectors `SubstVec target source`.  Defined as the
shipped `fxBaseSubstCategory` (no fork — the presentation is OF that category), named to surface the
SSC reading. -/
def sscSubstitutionCategory : RawCategory.{0, 0} := fxBaseSubstCategory

/-- The SSC substitution category's objects are scopes. -/
theorem sscSubstitutionCategory_object_eq_nat : sscSubstitutionCategory.Object = Nat := rfl

/-- The SSC substitution category's morphisms ARE the SSC substitution vectors — the morphisms carry
genuine `RawTerm` content (the single-substitution data), not mere variable reindexings. -/
theorem sscSubstitutionCategory_morphism_eq_substVec (sourceScope targetScope : Nat) :
    sscSubstitutionCategory.Morphism sourceScope targetScope = SubstVec targetScope sourceScope := rfl

/-! ## The iterated generation theorem: the SSC operations span every morphism -/

/-- **The comprehension generators span a substitution** — the inductive certificate that a
substitution is built from the SSC comprehension operations: the EMPTY substitution (the base: any
morphism out of the initial context `0`, i.e. any `SubstVec target 0 = PUnit`) and iterated context
EXTENSION (`SubstVec.cons`, prepending one `RawTerm` head).  Membership witnesses the morphism is a
tower of comprehension extensions over the empty substitution — the structural content of "the SSC
operations generate the substitution category". -/
inductive SubstVec.IsGeneratedBySsc : {target source : Nat} → SubstVec target source → Prop where
  /-- Base: the empty substitution (out of the initial context `0`) is generated. -/
  | empty {target : Nat} (emptyVec : SubstVec target 0) : SubstVec.IsGeneratedBySsc emptyVec
  /-- Step: extending a generated substitution by one head term is generated (context extension). -/
  | extend {target source : Nat} (headTerm : RawTerm target) {tailVec : SubstVec target source} :
      SubstVec.IsGeneratedBySsc tailVec →
      SubstVec.IsGeneratedBySsc (SubstVec.cons headTerm tailVec)

/-- A successor vector IS the comprehension extension of its head and tail (`cons` of the product
projections) — product eta on `SubstVec target (source + 1) = RawTerm target × SubstVec target source`.
The reconstruction step the spanning recursion runs. -/
theorem SubstVec.cons_head_tail {target source : Nat} (vec : SubstVec target (source + 1)) :
    SubstVec.cons vec.1 vec.2 = vec := rfl

/-- ★ **Every substitution is generated by the SSC comprehension operations** — the ITERATED spanning /
completeness.  By structural recursion on the scope: the empty scope is the base case (the unique
morphism out of the initial context), and a successor scope's vector is the `cons` extension of its
head over the spanning of its tail (product eta).  This is the GENERATION half of "the SSC algebra
PRESENTS the CwF": the comprehension generators reach every morphism of `fxBaseSubstCategory`.  The
genuinely-new content of this rung (zero-axiom — structural recursion on `Nat`, product eta, no
`funext`/`Quot.sound`). -/
theorem SubstVec.isGeneratedBySsc_complete {target : Nat} :
    {source : Nat} → (vec : SubstVec target source) → SubstVec.IsGeneratedBySsc vec
  | 0, emptyVec => SubstVec.IsGeneratedBySsc.empty emptyVec
  | _source + 1, vec =>
      SubstVec.IsGeneratedBySsc.extend vec.1 (SubstVec.isGeneratedBySsc_complete vec.2)

/-! ## The packaged strict CwF-presentation datum -/

/-- **The SSC-presents-CwF datum** of the FX substitution base, gathered as one citable object: the
single-substitution-calculus operations constitute a STRICT presentation of the CwF
`fxBaseSubstCategory`.  Each field is a CwF / presentation law holding STRICTLY (`Eq`) at the
term-algebra level — the category/functor laws (the `term-26`/`term-27` substitution-action collapse),
the comprehension (context-extension) structure, the comprehension-functor functoriality and display-map
naturality, and the SSC single-substitution generators with the iterated spanning.  The up-to-iso
biequivalence to the other model notions (`×type+term`, `context-6`/`fib-8`) is the honest deferral. -/
structure SscCwFPresentation where
  /-- Left identity (category law). -/
  identityLeft : ∀ {sourceScope targetScope : Nat} (vec : SubstVec targetScope sourceScope),
    (SubstVec.identity sourceScope).compose vec = vec
  /-- Right identity (category law). -/
  identityRight : ∀ {sourceScope targetScope : Nat} (vec : SubstVec targetScope sourceScope),
    vec.compose (SubstVec.identity targetScope) = vec
  /-- Associativity of substitution composition (category law). -/
  composeAssoc : ∀ {scopeA scopeB scopeC scopeD : Nat}
    (firstVec : SubstVec scopeB scopeA) (secondVec : SubstVec scopeC scopeB)
    (thirdVec : SubstVec scopeD scopeC),
    (firstVec.compose secondVec).compose thirdVec = firstVec.compose (secondVec.compose thirdVec)
  /-- ★ The substitution-action IDENTITY law (the `term-26` collapse): `subst id = id`. -/
  substActionIdentity : ∀ {scope : Nat} (term : RawTerm scope),
    RawTerm.subst (SubstVec.identity scope).toRawTermSubst term = term
  /-- ★ The substitution-action FUSION law (the `term-26`/`term-27` collapse):
  `subst (σ ∘ τ) = subst τ ∘ subst σ`. -/
  substActionCompose : ∀ {scopeA scopeB scopeC : Nat}
    (firstVec : SubstVec scopeB scopeA) (secondVec : SubstVec scopeC scopeB) (term : RawTerm scopeA),
    RawTerm.subst (firstVec.compose secondVec).toRawTermSubst term =
      RawTerm.subst secondVec.toRawTermSubst (RawTerm.subst firstVec.toRawTermSubst term)
  /-- The comprehension `p`-law (display projection cancels extension): `p ∘ ⟨σ, a⟩ = σ`. -/
  projectionLaw : ∀ {target source : Nat} (headTerm : RawTerm target)
    (tailVec : SubstVec target source),
    (SubstVec.weakening source).compose (SubstVec.cons headTerm tailVec) = tailVec
  /-- The comprehension `v`-law (the variable `q` recovers the head): `q[⟨σ, a⟩] = a`. -/
  variableLaw : ∀ {target source : Nat} (headTerm : RawTerm target)
    (tailVec : SubstVec target source) (isLt : 0 < source + 1),
    (SubstVec.cons headTerm tailVec).lookup ⟨0, isLt⟩ = headTerm
  /-- ★ The Σ-introduction (extension) naturality: `⟨σ, a⟩ ∘ δ = ⟨σ ∘ δ, a[δ]⟩`. -/
  extensionNaturality : ∀ {sourceScope midScope targetScope : Nat} (headTerm : RawTerm midScope)
    (tailVec : SubstVec midScope sourceScope) (sigma : SubstVec targetScope midScope),
    (SubstVec.cons headTerm tailVec).compose sigma =
      SubstVec.cons (RawTerm.subst sigma.toRawTermSubst headTerm) (tailVec.compose sigma)
  /-- ★ The comprehension η / surjective-pairing law: `id_{Γ.A} = ⟨q, p⟩`. -/
  comprehensionEta : ∀ (scope : Nat),
    SubstVec.identity (scope + 1) =
      SubstVec.cons (SubstVec.varCell ⟨0, Nat.succ_pos scope⟩) (SubstVec.weakening scope)
  /-- The comprehension UNIVERSAL PROPERTY: the extension is the unique morphism with the given
  projection and zeroth lookup. -/
  comprehensionUnique : ∀ {target source : Nat} (headTerm : RawTerm target)
    (tailVec : SubstVec target source) (candidate : SubstVec target (source + 1)),
    (SubstVec.weakening source).compose candidate = tailVec →
    candidate.lookup ⟨0, Nat.succ_pos source⟩ = headTerm →
    candidate = SubstVec.cons headTerm tailVec
  /-- ★ The comprehension functor preserves identities ON THE NOSE: `id⁺ = id`. -/
  liftPreservesIdentity : ∀ (scope : Nat),
    SubstVec.lift (SubstVec.identity scope) = SubstVec.identity (scope + 1)
  /-- ★ The comprehension functor preserves composition ON THE NOSE: `(σ ∘ τ)⁺ = σ⁺ ∘ τ⁺`. -/
  liftPreservesComposition : ∀ {sourceScope midScope targetScope : Nat}
    (firstVec : SubstVec midScope sourceScope) (secondVec : SubstVec targetScope midScope),
    SubstVec.lift (firstVec.compose secondVec) =
      (SubstVec.lift firstVec).compose (SubstVec.lift secondVec)
  /-- The display-map Beck–Chevalley naturality: `p ∘ σ⁺ = σ ∘ p`. -/
  displayMapNaturality : ∀ {sourceScope targetScope : Nat}
    (sigma : SubstVec targetScope sourceScope),
    (SubstVec.weakening sourceScope).compose sigma.lift =
      sigma.compose (SubstVec.weakening targetScope)
  /-- ★ The single substitution `⟨a⟩` is a SECTION of the display map: `p ∘ ⟨a⟩ = id`. -/
  singletonSection : ∀ {scope : Nat} (rawArg : RawTerm scope),
    (SubstVec.weakening scope).compose (SubstVec.singleton rawArg) = SubstVec.identity scope
  /-- ★ The single substitution `⟨a⟩` ACTS as the kernel β-reduct `subst0`: `body[⟨a⟩] = body[a]`. -/
  singletonActsAsSubstZero : ∀ {scope : Nat} (body : RawTerm (scope + 1)) (rawArg : RawTerm scope),
    RawTerm.subst (SubstVec.singleton rawArg).toRawTermSubst body = RawTerm.subst0 body rawArg
  /-- Comprehension extension is admissible from the single ops: `⟨σ, a⟩ = σ⁺ ∘ ⟨a⟩`. -/
  extensionFromSingleAndLift : ∀ {target source : Nat} (headTerm : RawTerm target)
    (tailVec : SubstVec target source),
    SubstVec.cons headTerm tailVec = tailVec.lift.compose (SubstVec.singleton headTerm)
  /-- ★ One-level FACTORIZATION (`context-9`): every extended-context substitution factors through
  `lift` and a single substitution — `vec = ((p ∘ vec)⁺) ∘ ⟨vec 0⟩`. -/
  oneStepFactorization : ∀ {target source : Nat} (vec : SubstVec target (source + 1)),
    vec = ((SubstVec.weakening source).compose vec).lift.compose
            (SubstVec.singleton (vec.lookup ⟨0, Nat.succ_pos source⟩))
  /-- ★ ITERATED GENERATION: every substitution is spanned by the SSC comprehension operations down to
  the empty substitution — the new completeness of this rung. -/
  everyMorphismGeneratedBySsc : ∀ {target source : Nat} (vec : SubstVec target source),
    SubstVec.IsGeneratedBySsc vec

/-- ★ **The single-substitution calculus PRESENTS the CwF `fxBaseSubstCategory`** — the zero-axiom
witness, wiring every CwF / presentation law to its shipped proof: the category laws
(`identity_compose` / `compose_identity` / `compose_assoc`), the substitution-action collapse
(`identity_subst_apply` / `compose_subst_apply`, the `term-26`/`term-27` content), the comprehension
structure (`weakening_compose_cons` / `cons_lookup_zero` / `cons_compose` / `identity_succ_eq_cons` /
`cons_unique`), the comprehension-functor functoriality (`lift_identity` / `lift_compose` /
`weakening_compose_lift`), and the SSC single-substitution generators (`weakening_compose_singleton` /
`subst_singleton_eq_subst0` / `cons_eq_lift_compose_singleton` / `factor_lift_singleton`) plus the new
iterated spanning (`isGeneratedBySsc_complete`).  The strict term-algebra presentation; the up-to-iso
biequivalence is `context-6`/`fib-8`. -/
def sscPresentsCwF : SscCwFPresentation where
  identityLeft := fun vec => SubstVec.identity_compose vec
  identityRight := fun vec => SubstVec.compose_identity vec
  composeAssoc := fun firstVec secondVec thirdVec =>
    SubstVec.compose_assoc firstVec secondVec thirdVec
  substActionIdentity := fun term => SubstVec.identity_subst_apply term
  substActionCompose := fun firstVec secondVec term =>
    SubstVec.compose_subst_apply firstVec secondVec term
  projectionLaw := fun headTerm tailVec => SubstVec.weakening_compose_cons headTerm tailVec
  variableLaw := fun headTerm tailVec isLt => SubstVec.cons_lookup_zero headTerm tailVec isLt
  extensionNaturality := fun headTerm tailVec sigma => SubstVec.cons_compose headTerm tailVec sigma
  comprehensionEta := fun scope => SubstVec.identity_succ_eq_cons scope
  comprehensionUnique := fun headTerm tailVec candidate projectsToTail zerothIsHead =>
    SubstVec.cons_unique headTerm tailVec candidate projectsToTail zerothIsHead
  liftPreservesIdentity := fun scope => SubstVec.lift_identity scope
  liftPreservesComposition := fun firstVec secondVec => SubstVec.lift_compose firstVec secondVec
  displayMapNaturality := fun sigma => SubstVec.weakening_compose_lift sigma
  singletonSection := fun rawArg => SubstVec.weakening_compose_singleton rawArg
  singletonActsAsSubstZero := fun body rawArg => SubstVec.subst_singleton_eq_subst0 body rawArg
  extensionFromSingleAndLift := fun headTerm tailVec =>
    SubstVec.cons_eq_lift_compose_singleton headTerm tailVec
  oneStepFactorization := fun vec => SubstVec.factor_lift_singleton vec
  everyMorphismGeneratedBySsc := fun vec => SubstVec.isGeneratedBySsc_complete vec

/-! ## Honesty markers -/

/-- **Honesty marker.**  The single-substitution-calculus algebra (`term-26`'s single weakening `p` +
single substitution `⟨a⟩`) PRESENTS the CwF `fxBaseSubstCategory`: the SSC comprehension operations
generate every morphism (`isGeneratedBySsc_complete`), and all CwF / presentation laws hold strictly
(`sscPresentsCwF`).  `= true`. -/
def fxContextSscCwF_hasSscCwFPresentation : Bool := true

/-- **Honesty marker.**  The substitution category is a STRICT CwF: every category / comprehension /
functor law holds ON THE NOSE (`Eq`, via `SubstVec.ext` / product eta on the de Bruijn term algebra),
not up to coherent isomorphism — the term-algebra-level presentation.  `= true`. -/
def fxContextSscCwF_hasStrictSubstitutionCategory : Bool := true

/-- **Honesty marker.**  The FULL up-to-iso BIEQUIVALENCE — that this CwF is biequivalent to the
natural model (Awodey), the representable map category (Uemura), the category with attributes
(Cartmell), and the contextual category / C-system — is NOT shipped: it is `context-6`'s `×type+term`
core (`fib-8`), packaging the type/term presheaves with comparison-functor coherences that need a
substitution-coherence quotient (`Quot.sound`) and up-to-iso natural-transformation naturality
(`funext`), both off-limits zero-axiom.  `= false`. -/
def fxContextSscCwF_hasFullBiequivalence : Bool := false

/-- **Honesty marker.**  This is the SELF-CONTAINED Axis presentation residue assembling the shipped
context-arc CwF bricks with the new iterated spanning; it is NOT a Core `StepOverTable` iota-table row.
`= false`. -/
def fxContextSscCwF_isOverCoreIotaTable : Bool := false

/-- ★ **Backed flip.**  The markers are as stated AND the presentation is non-vacuous: every morphism of
the substitution category is SSC-generated (the spanning), the comprehension `p`-law holds, and the
comprehension η-law holds — all surfaced through the `sscPresentsCwF` witness. -/
theorem fxContextSscCwF_isBacked :
    fxContextSscCwF_hasSscCwFPresentation = true
      ∧ fxContextSscCwF_hasStrictSubstitutionCategory = true
      ∧ fxContextSscCwF_hasFullBiequivalence = false
      ∧ (∀ {target source : Nat} (vec : SubstVec target source), SubstVec.IsGeneratedBySsc vec)
      ∧ (∀ {target source : Nat} (headTerm : RawTerm target) (tailVec : SubstVec target source),
          (SubstVec.weakening source).compose (SubstVec.cons headTerm tailVec) = tailVec)
      ∧ (∀ (scope : Nat), SubstVec.identity (scope + 1) =
          SubstVec.cons (SubstVec.varCell ⟨0, Nat.succ_pos scope⟩) (SubstVec.weakening scope)) :=
  ⟨rfl, rfl, rfl,
    sscPresentsCwF.everyMorphismGeneratedBySsc,
    sscPresentsCwF.projectionLaw,
    sscPresentsCwF.comprehensionEta⟩

/-! ## Smoke -/

/-- Smoke: the SSC generation grounds out at the INITIAL context — the empty substitution out of the
initial object `0` (the unique such morphism, `fxBaseSubstInitial`) is generated, so the spanning's base
case is canonical. -/
theorem sscPresentsCwF_emptyIsGenerated_smoke (target : Nat) :
    SubstVec.IsGeneratedBySsc (fxBaseSubstInitial.fromInitial target) :=
  sscPresentsCwF.everyMorphismGeneratedBySsc (fxBaseSubstInitial.fromInitial target)

/-- Smoke: the single substitution `⟨a⟩` is generated by the SSC operations — it is the extension of
the identity (itself spanned) by the argument head. -/
theorem sscPresentsCwF_singletonIsGenerated_smoke {scope : Nat} (rawArg : RawTerm scope) :
    SubstVec.IsGeneratedBySsc (SubstVec.singleton rawArg) :=
  sscPresentsCwF.everyMorphismGeneratedBySsc (SubstVec.singleton rawArg)

/-- Smoke: the presentation's carrier IS the shipped substitution category — the presentation is OF
`fxBaseSubstCategory`, no fork. -/
theorem sscSubstitutionCategory_eq_base : sscSubstitutionCategory = fxBaseSubstCategory := rfl

end FX1Poly.Axis
