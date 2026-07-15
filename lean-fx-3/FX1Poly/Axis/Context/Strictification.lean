import FX1Poly.Axis.Context.ComprehensionLaws
import FX1Poly.Axis.Context.Context

/-! # context-7 — strictification: substitution-as-pullback is STRICT on the de Bruijn base

`context-7` is the STRICTIFICATION rung: the Lumsdaine–Warren "local universes" coherence theorem
(Lumsdaine–Warren 2015; cf. Hofmann 1995, Curien, Bénabou).  In a categorical model of dependent type
theory, reindexing — substitution acting on a type, `A ↦ A[σ]` — is computed by PULLBACK, so it is only
PSEUDOfunctorial: `A[σ][τ] ≅ A[σ ∘ τ]` and `A[id] ≅ A` hold up to a coherent isomorphism, NOT on the
nose.  Syntactic type theory, however, demands STRICT functoriality (`A[σ][τ] = A[σ ∘ τ]`,
`A[id] = A` definitionally), because substitution is defined by structural recursion.  The coherence
theorem strictifies any model into a SPLIT one (strict reindexing) via the local-universes construction.

The FULL theorem is `×type+term` — it strictifies the TYPES and TERMS presheaves fibred over the base —
and lives in `Core/` / `fib`.  This file ships the strictly CONTEXT-SIDE residue: the one fragment of
strictification that lives purely on the BASE of contexts and substitutions, with the type/term
presheaves abstracted away.

  **On the de Bruijn syntactic base, reindexing is ALREADY STRICTLY FUNCTORIAL — split by
  construction, no coherence construction required.**

This is the fixed point of the local-universes construction: `SubstVec` composition is strictly
associative/unital (the shipped `fxBaseSubstCategory` category laws), and the operation that realizes
"substitute under one binder" — the de Bruijn LIFT `σ⁺ = ⟨q, σ ∘ p⟩` (`SubstVec.lift`) — is a STRICT
ENDOFUNCTOR of the substitution base.  Concretely:

  * `SubstVec.lift_identity` — lifting the identity substitution is the identity (`id⁺ = id`): the
    functor preserves identities ON THE NOSE.
  * `SubstVec.lift_compose` — lifting a composite is the composite of lifts (`(σ ∘ τ)⁺ = σ⁺ ∘ τ⁺`):
    the functor preserves composition ON THE NOSE.  This is the CRUX — exactly the strict
    functoriality of reindexing that the local-universes theorem must engineer for a general model and
    that holds DEFINITIONALLY here (via the comprehension-stability square `cons_compose`, the
    display-map naturality `weakening_compose_lift`, and substitution associativity `compose_assoc`).
  * `fxContextExtensionFunctor : RawEndofunctor fxBaseSubstCategory` — the two laws packaged as a
    genuine STRICT endofunctor `(− + 1, lift)` of the substitution base.  That it is a `RawEndofunctor`
    (whose `preservesIdentity` / `preservesComposition` fields are EQUALITIES, not coherent isos) IS
    the strictification conclusion: the syntactic comprehension is a SPLIT comprehension.
  * `fxContextExtensionFunctor_displayNatural` — the display map `p = weakening` is STRICTLY natural
    with respect to the extension functor (`p ∘ σ⁺ = σ ∘ p`), so the strict functor RESPECTS the
    display structure: it is a strict DISPLAY-map endofunctor (a split-comprehension reindexing).
  * `SubstVec.reindexTerm` + `reindexTerm_identity` / `reindexTerm_compose` — ★ the DUAL half: TERM
    reindexing is strict too.  The syntactic term presheaf `Tm` (`scope ↦ RawTerm scope`, substitution as
    action; a covariant functor on `fxBaseSubstCategory = 𝒞ᵒᵖ`, i.e. the presheaf `Tm` on the context
    category `𝒞`) is SPLIT — `t[id] = t` and `t[σ ∘ τ] = t[σ][τ]` hold on the nose — where a semantic model
    has only the coherence isomorphisms the local-universes construction must trivialize.  This is that
    construction's output for terms, delivered DEFINITIONALLY (the same computation as `compose_assoc`).
  * `FxLocalUniversesCoherence` / `fxLocalUniversesCoherence` — ★ the assembled split-comprehension witness:
    the base is strictly associative/unital, CONTEXT reindexing (the lift) and TERM reindexing (`Tm`) are
    strict functors, the display map is strictly natural, and the comprehension square is strictly stable
    under substitution.  The local-universes coherence, context-side, at full strength — one citable value.

Contrast with `fxWeakeningLock` (`context-4` substrate): that is weakening-by-`K` via the `context-3`
COPRODUCT (`(− + K)`, the modal lock carrier); this is weakening-by-one via the comprehension LIFT, the
type-theoretically central "substitution under a binder".  Both are strict endofunctors of the same
base — the de Bruijn presentation makes every reindexing strict.

SHIPPED here (context-side, split by de Bruijn construction): the base, the strict context-extension
endofunctor, the strict SYNTACTIC (raw) `Tm` presheaf, the strict display naturality, the strict
comprehension stability — assembled as `fxLocalUniversesCoherence`.

DEFERRED to `fib-5` (`×type+term`, honestly NOT shipped here, recorded by
`fxLocalUniversesCoherence_hasTypedPresheafStrictification = false`): the actual Lumsdaine–Warren MODEL
construction over a SEMANTIC model — strictifying the TYPED type-in-context presheaf `Ty` and the
term-of-a-type presheaf `Tm(A)`, the local-universe classifying object `(V → U)`, and the
strict-model-≃-pseudo-model equivalence (the coherence isomorphisms it trivializes).  `context-7` delivers
that the BASE reindexing (contexts AND raw terms) is split by construction — the prerequisite making the
typed type/term strictification land. -/

namespace FX1Poly.Axis

open FX1Poly.Core FX1Poly.Axis.Syntax

/-! ## The variable-substitution bridge -/

/-- **Substituting a variable cell looks it up.**  Applying a substitution `vec` to the variable term
`var i` yields `vec.lookup i`.  Proved by routing through `(identity ∘ vec)`: by `lookup_compose` its
`i`-th lookup is `subst vec (identity.lookup i) = subst vec (var i)`, and by `identity_compose` that
composite IS `vec`, so the lookup is `vec.lookup i`.  Zero-axiom. -/
theorem SubstVec.subst_varCell {target source : Nat} (vec : SubstVec target source)
    (index : Fin source) :
    RawTerm.subst vec.toRawTermSubst (SubstVec.varCell index) = vec.lookup index := by
  have viaComposeIdentity :
      ((SubstVec.identity source).compose vec).lookup index
        = RawTerm.subst vec.toRawTermSubst (SubstVec.varCell index) := by
    rw [SubstVec.lookup_compose, SubstVec.identity_lookup]
  rw [SubstVec.identity_compose] at viaComposeIdentity
  exact viaComposeIdentity.symm

/-- **The lift fixes the freshly-bound variable.**  Substituting the zeroth variable under a lifted
substitution `σ⁺` returns the zeroth variable (`σ⁺` sends `var 0 ↦ var 0` — the v-law for the lift's
`cons`-head).  The head-component of the strict composition law below. -/
theorem SubstVec.subst_lift_varCellZero {sourceScope targetScope : Nat}
    (sigma : SubstVec targetScope sourceScope) :
    RawTerm.subst sigma.lift.toRawTermSubst (SubstVec.varCell ⟨0, Nat.succ_pos sourceScope⟩)
      = SubstVec.varCell ⟨0, Nat.succ_pos targetScope⟩ := by
  rw [SubstVec.subst_varCell]
  show (SubstVec.cons (SubstVec.varCell ⟨0, Nat.succ_pos targetScope⟩)
        (sigma.compose (SubstVec.weakening targetScope))).lookup ⟨0, Nat.succ_pos sourceScope⟩
      = SubstVec.varCell ⟨0, Nat.succ_pos targetScope⟩
  exact SubstVec.cons_lookup_zero _ _ _

/-! ## The strict functor laws of the de Bruijn lift (the strictification core) -/

/-- **The lift preserves identities ON THE NOSE** — `id⁺ = id`.  Lifting the identity substitution at
`scope` yields the identity at `scope + 1`.  Proof: `lift id = ⟨q, id ∘ p⟩ = ⟨q, p⟩` (by the left
identity law) `= id_{scope+1}` (by the comprehension η-law `identity_succ_eq_cons`).  This is the
`preservesIdentity` half of the strict reindexing functor. -/
theorem SubstVec.lift_identity (scope : Nat) :
    SubstVec.lift (SubstVec.identity scope) = SubstVec.identity (scope + 1) := by
  show SubstVec.cons (SubstVec.varCell ⟨0, Nat.succ_pos scope⟩)
        ((SubstVec.identity scope).compose (SubstVec.weakening scope))
      = SubstVec.identity (scope + 1)
  rw [SubstVec.identity_compose, ← SubstVec.identity_succ_eq_cons]

/-- ★ **The lift preserves composition ON THE NOSE** — `(σ ∘ τ)⁺ = σ⁺ ∘ τ⁺`.  Lifting a composite of
substitutions is the composite of the lifts.  This is the CRUX of strictification: exactly the strict
functoriality of reindexing that the Lumsdaine–Warren local-universes theorem engineers for a general
model, holding DEFINITIONALLY on the de Bruijn base.

Proof — unfold both lifts (keeping `σ⁺`/`τ⁺` on the right folded), then the RHS `(⟨q, σ∘p⟩) ∘ τ⁺`
expands by the comprehension-stability square `cons_compose` to `⟨ q[τ⁺], (σ∘p) ∘ τ⁺ ⟩`; the head is
`q` (the lift fixes the fresh variable, `subst_lift_varCellZero`) and the tail reassociates to
`(σ∘τ)∘p` via display-map naturality (`weakening_compose_lift`: `p ∘ τ⁺ = τ ∘ p`) bracketed by
substitution associativity (`compose_assoc`).  Both `cons`-components then match the unfolded LHS. -/
theorem SubstVec.lift_compose {sourceScope midScope targetScope : Nat}
    (firstVec : SubstVec midScope sourceScope) (secondVec : SubstVec targetScope midScope) :
    SubstVec.lift (firstVec.compose secondVec)
      = (SubstVec.lift firstVec).compose (SubstVec.lift secondVec) := by
  show SubstVec.cons (SubstVec.varCell ⟨0, Nat.succ_pos targetScope⟩)
        ((firstVec.compose secondVec).compose (SubstVec.weakening targetScope))
      = (SubstVec.cons (SubstVec.varCell ⟨0, Nat.succ_pos midScope⟩)
          (firstVec.compose (SubstVec.weakening midScope))).compose (SubstVec.lift secondVec)
  rw [SubstVec.cons_compose, SubstVec.subst_lift_varCellZero secondVec,
      SubstVec.compose_assoc firstVec secondVec (SubstVec.weakening targetScope),
      ← SubstVec.weakening_compose_lift secondVec,
      ← SubstVec.compose_assoc firstVec (SubstVec.weakening midScope) (SubstVec.lift secondVec)]

/-! ## The strict context-extension endofunctor (the strictification conclusion) -/

/-- ★ **Context extension is a STRICT endofunctor of the substitution base.**  The de Bruijn
context-extension operation `(− + 1, lift)` — add one fresh binding to the context, and act on
substitutions by the under-binder lift — is a genuine `RawEndofunctor` of `fxBaseSubstCategory`.

Its `preservesIdentity` / `preservesComposition` fields are EQUALITIES (`lift_identity` /
`lift_compose`), not coherent isomorphisms: that is precisely what it means for this reindexing to be
SPLIT (strict).  A general categorical model achieves this only via the Lumsdaine–Warren local-universes
construction; on the de Bruijn syntactic base it holds by construction.  This is `context-7`'s
"substitution-as-pullback → strict", realized on the context base. -/
def fxContextExtensionFunctor : RawEndofunctor fxBaseSubstCategory where
  mapObject := fun (scope : Nat) => scope + 1
  mapMorphism := fun substitution => by exact SubstVec.lift substitution
  preservesIdentity := fun scope => by exact SubstVec.lift_identity scope
  preservesComposition := fun firstVec secondVec => by exact SubstVec.lift_compose firstVec secondVec

/-- The extension functor's object action adds one binding (`Γ ↦ Γ.A`, at the scope level `n ↦ n+1`). -/
theorem fxContextExtensionFunctor_mapObject (scope : Nat) :
    fxContextExtensionFunctor.mapObject scope = scope + 1 := rfl

/-- The extension functor's morphism action IS the de Bruijn lift. -/
theorem fxContextExtensionFunctor_mapMorphism {sourceScope targetScope : Nat}
    (substitution : SubstVec targetScope sourceScope) :
    fxContextExtensionFunctor.mapMorphism substitution = SubstVec.lift substitution := rfl

/-- **The display map is STRICTLY natural for the extension functor** — `p ∘ σ⁺ = σ ∘ p`.  The display
projection `weakening` is a strict natural transformation between the context-extension endofunctor and
the identity functor: it commutes with reindexing ON THE NOSE.  This is the shipped Beck–Chevalley
square `weakening_compose_lift` restated through `fxContextExtensionFunctor`, witnessing that the strict
endofunctor RESPECTS the display structure — a strict DISPLAY-map (split-comprehension) reindexing. -/
theorem fxContextExtensionFunctor_displayNatural {sourceScope targetScope : Nat}
    (sigma : SubstVec targetScope sourceScope) :
    (SubstVec.weakening sourceScope).compose (fxContextExtensionFunctor.mapMorphism sigma)
      = sigma.compose (SubstVec.weakening targetScope) :=
  SubstVec.weakening_compose_lift sigma

/-! ## The strict raw-term reindexing presheaf (the split syntactic `Tm`)

The de Bruijn LIFT being a strict endofunctor strictifies reindexing of CONTEXTS.  The DUAL, equally-central
half of the local-universes coherence is the strictness of reindexing of TERMS: the presheaf `Tm` sending a
context to its set of raw terms, with substitution as the morphism-action.

In a SEMANTIC model `Tm` is only PSEUDOfunctorial — reindexing `t ↦ t[σ]` respects identity and composition
of substitutions only up to the coherence isomorphisms the local-universes construction must engineer.  On
the de Bruijn syntactic base it is STRICT by construction: `t[id] = t` and `t[σ ∘ τ] = t[σ][τ]` hold ON THE
NOSE.  Because `fxBaseSubstCategory = 𝒞ᵒᵖ` (its morphisms ARE substitutions), the reindexing action is the
COVARIANT functor `scope ↦ RawTerm scope` on `fxBaseSubstCategory` — i.e. the contravariant presheaf `Tm` on
the context category `𝒞`.  This is the syntactic `Tm` shown SPLIT (the type-free shadow of the
"coherence isomorphisms it trivializes"); the TYPED type-in-context / term-of-a-type presheaves and the
local-universe classifying object remain the `fib-5` deferral (below). -/

/-- **The raw-term reindexing action** — `Tm`'s morphism-action.  A substitution `vec` (an
`fxBaseSubstCategory` morphism `source ⟶ target`, i.e. a `SubstVec target source`) reindexes a raw term in
context `source` to one in context `target` by substitution.  This is the syntactic `Tm` presheaf's action
on morphisms; the strict functor laws follow.

AXIS HYGIENE — why this is CONTEXT-side though its values are `RawTerm` (the term axis's object): raw `Tm`
is REPRESENTABLE by the context base — `Tm(X) = RawTerm X ≅ SubstVec X 1 = Hom_fx(◇.𝟙, X)` (a single term
is a one-variable substitution) — so `Tm = Hom_fx(◇.𝟙, −)` is a HOM-FUNCTOR of the substitution category,
and `reindexTerm` is its postcomposition action.  Its substitution CONTENT is the term axis's `RawTerm.subst`
(`Axis/Term/Subst/`, which `reindexTerm_identity`/`_compose` below delegate to); context only re-packages it
in category language, exactly as `SubstVec.compose` is built from `RawTermSubst.compose`.  TYPED `Tm(A)` is
NOT base-representable (it needs the universe to classify terms-of-a-type) — that is the `×type+term`/`fib-5`
deferral, and this representability of the RAW presheaf is precisely what makes the shipped/deferred line
fall where it does. -/
def SubstVec.reindexTerm {sourceScope targetScope : Nat}
    (vec : SubstVec targetScope sourceScope) (term : RawTerm sourceScope) : RawTerm targetScope :=
  RawTerm.subst vec.toRawTermSubst term

/-- **`Tm` preserves identities ON THE NOSE** — `t[id] = t`.  Reindexing along the identity substitution is
the identity on raw terms.  Proof: the identity vector's lookup is the variable term (`identity_lookup`), so
`subst_pointwise` rebridges the action to `RawTermSubst.identity`, which `subst_identity_apply` collapses.
The `preservesIdentity` half of the syntactic `Tm` presheaf's strictness. -/
theorem SubstVec.reindexTerm_identity {scope : Nat} (term : RawTerm scope) :
    SubstVec.reindexTerm (SubstVec.identity scope) term = term :=
  (RawTerm.subst_pointwise (fun position => SubstVec.identity_lookup scope position) term).trans
    (RawTerm.subst_identity_apply term)

/-- ★ **`Tm` preserves composition ON THE NOSE** — `t[σ ∘ τ] = t[σ][τ]`.  Reindexing along a composite
substitution is the composite of the reindexings (covariantly on `fxBaseSubstCategory`, i.e. contravariantly
on the context category — the presheaf law).  This is the strict functoriality of TERM reindexing that the
Lumsdaine–Warren local-universes theorem engineers for a general model and that holds DEFINITIONALLY on the
de Bruijn base.  Proof: `lookup_compose` rebridges the composite vector's lookup pointwise to
`RawTermSubst.compose` (via `subst_pointwise`), and the shipped subst-then-subst law `RawTerm.subst_compose`
splits it.  (The same computation as the inner calc of `compose_assoc` — this is that associativity law's
term-level shadow.) -/
theorem SubstVec.reindexTerm_compose {sourceScope midScope targetScope : Nat}
    (firstVec : SubstVec midScope sourceScope) (secondVec : SubstVec targetScope midScope)
    (term : RawTerm sourceScope) :
    SubstVec.reindexTerm (firstVec.compose secondVec) term
      = SubstVec.reindexTerm secondVec (SubstVec.reindexTerm firstVec term) :=
  (RawTerm.subst_pointwise
      (fun position => SubstVec.lookup_compose firstVec secondVec position) term).trans
    (RawTerm.subst_compose firstVec.toRawTermSubst secondVec.toRawTermSubst term).symm

/-! ## The split comprehension / local-universes coherence, assembled -/

/-- **The local-universes coherence of the FX context base, context-side, at full strength**, gathered as
one citable object.  Substitution-as-pullback is SPLIT (strict) on the de Bruijn base — the conclusion the
Lumsdaine–Warren construction engineers for a general categorical model, holding here by construction:

  * the base `fxBaseSubstCategory` is strictly associative/unital (`context-1`);
  * CONTEXT reindexing — the de Bruijn context-extension endofunctor (the lift) — is a STRICT endofunctor
    (`contextReindexing`, whose `preservesIdentity` / `preservesComposition` fields are EQUALITIES);
  * TERM reindexing — the syntactic `Tm` presheaf — is a STRICT functor (`termReindexIdentity` /
    `termReindexComposition`);
  * the display map is STRICTLY natural (`displayStrictlyNatural`, the Beck–Chevalley square);
  * the comprehension extension is STRICTLY stable under substitution (`comprehensionStable`, the
    substitution-stability square that makes reindexing well-defined).

Together: the whole split-comprehension datum is strict ON THE NOSE — no coherence isomorphisms to
trivialize. -/
structure FxLocalUniversesCoherence where
  /-- CONTEXT reindexing is a strict endofunctor: the de Bruijn context-extension `(− + 1, lift)`, whose
  functor laws are equalities (`lift_identity` / `lift_compose`) — the split-comprehension reindexing. -/
  contextReindexing : RawEndofunctor fxBaseSubstCategory
  /-- ★ TERM reindexing preserves identities: the syntactic `Tm` presheaf sends `id` to `id` on the nose. -/
  termReindexIdentity : ∀ {scope : Nat} (term : RawTerm scope),
    SubstVec.reindexTerm (SubstVec.identity scope) term = term
  /-- ★ TERM reindexing preserves composition: `t[σ ∘ τ] = t[σ][τ]` — the syntactic `Tm` presheaf is split. -/
  termReindexComposition : ∀ {sourceScope midScope targetScope : Nat}
    (firstVec : SubstVec midScope sourceScope) (secondVec : SubstVec targetScope midScope)
    (term : RawTerm sourceScope),
    SubstVec.reindexTerm (firstVec.compose secondVec) term
      = SubstVec.reindexTerm secondVec (SubstVec.reindexTerm firstVec term)
  /-- The display map `p = weakening` is strictly natural for the context-extension functor (`p ∘ σ⁺ = σ ∘ p`,
  the Beck–Chevalley square) — the strict reindexing RESPECTS the display structure. -/
  displayStrictlyNatural : ∀ {sourceScope targetScope : Nat} (sigma : SubstVec targetScope sourceScope),
    (SubstVec.weakening sourceScope).compose sigma.lift = sigma.compose (SubstVec.weakening targetScope)
  /-- The comprehension extension `⟨head, tail⟩` is strictly stable under substitution (`cons_compose`, the
  substitution-stability square) — the Σ-introduction reindexes on the nose. -/
  comprehensionStable : ∀ {sourceScope midScope targetScope : Nat} (headTerm : RawTerm midScope)
    (tailVec : SubstVec midScope sourceScope) (sigma : SubstVec targetScope midScope),
    (SubstVec.cons headTerm tailVec).compose sigma
      = SubstVec.cons (RawTerm.subst sigma.toRawTermSubst headTerm) (tailVec.compose sigma)

/-- ★ The FX context base HAS local-universes coherence, context-side — the witness wiring the strict
context-extension endofunctor, the strict syntactic `Tm` presheaf (identity + composition), the strict
display naturality, and the strict comprehension stability.  Substitution-as-pullback is SPLIT by
construction; the local-universes construction is the FIXED POINT here, not a step to perform. -/
def fxLocalUniversesCoherence : FxLocalUniversesCoherence where
  contextReindexing := fxContextExtensionFunctor
  termReindexIdentity := fun term => SubstVec.reindexTerm_identity term
  termReindexComposition := fun firstVec secondVec term =>
    SubstVec.reindexTerm_compose firstVec secondVec term
  displayStrictlyNatural := fun sigma => SubstVec.weakening_compose_lift sigma
  comprehensionStable := fun headTerm tailVec sigma => SubstVec.cons_compose headTerm tailVec sigma

/-- **Honesty marker.**  This witness delivers only the CONTEXT-SIDE split structure — the base, the strict
context-extension endofunctor, the strict syntactic (raw) `Tm` presheaf, the strict display naturality, and
the strict comprehension stability — all split by de Bruijn construction.  It does NOT strictify the TYPED
presheaves: the type-in-context functor `Ty`, the term-of-a-type presheaf `Tm(A)`, the local-universe
classifying object `(V → U)`, and the strict-model-≃-pseudo-model equivalence are the actual Lumsdaine–Warren
MODEL construction over a semantic model — `×type+term`, deferred to `fib-5`.  `= false` records that the
typed-presheaf strictification is not performed here. -/
def fxLocalUniversesCoherence_hasTypedPresheafStrictification : Bool := false

/-! ## Smoke: the term presheaf reindexes the fresh variable to the substituted head -/

/-- Smoke: reindexing the zeroth variable along a comprehension extension `⟨head, tail⟩` returns the head
(`Tm`'s action realizes the v-law) — `(var 0)[⟨head, tail⟩] = head`, definitionally after `subst_varCell`. -/
theorem fxLocalUniversesCoherence_reindexTerm_consZero_smoke {scope targetScope : Nat}
    (headTerm : RawTerm targetScope) (tailVec : SubstVec targetScope scope) :
    SubstVec.reindexTerm (SubstVec.cons headTerm tailVec)
        (SubstVec.varCell ⟨0, Nat.succ_pos scope⟩) = headTerm :=
  SubstVec.subst_varCell (SubstVec.cons headTerm tailVec) ⟨0, Nat.succ_pos scope⟩

end FX1Poly.Axis
