import FX1Poly.Tier0.Context.ComprehensionLaws
import FX1Poly.Tier0.Context.Context

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

Contrast with `fxWeakeningLock` (`context-4` substrate): that is weakening-by-`K` via the `context-3`
COPRODUCT (`(− + K)`, the modal lock carrier); this is weakening-by-one via the comprehension LIFT, the
type-theoretically central "substitution under a binder".  Both are strict endofunctors of the same
base — the de Bruijn presentation makes every reindexing strict.

DEFERRED to `fib-5` (`×type+term`, honestly NOT shipped here): the action of strictification on the
TYPES and TERMS presheaves — the local-universes object, the splitting of the type-in-context functor,
and the coherence isomorphisms it trivializes.  `context-7` delivers only that the BASE reindexing is
split by construction, which is the prerequisite making the type/term strictification land. -/

namespace FX1Poly.Tier0

open FX1Poly.Core FX1Poly.Tier0.Syntax

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

end FX1Poly.Tier0
