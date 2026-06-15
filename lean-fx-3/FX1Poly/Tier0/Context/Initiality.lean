import FX1Poly.Tier0.Context.Instances.Subst.FxBaseSubstColimits

/-! # context-5 — the syntactic context structure is initial (the object-level residue)

`context-5` is the INITIALITY theorem (Brunerie–de Boer–Lumsdaine–Mörtberg): the syntactic
category-with-families built from the raw syntax is the INITIAL object in the category of CwFs, i.e.
for every model there is a UNIQUE structure-preserving morphism — the interpretation / recursion
principle.  The full theorem is `×type+term` (the coherence between syntactic substitution and
semantic reindexing must be threaded through every former; an honest QIIT presentation needs
`Quot.sound`, which is off-limits under the zero-axiom discipline) and defers to `fib-5`.

This file ships the strictly CONTEXT-SIDE residue — the NON-quotient, object-level fragment, which
is exactly the part the SPLIT DISCIPLINE leaves on the context axis:

  the syntactic context category's OBJECTS (scopes) form the INITIAL ALGEBRA of
  "empty context + context-extension", so a model's context-functor-on-objects is the UNIQUE
  homomorphism out of it.

That uniqueness IS the object-action of the initial CwF-morphism (the recursor's context half), and
it is provable zero-axiom by structural recursion on the scope (`Nat`), with no quotient.  The pieces:

  * `ContextExtensionAlgebra` — the object-level model interface: a carrier of semantic contexts with
    a chosen empty context and a unary context-extension `Γ ↦ Γ.A` (the binding's TYPE `A` is
    ABSTRACTED AWAY — that abstraction is precisely the `×type` content deferred to `fib-5`);
  * `realizeScope` (+ its two computation rules) — EXISTENCE of the morphism-on-objects, by
    structural recursion (`emptyContext` extended `scope`-many times);
  * `realizeScope_unique` / `realization_unique_pointwise` — UNIQUENESS = the genuine initiality:
    any two context-extension homomorphisms agreeing on the generators coincide pointwise;
  * `fxBaseSubstContextAlgebra` — the SYNTACTIC context structure as such an algebra (carrier = the
    `context-0` category's objects, empty = `context-3`'s initial object scope `0`, extend = `+1`);
  * `fxBaseSubstContextAlgebra_realizeScope_id` — initiality reflexively: the unique context
    ENDO-morphism of the syntactic structure is the identity;
  * `fxBaseSubstContextAlgebra_emptyContext_isInitial` — the 0-ary generator IS `context-3`'s shipped
    initial object (`fxBaseSubstInitial`).

DEFERRED to `fib-5` (`×type+term`, honestly NOT shipped here): the action on MORPHISMS (substitutions
carry `RawTerm` content = `×term`), the uniqueness of the TYPE/TERM presheaf morphisms (`×type`), and
the intrinsic QIIT presentation with its substitution-coherence quotient (needs `Quot.sound`).
`context-5` is `blockedBy context-6` (biequivalence) and presupposes `context-7` strictification for
the full coherence; only the object-level recursion skeleton is unconditional and lands now. -/

namespace FX1Poly.Tier0

universe u

/-- The object-level shape of a model CwF's category of contexts: a carrier of semantic contexts, a
chosen empty/terminal context, and a unary context-extension operation `Γ ↦ Γ.A` with the binding's
TYPE abstracted away.  A CwF-morphism's action on the syntactic context OBJECTS is exactly a
homomorphism out of the syntactic algebra into one of these; abstracting the type is what keeps this
purely context-side (the type-indexed comprehension is the `×type` content of `fib-5`). -/
structure ContextExtensionAlgebra where
  /-- The carrier of semantic contexts. -/
  Carrier : Type u
  /-- The empty / terminal context — the 0-ary generator. -/
  emptyContext : Carrier
  /-- Context comprehension on objects: extend a context by one binding (`Γ ↦ Γ.A`). -/
  extendContext : Carrier → Carrier

/-- The **unique realization** of each syntactic scope as an iterated extension of the empty context:
`realizeScope n` is `emptyContext` extended `n`-many times.  This IS the object-action of the unique
CwF-morphism out of the syntactic context category, by structural recursion on the scope. -/
def ContextExtensionAlgebra.realizeScope (algebra : ContextExtensionAlgebra.{u}) (scope : Nat) :
    algebra.Carrier :=
  Nat.rec algebra.emptyContext (fun _ partialResult => algebra.extendContext partialResult) scope

/-- Realization at the empty scope is the empty context (the recursor's base computation rule). -/
theorem ContextExtensionAlgebra.realizeScope_zero (algebra : ContextExtensionAlgebra.{u}) :
    algebra.realizeScope 0 = algebra.emptyContext := rfl

/-- Realization at a successor scope extends the realization of the predecessor (the recursor's step
computation rule). -/
theorem ContextExtensionAlgebra.realizeScope_succ (algebra : ContextExtensionAlgebra.{u})
    (scope : Nat) :
    algebra.realizeScope (scope + 1) = algebra.extendContext (algebra.realizeScope scope) := rfl

/-- **Uniqueness of the realization** (the initiality core): any map out of the syntactic scopes that
sends the empty scope to the empty context and a successor scope to the extension of its predecessor's
image MUST be `realizeScope` — there is no other context-functor-on-objects.  Structural recursion on
the scope, no quotient. -/
theorem ContextExtensionAlgebra.realizeScope_unique (algebra : ContextExtensionAlgebra.{u})
    (candidate : Nat → algebra.Carrier)
    (preservesEmpty : candidate 0 = algebra.emptyContext)
    (preservesExtend : ∀ scope, candidate (scope + 1) = algebra.extendContext (candidate scope)) :
    ∀ scope, candidate scope = algebra.realizeScope scope
  | 0 => preservesEmpty
  | scope + 1 =>
    (preservesExtend scope).trans
      (congrArg algebra.extendContext
        (algebra.realizeScope_unique candidate preservesEmpty preservesExtend scope))

/-- **Object-level initiality**: any TWO context-extension homomorphisms out of the syntactic scopes
that agree on the generators are pointwise equal — the object-action of an initial-CwF morphism is
unique.  Direct corollary of `realizeScope_unique` (both factor through the same realization). -/
theorem ContextExtensionAlgebra.realization_unique_pointwise (algebra : ContextExtensionAlgebra.{u})
    (firstCandidate secondCandidate : Nat → algebra.Carrier)
    (firstEmpty : firstCandidate 0 = algebra.emptyContext)
    (firstExtend : ∀ scope, firstCandidate (scope + 1) = algebra.extendContext (firstCandidate scope))
    (secondEmpty : secondCandidate 0 = algebra.emptyContext)
    (secondExtend :
      ∀ scope, secondCandidate (scope + 1) = algebra.extendContext (secondCandidate scope))
    (scope : Nat) :
    firstCandidate scope = secondCandidate scope :=
  (algebra.realizeScope_unique firstCandidate firstEmpty firstExtend scope).trans
    (algebra.realizeScope_unique secondCandidate secondEmpty secondExtend scope).symm

/-- The SYNTACTIC context category's own object-level context-extension structure: the carrier is the
`context-0` category's objects (scopes `Nat`), the empty context is `context-3`'s initial object
(scope `0`), and context extension is `+1` — the object-action of `context-1`'s comprehension (adding
one binding).  Realizing any model out of THIS algebra is the object-action of the initial
CwF-morphism. -/
def fxBaseSubstContextAlgebra : ContextExtensionAlgebra.{0} where
  Carrier := Nat
  emptyContext := 0
  extendContext := Nat.succ

/-- **Initiality, reflexively**: realizing the syntactic context structure INTO ITSELF is the identity
on scopes — the unique context-ENDO-morphism of the syntactic CwF is `id`.  (Together with
`realizeScope_unique`, this is the "initial object has only the identity endomorphism" fact at the
object level.) -/
theorem fxBaseSubstContextAlgebra_realizeScope_id :
    ∀ scope, fxBaseSubstContextAlgebra.realizeScope scope = scope
  | 0 => rfl
  | scope + 1 => congrArg Nat.succ (fxBaseSubstContextAlgebra_realizeScope_id scope)

/-- The syntactic algebra's empty context (its 0-ary generator) carries `context-3`'s shipped initial
object structure `fxBaseSubstInitial` — the unique substitution from the empty context to every scope.
Ties the object-level initiality residue back to the colimit leg.  (`IsInitialObject` is data, so this
is a `def` re-exposing the witness at the algebra's empty context.) -/
def fxBaseSubstContextAlgebra_emptyContext_isInitial :
    IsInitialObject fxBaseSubstCategory fxBaseSubstContextAlgebra.emptyContext :=
  fxBaseSubstInitial

end FX1Poly.Tier0
