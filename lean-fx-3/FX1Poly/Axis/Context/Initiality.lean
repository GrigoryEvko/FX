import FX1Poly.Axis.Context.Instances.Subst.FxBaseSubstColimits

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

The object-level fragment is packaged as a genuine INITIAL-ALGEBRA statement (Lambek framing): the
context-extension algebras form a category whose morphisms are `ContextExtensionAlgebraMorphism` (a
carrier map plus the two preservation laws, with `identity`/`compose`), and the syntactic algebra is
its INITIAL object — `syntacticRealizationMorphism` is the morphism OUT of it into any model
(EXISTENCE, realization packaged as a homomorphism) and `syntacticRealizationMorphism_unique` proves
no other morphism exists (UNIQUENESS = the initiality theorem proper), with the unique endomorphism
the identity (`syntacticRealizationMorphism_self_is_identity`).  A non-vacuous FAITHFUL witness model
`unaryListAlgebra` (contexts as telescopes of unit-bindings) shows the realization computes
(`realizeScope_unaryList_length`: scope `n` realizes to a length-`n` telescope) and embeds injectively
(`realizeScope_unaryList_injective`) — so the syntactic context structure is NOT collapsed by
realization.

DEFERRED to `fib-5` (`×type+term`, honestly NOT shipped here): the action on MORPHISMS (substitutions
carry `RawTerm` content = `×term`), the uniqueness of the TYPE/TERM presheaf morphisms (`×type`), and
the intrinsic QIIT presentation with its substitution-coherence quotient (needs `Quot.sound`).
`context-5` is `blockedBy context-6` (biequivalence) and presupposes `context-7` strictification for
the full coherence; only the object-level recursion skeleton is unconditional and lands now. -/

namespace FX1Poly.Axis

universe u v w

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

/-! ### The initial context-extension algebra (Lambek packaging)

The bare-function statements above ARE object-level initiality, but their proper categorical home is
"the syntactic algebra is the INITIAL OBJECT of the category of context-extension algebras."  This
section makes that literal: the morphism of these algebras (a carrier map preserving empty + extend),
the realization repackaged AS the unique such morphism out of the syntactic algebra, its uniqueness
(the initiality theorem proper), and a non-vacuous faithful witness model.  Still strictly
context-side: the morphism here is the object-functor of a CwF-morphism with the type-indexed
comprehension abstracted away (the `×type+term` core stays deferred to `fib-5`). -/

/-- A **homomorphism of context-extension algebras**: a map on carriers that sends the empty context
to the empty context and commutes with context-extension.  This is the object-action of a CwF-morphism
on the context category (its two coherence squares, with the type-indexed part abstracted away), so the
context-extension algebras form a category in which the syntactic algebra will be the initial object. -/
structure ContextExtensionAlgebraMorphism (source : ContextExtensionAlgebra.{u})
    (target : ContextExtensionAlgebra.{v}) where
  /-- The underlying map of semantic contexts. -/
  mapCarrier : source.Carrier → target.Carrier
  /-- The morphism preserves the empty context (the 0-ary generator). -/
  preservesEmpty : mapCarrier source.emptyContext = target.emptyContext
  /-- The morphism commutes with context-extension (the unary generator). -/
  preservesExtend :
    ∀ object, mapCarrier (source.extendContext object) = target.extendContext (mapCarrier object)

/-- The identity homomorphism — the carrier identity preserves both generators trivially. -/
def ContextExtensionAlgebraMorphism.identity (algebra : ContextExtensionAlgebra.{u}) :
    ContextExtensionAlgebraMorphism algebra algebra where
  mapCarrier := fun object => object
  preservesEmpty := rfl
  preservesExtend := fun _object => rfl

/-- Composition of context-extension homomorphisms — the carrier maps compose and the two preservation
laws chain through.  Gives the context-extension algebras genuine categorical composition, so "initial
object" below is a statement about a real category. -/
def ContextExtensionAlgebraMorphism.compose {algebraA : ContextExtensionAlgebra.{u}}
    {algebraB : ContextExtensionAlgebra.{v}} {algebraC : ContextExtensionAlgebra.{w}}
    (firstMorphism : ContextExtensionAlgebraMorphism algebraA algebraB)
    (secondMorphism : ContextExtensionAlgebraMorphism algebraB algebraC) :
    ContextExtensionAlgebraMorphism algebraA algebraC where
  mapCarrier := fun object => secondMorphism.mapCarrier (firstMorphism.mapCarrier object)
  preservesEmpty := by
    show secondMorphism.mapCarrier (firstMorphism.mapCarrier algebraA.emptyContext)
      = algebraC.emptyContext
    rw [firstMorphism.preservesEmpty, secondMorphism.preservesEmpty]
  preservesExtend := fun object => by
    show secondMorphism.mapCarrier (firstMorphism.mapCarrier (algebraA.extendContext object))
      = algebraC.extendContext (secondMorphism.mapCarrier (firstMorphism.mapCarrier object))
    rw [firstMorphism.preservesExtend, secondMorphism.preservesExtend]

/-- **The unique morphism out of the syntactic algebra** (EXISTENCE half of initiality): the
realization repackaged as a homomorphism FROM the syntactic context structure into any model.  Its
carrier map is `realizeScope`, and its two preservation laws are exactly the realization computation
rules (`realizeScope_zero` / `realizeScope_succ`) — the syntactic generators `0`/`Nat.succ` realize to
the model's `emptyContext`/`extendContext`. -/
def syntacticRealizationMorphism (target : ContextExtensionAlgebra.{u}) :
    ContextExtensionAlgebraMorphism fxBaseSubstContextAlgebra target where
  mapCarrier := target.realizeScope
  preservesEmpty := target.realizeScope_zero
  preservesExtend := fun scope => target.realizeScope_succ scope

/-- **The syntactic algebra is initial** (UNIQUENESS half — the initiality theorem proper): every
homomorphism out of the syntactic context structure equals `syntacticRealizationMorphism` pointwise, so
there is exactly one.  Direct from `realizeScope_unique`, reading the morphism's preservation fields as
the recursor's empty/extend obligations. -/
theorem syntacticRealizationMorphism_unique (target : ContextExtensionAlgebra.{u})
    (otherMorphism : ContextExtensionAlgebraMorphism fxBaseSubstContextAlgebra target) (scope : Nat) :
    otherMorphism.mapCarrier scope = (syntacticRealizationMorphism target).mapCarrier scope :=
  target.realizeScope_unique otherMorphism.mapCarrier otherMorphism.preservesEmpty
    otherMorphism.preservesExtend scope

/-- The unique context **endomorphism** of the syntactic structure is the identity (initiality
reflexively, at the morphism level): realizing the syntactic algebra into itself agrees pointwise with
`ContextExtensionAlgebraMorphism.identity`.  This is `fxBaseSubstContextAlgebra_realizeScope_id` lifted
to the morphism packaging. -/
theorem syntacticRealizationMorphism_self_is_identity (scope : Nat) :
    (syntacticRealizationMorphism fxBaseSubstContextAlgebra).mapCarrier scope
      = (ContextExtensionAlgebraMorphism.identity fxBaseSubstContextAlgebra).mapCarrier scope :=
  fxBaseSubstContextAlgebra_realizeScope_id scope

/-- A **non-vacuous faithful witness model**: semantic contexts as TELESCOPES of unit-bindings (carrier
`List Unit`, empty context the empty telescope, extension prepending one binding).  This is the "a
context is a list of `n` bindings" reading; realizing into it exhibits the recursion computing into a
genuinely non-identity model. -/
def unaryListAlgebra : ContextExtensionAlgebra.{0} where
  Carrier := List Unit
  emptyContext := []
  extendContext := fun bindings => () :: bindings

/-- The realization is FAITHFUL on lengths: scope `n` realizes to a telescope of exactly `n` bindings.
Concrete, non-vacuous proof that `realizeScope` computes (structural recursion on the scope). -/
theorem realizeScope_unaryList_length :
    ∀ scope, (unaryListAlgebra.realizeScope scope).length = scope
  | 0 => rfl
  | scope + 1 => congrArg Nat.succ (realizeScope_unaryList_length scope)

/-- The realization **embeds the syntactic scopes injectively** into the telescope model: distinct
scopes realize to distinct telescopes (they have distinct lengths).  So initiality does NOT collapse
the syntactic context structure — there is a model into which it embeds faithfully. -/
theorem realizeScope_unaryList_injective {firstScope secondScope : Nat}
    (realizationsAgree :
      unaryListAlgebra.realizeScope firstScope = unaryListAlgebra.realizeScope secondScope) :
    firstScope = secondScope := by
  have lengthsAgree : (unaryListAlgebra.realizeScope firstScope).length
      = (unaryListAlgebra.realizeScope secondScope).length :=
    congrArg List.length realizationsAgree
  rw [realizeScope_unaryList_length, realizeScope_unaryList_length] at lengthsAgree
  exact lengthsAgree

end FX1Poly.Axis
