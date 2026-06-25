import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.Initiality

/-! # FX1PolyAudit/AuditTier0ContextInitiality — zero-axiom gate for context-5's object-level residue

Per-declaration zero-axiom gate for `context-5`'s strictly context-side deliverable
(`FX1Poly/Tier0/Context/Initiality.lean`): the object-level fragment of the INITIALITY theorem — the
syntactic context category's objects (scopes) form the initial algebra of "empty context +
context-extension", so a model's context-functor-on-objects is the unique homomorphism out of it.

  * `ContextExtensionAlgebra` — the object-level model interface (carrier + empty + extend, type
    abstracted away — the `×type` content is deferred);
  * `realizeScope` + `realizeScope_zero` / `realizeScope_succ` — EXISTENCE of the morphism-on-objects
    by structural recursion, with its two computation rules;
  * `realizeScope_unique` + `realization_unique_pointwise` — UNIQUENESS = the genuine object-level
    initiality (any two homomorphisms agreeing on the generators coincide);
  * `fxBaseSubstContextAlgebra` — the syntactic context structure as an algebra (wired to `context-0`
    objects + `context-3` initial object + `context-1` comprehension);
  * `fxBaseSubstContextAlgebra_realizeScope_id` — the unique context endomorphism is the identity;
  * `fxBaseSubstContextAlgebra_emptyContext_isInitial` — the 0-ary generator IS `fxBaseSubstInitial`.

The object-level fragment is then packaged as a genuine INITIAL-ALGEBRA statement (Lambek framing):

  * `ContextExtensionAlgebraMorphism` (+ `identity` / `compose`) — the homomorphisms of these algebras,
    making them a category in which the syntactic algebra is the initial object;
  * `syntacticRealizationMorphism` — EXISTENCE: the realization packaged as the morphism OUT of the
    syntactic algebra into any model;
  * `syntacticRealizationMorphism_unique` — UNIQUENESS = the initiality theorem proper (no other
    morphism out of the syntactic algebra);
  * `syntacticRealizationMorphism_self_is_identity` — the unique endomorphism is the identity;
  * `unaryListAlgebra` + `realizeScope_unaryList_length` / `realizeScope_unaryList_injective` — a
    non-vacuous FAITHFUL witness model (contexts as telescopes of unit-bindings) into which the
    syntactic scopes embed injectively.

The action on MORPHISMS (substitutions = `×term`), the type/term presheaf morphism uniqueness
(`×type`), and the intrinsic QIIT presentation with its substitution-coherence quotient (needs
`Quot.sound`) are the cross-axis core, honestly deferred to `fib-5`.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The object-level model interface + the unique realization with its two computation rules
#assert_no_axioms FX1Poly.Tier0.ContextExtensionAlgebra
#assert_no_axioms FX1Poly.Tier0.ContextExtensionAlgebra.realizeScope
#assert_no_axioms FX1Poly.Tier0.ContextExtensionAlgebra.realizeScope_zero
#assert_no_axioms FX1Poly.Tier0.ContextExtensionAlgebra.realizeScope_succ

-- The initiality core: uniqueness of the realization + pointwise rigidity of any two homomorphisms
#assert_no_axioms FX1Poly.Tier0.ContextExtensionAlgebra.realizeScope_unique
#assert_no_axioms FX1Poly.Tier0.ContextExtensionAlgebra.realization_unique_pointwise

-- The syntactic context structure as an algebra + reflexive initiality + tie to context-3's colimit
#assert_no_axioms FX1Poly.Tier0.fxBaseSubstContextAlgebra
#assert_no_axioms FX1Poly.Tier0.fxBaseSubstContextAlgebra_realizeScope_id
#assert_no_axioms FX1Poly.Tier0.fxBaseSubstContextAlgebra_emptyContext_isInitial

-- The initial-algebra packaging (Lambek): the morphisms of context-extension algebras + their category
#assert_no_axioms FX1Poly.Tier0.ContextExtensionAlgebraMorphism
#assert_no_axioms FX1Poly.Tier0.ContextExtensionAlgebraMorphism.identity
#assert_no_axioms FX1Poly.Tier0.ContextExtensionAlgebraMorphism.compose

-- The syntactic algebra is the initial object: the unique realization morphism + its uniqueness/idem
#assert_no_axioms FX1Poly.Tier0.syntacticRealizationMorphism
#assert_no_axioms FX1Poly.Tier0.syntacticRealizationMorphism_unique
#assert_no_axioms FX1Poly.Tier0.syntacticRealizationMorphism_self_is_identity

-- The non-vacuous faithful witness model (contexts as telescopes of unit-bindings)
#assert_no_axioms FX1Poly.Tier0.unaryListAlgebra
#assert_no_axioms FX1Poly.Tier0.realizeScope_unaryList_length
#assert_no_axioms FX1Poly.Tier0.realizeScope_unaryList_injective

end FX1PolyAudit
