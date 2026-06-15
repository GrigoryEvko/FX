import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.Strictification

/-! # FX1PolyAudit/AuditTier0ContextStrictification — zero-axiom gate for context-7's strictification

Per-declaration zero-axiom gate for `context-7`'s strictly context-side deliverable
(`FX1Poly/Tier0/Context/Strictification.lean`): the Lumsdaine–Warren local-universes coherence theorem,
realized on the de Bruijn substitution base — substitution-as-pullback is STRICTLY functorial (the base
reindexing is SPLIT by construction, no coherence construction required).

  * `SubstVec.subst_varCell` / `subst_lift_varCellZero` — the variable-substitution bridges (substituting
    a variable cell looks it up; the lift fixes the fresh variable);
  * `SubstVec.lift_identity` — the de Bruijn lift preserves identities ON THE NOSE (`id⁺ = id`);
  * `SubstVec.lift_compose` — ★ the lift preserves composition ON THE NOSE (`(σ∘τ)⁺ = σ⁺∘τ⁺`), the
    strict-functoriality crux;
  * `fxContextExtensionFunctor` — the strict context-extension endofunctor `(− + 1, lift)` of
    `fxBaseSubstCategory` (whose `preservesIdentity`/`preservesComposition` are EQUALITIES — the SPLIT
    reindexing the local-universes theorem must engineer for a general model);
  * `fxContextExtensionFunctor_mapObject` / `_mapMorphism` — the functor's action unfolders;
  * `fxContextExtensionFunctor_displayNatural` — the display map is STRICTLY natural for the extension
    functor (`p ∘ σ⁺ = σ ∘ p`), so it is a strict DISPLAY-map (split-comprehension) reindexing.

The action of strictification on the TYPES/TERMS presheaves (the local-universes object, the splitting
of the type-in-context functor, the trivialized coherence isomorphisms) is the cross-axis core, honestly
deferred to `fib-5`.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The variable-substitution bridges
#assert_no_axioms FX1Poly.Tier0.SubstVec.subst_varCell
#assert_no_axioms FX1Poly.Tier0.SubstVec.subst_lift_varCellZero

-- The strict functor laws of the de Bruijn lift (the strictification core)
#assert_no_axioms FX1Poly.Tier0.SubstVec.lift_identity
#assert_no_axioms FX1Poly.Tier0.SubstVec.lift_compose

-- The strict context-extension endofunctor + its action unfolders + display-map strict naturality
#assert_no_axioms FX1Poly.Tier0.fxContextExtensionFunctor
#assert_no_axioms FX1Poly.Tier0.fxContextExtensionFunctor_mapObject
#assert_no_axioms FX1Poly.Tier0.fxContextExtensionFunctor_mapMorphism
#assert_no_axioms FX1Poly.Tier0.fxContextExtensionFunctor_displayNatural

end FX1PolyAudit
