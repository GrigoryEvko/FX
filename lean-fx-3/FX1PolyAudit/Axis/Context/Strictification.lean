import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Context.Strictification

/-! # FX1PolyAudit/AuditAxisContextStrictification — zero-axiom gate for context-7's strictification

Per-declaration zero-axiom gate for `context-7`'s strictly context-side deliverable
(`FX1Poly/Axis/Context/Strictification.lean`): the Lumsdaine–Warren local-universes coherence theorem,
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
  * `SubstVec.reindexTerm` / `reindexTerm_identity` / `reindexTerm_compose` — ★ the DUAL half: the
    syntactic raw-term presheaf `Tm` (substitution as morphism-action) is a STRICT functor on
    `fxBaseSubstCategory` (`t[id] = t`, `t[σ∘τ] = t[σ][τ]` on the nose) — `Tm` shown SPLIT;
  * `FxLocalUniversesCoherence` / `fxLocalUniversesCoherence` — ★ the assembled split-comprehension witness
    (strict base + context reindexing + term `Tm` reindexing + display naturality + comprehension
    stability), the context-side local-universes coherence at full strength;
  * `fxLocalUniversesCoherence_hasTypedPresheafStrictification` — the honesty marker (`= false`); see below;
  * `fxLocalUniversesCoherence_reindexTerm_consZero_smoke` — `Tm` realizes the v-law (`(var 0)[⟨h,t⟩] = h`).

The actual Lumsdaine–Warren MODEL construction over a SEMANTIC model — strictifying the TYPED
type-in-context `Ty` / term-of-a-type `Tm(A)` presheaves, the local-universe classifying object `(V → U)`,
and the strict-≃-pseudo model equivalence — is the cross-axis core (`×type+term`), honestly deferred to
`fib-5` and recorded by `fxLocalUniversesCoherence_hasTypedPresheafStrictification = false`.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The variable-substitution bridges
#assert_no_axioms FX1Poly.Axis.SubstVec.subst_varCell
#assert_no_axioms FX1Poly.Axis.SubstVec.subst_lift_varCellZero

-- The strict functor laws of the de Bruijn lift (the strictification core)
#assert_no_axioms FX1Poly.Axis.SubstVec.lift_identity
#assert_no_axioms FX1Poly.Axis.SubstVec.lift_compose

-- The strict context-extension endofunctor + its action unfolders + display-map strict naturality
#assert_no_axioms FX1Poly.Axis.fxContextExtensionFunctor
#assert_no_axioms FX1Poly.Axis.fxContextExtensionFunctor_mapObject
#assert_no_axioms FX1Poly.Axis.fxContextExtensionFunctor_mapMorphism
#assert_no_axioms FX1Poly.Axis.fxContextExtensionFunctor_displayNatural

-- The strict raw-term reindexing presheaf (the split syntactic `Tm`)
#assert_no_axioms FX1Poly.Axis.SubstVec.reindexTerm
#assert_no_axioms FX1Poly.Axis.SubstVec.reindexTerm_identity
#assert_no_axioms FX1Poly.Axis.SubstVec.reindexTerm_compose

-- The assembled split-comprehension / local-universes coherence witness + honesty marker + smoke
#assert_no_axioms FX1Poly.Axis.FxLocalUniversesCoherence
#assert_no_axioms FX1Poly.Axis.fxLocalUniversesCoherence
#assert_no_axioms FX1Poly.Axis.fxLocalUniversesCoherence_hasTypedPresheafStrictification
#assert_no_axioms FX1Poly.Axis.fxLocalUniversesCoherence_reindexTerm_consZero_smoke

end FX1PolyAudit
