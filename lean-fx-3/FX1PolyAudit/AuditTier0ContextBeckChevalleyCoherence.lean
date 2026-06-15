import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.BeckChevalleyCoherence

/-! # FX1PolyAudit/AuditTier0ContextBeckChevalleyCoherence — zero-axiom gate for context-17

Per-declaration zero-axiom gate for `context-17`'s context-side deliverable
(`FX1Poly/Tier0/Context/BeckChevalleyCoherence.lean`): the Beck–Chevalley coherence of the FX context base
at FULL STRENGTH — the display map as a genuine natural transformation, the BC pasting coherence, and the
naturality of the Σ-introduction and display projection.

  * `fxDisplayTransformation` — ★ the display map as a `RawEndofunctorTransformation` `id ⇒ extension`
    (naturality = `weakening_compose_lift` at every morphism);
  * `SubstVec.beckChevalley_paste` — ★ the BC pasting coherence (`p ∘ (τ⁺ ∘ σ⁺) = (τ ∘ σ) ∘ p`);
  * `SubstVec.weakening_compose_cons_natural` — the display projection is natural in the context;
  * `FxBeckChevalleyCoherence` / `fxBeckChevalleyCoherence` — the assembled coherence object;
  * `fxDisplayTransformation_component_smoke` — the nat-trans component is the display map `weakening`.

The substitution-square universal property is a PUSHOUT here (colimit → `context-3`/`context-20`); the
Π-direction Beck–Chevalley needs the Π right adjoint (LCC, `×type → context-16`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Tier0.fxDisplayTransformation
#assert_no_axioms FX1Poly.Tier0.SubstVec.beckChevalley_paste
#assert_no_axioms FX1Poly.Tier0.SubstVec.weakening_compose_cons_natural
#assert_no_axioms FX1Poly.Tier0.FxBeckChevalleyCoherence
#assert_no_axioms FX1Poly.Tier0.fxBeckChevalleyCoherence
#assert_no_axioms FX1Poly.Tier0.fxDisplayTransformation_component_smoke

end FX1PolyAudit
