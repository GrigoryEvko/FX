import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.BeckChevalleyCoherence

/-! # FX1PolyAudit/AuditTier0ContextBeckChevalleyCoherence — zero-axiom gate for context-17

Per-declaration zero-axiom gate for `context-17`'s context-side deliverable
(`FX1Poly/Tier0/Context/BeckChevalleyCoherence.lean`): the Beck–Chevalley coherence of the FX context base
at FULL STRENGTH — the display map as a genuine natural transformation, the BC pasting coherence, and the
naturality of the Σ-introduction and display projection.

  * `fxDisplayTransformation` — ★ the display map as a `RawEndofunctorTransformation` `id ⇒ extension`
    (naturality = `weakening_compose_lift` at every morphism);
  * `fxDisplayTowerTransformation` — ★ the iterated display tower `id ⇒ extension ∘ extension` (the Godement
    `hcomp` of the display 2-cell with itself; BC composes 2-categorically, naturality is free);
  * `fxDisplayTowerTransformation_component` — the tower's component is the 2-fold display `p ∘ p`;
  * `SubstVec.beckChevalley_paste` — ★ the BC pasting coherence (`p ∘ (τ⁺ ∘ σ⁺) = (τ ∘ σ) ∘ p`);
  * `SubstVec.weakening_tower_natural` — ★ the explicit telescope BC (`p² ∘ σ⁺⁺ = σ ∘ p²`);
  * `SubstVec.weakening_compose_cons_natural` — the display projection is natural in the context;
  * `fxComprehensionPullback` — ★ the substitution/display square as a genuine `PullbackSquare` in the real
    context category `𝒞` (`context-15`'s opposite) — display maps are stable under pullback (THE BC heart);
  * `FxBeckChevalleyCoherence` / `fxBeckChevalleyCoherence` — the assembled coherence object;
  * `fxDisplayTransformation_component_smoke` / `fxComprehensionPullback_projectionRight_smoke` — smokes.

The substitution-square universal property NOW lands as a PULLBACK in `𝒞` (`fxComprehensionPullback`, via
`context-15`); in `𝒞ᵒᵖ = fxBaseSubstCategory` the same square is the colimit-layer PUSHOUT.  The Π-direction
Beck–Chevalley still needs the Π right adjoint (LCC, `×type → context-16`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Tier0.fxDisplayTransformation
#assert_no_axioms FX1Poly.Tier0.fxDisplayTowerTransformation
#assert_no_axioms FX1Poly.Tier0.fxDisplayTowerTransformation_component
#assert_no_axioms FX1Poly.Tier0.SubstVec.beckChevalley_paste
#assert_no_axioms FX1Poly.Tier0.SubstVec.weakening_tower_natural
#assert_no_axioms FX1Poly.Tier0.SubstVec.weakening_compose_cons_natural
#assert_no_axioms FX1Poly.Tier0.fxComprehensionPullback
#assert_no_axioms FX1Poly.Tier0.FxBeckChevalleyCoherence
#assert_no_axioms FX1Poly.Tier0.fxBeckChevalleyCoherence
#assert_no_axioms FX1Poly.Tier0.fxDisplayTransformation_component_smoke
#assert_no_axioms FX1Poly.Tier0.fxComprehensionPullback_projectionRight_smoke

end FX1PolyAudit
