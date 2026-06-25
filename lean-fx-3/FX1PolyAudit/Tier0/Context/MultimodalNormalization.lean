import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.MultimodalNormalization

/-! # FX1PolyAudit/AuditTier0ContextMultimodalNormalization — zero-axiom gate for context-12's NbE

Per-declaration zero-axiom gate for `context-12`'s context-side deliverable
(`FX1Poly/Tier0/Context/MultimodalNormalization.lean`): Gratzer-style multimodal NbE over the modal base,
realized as normalization-by-evaluation for the SUBSTITUTION calculus (the base's morphisms) — eval is
`context-8`'s `denote`, reify + the section + the normalizer + the σ-rewriting bridge are added here.

  * `NbeRetraction` + `normalize` + `eval_normalize` / `normalize_idempotent` / `normalize_complete` /
    `eval_eq_of_normalize_eq` / `normalize_eq_iff_eval_eq` — the generic NbE-as-retraction package
    (soundness / idempotence / completeness / the conversion characterization);
  * `SubstExpr.emptyToScope` / `SubstVec.reify` / `SubstExpr.denote_reify` — reify for the substitution
    calculus + ★ the section law `denote ∘ reify = id`;
  * `fxSubstNbe` / `fxSubstNormalize` / `fxSubstNormalize_denote` / `fxSubstConv_iff` — the concrete NbE,
    the normalizer, soundness, and ★ the conversion characterization (conversion = semantic equality);
  * `fxSubstNormalize_substStep_invariant` / `fxSubstNormalize_substStepStar_invariant` — ★ the NbE normal
    form is a σ-rewriting invariant (the bridge to `context-8`: Path-A NbE agrees with Path-rewriting);
  * `FxMultimodalNbe` / `fxMultimodalNbe` — the assembled witness;
  * `fxMultimodalNbe_hasTypedTermReification` / `fxMultimodalNbe_hasModalLockThreading` — the honesty
    markers (`= false`): typed-term reification is `×type+term`/`fib-6`; modal-lock threading is
    `×mode`/`fib-3`;
  * `fxMultimodalNbe_normalize_idempotent_smoke`.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The generic NbE-as-retraction package
#assert_no_axioms FX1Poly.Tier0.NbeRetraction
#assert_no_axioms FX1Poly.Tier0.NbeRetraction.normalize
#assert_no_axioms FX1Poly.Tier0.NbeRetraction.eval_normalize
#assert_no_axioms FX1Poly.Tier0.NbeRetraction.normalize_idempotent
#assert_no_axioms FX1Poly.Tier0.NbeRetraction.normalize_complete
#assert_no_axioms FX1Poly.Tier0.NbeRetraction.eval_eq_of_normalize_eq
#assert_no_axioms FX1Poly.Tier0.NbeRetraction.normalize_eq_iff_eval_eq

-- reify for the substitution calculus + the section law
#assert_no_axioms FX1Poly.Tier0.SubstExpr.emptyToScope
#assert_no_axioms FX1Poly.Tier0.SubstVec.reify
#assert_no_axioms FX1Poly.Tier0.SubstExpr.denote_reify

-- The concrete substitution-calculus NbE + soundness + the conversion characterization
#assert_no_axioms FX1Poly.Tier0.fxSubstNbe
#assert_no_axioms FX1Poly.Tier0.fxSubstNormalize
#assert_no_axioms FX1Poly.Tier0.fxSubstNormalize_denote
#assert_no_axioms FX1Poly.Tier0.fxSubstConv_iff

-- The bridge to context-8's σ-rewriting (NbE normal form is a rewriting invariant)
#assert_no_axioms FX1Poly.Tier0.fxSubstNormalize_substStep_invariant
#assert_no_axioms FX1Poly.Tier0.fxSubstNormalize_substStepStar_invariant

-- The assembled witness + honesty markers + smoke
#assert_no_axioms FX1Poly.Tier0.FxMultimodalNbe
#assert_no_axioms FX1Poly.Tier0.fxMultimodalNbe
#assert_no_axioms FX1Poly.Tier0.fxMultimodalNbe_hasTypedTermReification
#assert_no_axioms FX1Poly.Tier0.fxMultimodalNbe_hasModalLockThreading
#assert_no_axioms FX1Poly.Tier0.fxMultimodalNbe_normalize_idempotent_smoke

end FX1PolyAudit
