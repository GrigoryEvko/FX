import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Context.SubstitutionFree

/-! # FX1PolyAudit/AuditAxisContextSubstitutionFree — zero-axiom gate for context-9's SFMTT residue

Per-declaration zero-axiom gate for `context-9`'s context-side deliverable
(`FX1Poly/Axis/Context/SubstitutionFree.lean`): the substitution-free structural algorithm (SFMTT) on the
de Bruijn substitution base — substitution is ADMISSIBLE, the structural β-engine uses only `lift`,
`singleton`, and `weakening`, never a general substitution composition.

  * `SubstVec.lift_compose_singleton` — ★ the β-substitution law `(σ⁺) ∘ ⟨arg⟩ = arg · σ`;
  * `SubstVec.singleton_compose` — single substitution under a substitution `⟨arg⟩ ∘ σ = (arg[σ]) · σ`;
  * `SubstVec.singleton_naturality` — ★ the substitution lemma `⟨arg⟩ ∘ σ = (σ⁺) ∘ ⟨arg[σ]⟩`;
  * `SubstVec.cons_eq_lift_compose_singleton` — comprehension extension is admissible (`head·tail = tail⁺∘⟨head⟩`);
  * `SubstVec.factor_lift_singleton` — ★ COMPLETENESS: every substitution into an extended context factors
    through `lift` + a single substitution (substitution is admissible — no general composition primitive);
  * `SubstVec.weakening_is_renaming` / `SubstVec.identity_is_renaming` — weakening and identity are RENAMINGS
    (`singleton` is the only term-carrying structural primitive);
  * `fxSubstitutionFree` — the seven substitution-free laws gathered as the structural-algorithm object;
  * `SubstVec.lift_identity_compose_singleton_smoke` — the β-law at the identity;
  * `RawTerm.subst_cons_eq_singleton_after_lift` — the `⟦×term⟧` context→term bridge corollary (term-axis
    content surfaced in this file: the operational β on terms; gated here for zero-axiom, EXCLUDED from the
    `fxSubstitutionFree` context bundle; home is term-2 / term-26).

The renaming-soundness leg (renamings ⊂ substitutions) is `context-1`'s `renamingInclusion` (already gated);
the modal-lock-relative soundness/completeness is the `×mode` core deferred to `fib-3`.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Axis.SubstVec.lift_compose_singleton
#assert_no_axioms FX1Poly.Axis.SubstVec.singleton_compose
#assert_no_axioms FX1Poly.Axis.SubstVec.singleton_naturality
#assert_no_axioms FX1Poly.Axis.SubstVec.cons_eq_lift_compose_singleton
#assert_no_axioms FX1Poly.Axis.SubstVec.factor_lift_singleton
#assert_no_axioms FX1Poly.Axis.SubstVec.weakening_is_renaming
#assert_no_axioms FX1Poly.Axis.SubstVec.identity_is_renaming
#assert_no_axioms FX1Poly.Axis.fxSubstitutionFree
#assert_no_axioms FX1Poly.Axis.SubstVec.lift_identity_compose_singleton_smoke
#assert_no_axioms FX1Poly.Axis.RawTerm.subst_cons_eq_singleton_after_lift

-- The ALGORITHMIC form: the structural normal form is substitution-free (SFMTT headline, tying to context-12)
#assert_no_axioms FX1Poly.Axis.SubstExpr.IsStructural
#assert_no_axioms FX1Poly.Axis.SubstExpr.isStructural_emptyToScope
#assert_no_axioms FX1Poly.Axis.SubstVec.isStructural_reify
#assert_no_axioms FX1Poly.Axis.fxSubstNormalize_isStructural
#assert_no_axioms FX1Poly.Axis.SubstVec.hasSubstitutionFreePresentation
#assert_no_axioms FX1Poly.Axis.SubstitutionFreeNormalForm
#assert_no_axioms FX1Poly.Axis.fxSubstitutionFreeNormalForm
#assert_no_axioms FX1Poly.Axis.fxSubstNormalize_isStructural_identity_smoke

end FX1PolyAudit
