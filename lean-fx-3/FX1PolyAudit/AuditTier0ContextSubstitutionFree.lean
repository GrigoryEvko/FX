import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.SubstitutionFree

/-! # FX1PolyAudit/AuditTier0ContextSubstitutionFree — zero-axiom gate for context-9's SFMTT residue

Per-declaration zero-axiom gate for `context-9`'s context-side deliverable
(`FX1Poly/Tier0/Context/SubstitutionFree.lean`): the substitution-free structural algorithm (SFMTT) on the
de Bruijn substitution base — substitution is ADMISSIBLE, the structural β-engine uses only `lift`,
`singleton`, and `weakening`, never a general substitution composition.

  * `SubstVec.lift_compose_singleton` — ★ the β-substitution law `(σ⁺) ∘ ⟨arg⟩ = arg · σ`;
  * `SubstVec.singleton_compose` — single substitution under a substitution `⟨arg⟩ ∘ σ = (arg[σ]) · σ`;
  * `SubstVec.singleton_naturality` — ★ the substitution lemma `⟨arg⟩ ∘ σ = (σ⁺) ∘ ⟨arg[σ]⟩`;
  * `SubstVec.cons_eq_lift_compose_singleton` — comprehension extension is admissible (`head·tail = tail⁺∘⟨head⟩`);
  * `SubstVec.factor_lift_singleton` — ★ COMPLETENESS: every substitution into an extended context factors
    through `lift` + a single substitution (substitution is admissible — no general composition primitive);
  * `SubstVec.weakening_is_renaming` — weakening is a RENAMING (the structural maps are substitution-free);
  * `fxSubstitutionFree` — the seven substitution-free laws gathered as the structural-algorithm object;
  * `SubstVec.lift_identity_compose_singleton_smoke` — the β-law at the identity.

The renaming-soundness leg (renamings ⊂ substitutions) is `context-1`'s `renamingInclusion` (already gated);
the modal-lock-relative soundness/completeness is the `×mode` core deferred to `fib-3`.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Tier0.SubstVec.lift_compose_singleton
#assert_no_axioms FX1Poly.Tier0.SubstVec.singleton_compose
#assert_no_axioms FX1Poly.Tier0.SubstVec.singleton_naturality
#assert_no_axioms FX1Poly.Tier0.SubstVec.cons_eq_lift_compose_singleton
#assert_no_axioms FX1Poly.Tier0.SubstVec.factor_lift_singleton
#assert_no_axioms FX1Poly.Tier0.SubstVec.weakening_is_renaming
#assert_no_axioms FX1Poly.Tier0.fxSubstitutionFree
#assert_no_axioms FX1Poly.Tier0.SubstVec.lift_identity_compose_singleton_smoke

end FX1PolyAudit
