import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Context.ExplicitSubstitution

/-! # FX1PolyAudit/AuditTier0ContextExplicitSubstitution — zero-axiom gate for context-8's λσ calculus

Per-declaration zero-axiom gate for `context-8`'s context-side deliverable
(`FX1Poly/Tier0/Context/ExplicitSubstitution.lean`): the λσ (Abadi–Cardelli–Curien–Lévy) EXPLICIT
SUBSTITUTION calculus on the SUBSTITUTION sort, denoting into `fxBaseSubstCategory`.

  * `SubstExpr.denote` (+ the four `denote_*` unfolders) — the interpretation of λσ substitution syntax
    into the semantic `SubstVec` category;
  * `SubstStep.denote_eq` — ★ every one of the seven λσ σ-rules preserves the denotation (each rule IS a
    proven category/comprehension law — soundness of the λσ substitution-equational theory);
  * `SubstStepStar.denote_eq` — multi-step σ-reduction preserves the denotation;
  * `substExpr_churchRosser_modulo_denote` — ★ the calculus is Church–Rosser modulo denotation (any two
    reducts denote to the same morphism — the confluence guarantee at the level of meaning);
  * `SubstStep.idLeft_identity_smoke` — a concrete reduction smoke;
  * `SubstExpr.weight` (+ the four `weight_*` unfolders) + `SubstExpr.weight_pos` — the SN measure;
  * `SubstStep.weight_decreasing` — ★ every σ-rule strictly decreases the weight (the termination certificate);
  * `SubstStep.wellFounded` / `SubstStep.stronglyNormalizing` — ★ STRONG NORMALIZATION: no infinite σ-reduction.

The term closures `a[s]`, the β-rule, the full syntactic critical-pair Church–Rosser, and the Melliès PSN
non-termination boundary are `×term`, deferred to the term axis / `fib` (see the module docstring's ledger).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The denotation into the semantic substitution category + its unfolders
#assert_no_axioms FX1Poly.Tier0.SubstExpr.denote
#assert_no_axioms FX1Poly.Tier0.SubstExpr.denote_identitySub
#assert_no_axioms FX1Poly.Tier0.SubstExpr.denote_shiftSub
#assert_no_axioms FX1Poly.Tier0.SubstExpr.denote_consSub
#assert_no_axioms FX1Poly.Tier0.SubstExpr.denote_composeSub

-- Soundness of the seven λσ σ-rules + multi-step + denotational Church–Rosser
#assert_no_axioms FX1Poly.Tier0.SubstStep.denote_eq
#assert_no_axioms FX1Poly.Tier0.SubstStepStar.denote_eq
#assert_no_axioms FX1Poly.Tier0.substExpr_churchRosser_modulo_denote
#assert_no_axioms FX1Poly.Tier0.SubstStep.idLeft_identity_smoke

-- Strong normalization: the weight measure + every-rule-decreases + well-foundedness
#assert_no_axioms FX1Poly.Tier0.SubstExpr.weight
#assert_no_axioms FX1Poly.Tier0.SubstExpr.weight_identitySub
#assert_no_axioms FX1Poly.Tier0.SubstExpr.weight_shiftSub
#assert_no_axioms FX1Poly.Tier0.SubstExpr.weight_consSub
#assert_no_axioms FX1Poly.Tier0.SubstExpr.weight_composeSub
#assert_no_axioms FX1Poly.Tier0.SubstExpr.weight_pos
#assert_no_axioms FX1Poly.Tier0.SubstStep.weight_decreasing
#assert_no_axioms FX1Poly.Tier0.SubstStep.wellFounded
#assert_no_axioms FX1Poly.Tier0.SubstStep.stronglyNormalizing

end FX1PolyAudit
