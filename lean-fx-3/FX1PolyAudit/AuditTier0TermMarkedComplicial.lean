import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Term.Rewrite.MarkedComplicial

/-! # FX1PolyAudit/AuditTier0TermMarkedComplicial — zero-axiom gate for term-18 (marked/complicial)

Per-declaration zero-axiom gate for `FX1Poly/Tier0/Term/Rewrite/MarkedComplicial.lean`: the dimension-1
equivalence marking (`IsRewriteEquivalence`), the stratification axioms (`rewriteEquivalence_nil` /
`rewriteEquivalence_symm` / `rewriteEquivalence_comp`), 2-triviality (`rewriteOmega_twoTrivial`), and the
packaged marked rewriting ω-category (`RewriteMarking` / `equivalenceMarking`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The dimension-1 equivalence marking + the stratification axioms
#assert_no_axioms FX1Poly.Core.IsRewriteEquivalence
#assert_no_axioms FX1Poly.Core.rewriteEquivalence_nil
#assert_no_axioms FX1Poly.Core.rewriteEquivalence_symm
#assert_no_axioms FX1Poly.Core.rewriteEquivalence_comp

-- 2-triviality (every 2-cell thin ⟹ the (∞,1) presentation)
#assert_no_axioms FX1Poly.Core.rewriteOmega_twoTrivial

-- The packaged marked rewriting ω-category
#assert_no_axioms FX1Poly.Core.RewriteMarking
#assert_no_axioms FX1Poly.Core.equivalenceMarking

end FX1PolyAudit
