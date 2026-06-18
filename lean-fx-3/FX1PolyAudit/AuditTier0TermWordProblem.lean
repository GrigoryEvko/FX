import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Term.Rewrite.WordProblem

/-! # FX1PolyAudit/AuditTier0TermWordProblem — zero-axiom gate for term-20 (word problem, CAPSTONE)

Per-declaration zero-axiom gate for `FX1Poly/Tier0/Term/Rewrite/WordProblem.lean`: the decidability-boundary
witnesses (`ForkCarrier` / `forkStep` / the apex/leaf/normal lemmas / `forkStep_apex_hasTwoDistinctNormalForms`
/ `forkStep_notConfluent`).  The POSITIVE decision is `term-7`'s engine (`ConvergentNormalizer.*`), cited by
the `term-20` marker, not duplicated here.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The boundary: confluence is necessary (a non-confluent system with two distinct normal forms)
#assert_no_axioms FX1Poly.Core.ForkCarrier
#assert_no_axioms FX1Poly.Core.forkStep
#assert_no_axioms FX1Poly.Core.forkStep_apex_leftLeaf
#assert_no_axioms FX1Poly.Core.forkStep_apex_rightLeaf
#assert_no_axioms FX1Poly.Core.forkStep_leftLeaf_normal
#assert_no_axioms FX1Poly.Core.forkStep_rightLeaf_normal
#assert_no_axioms FX1Poly.Core.forkLeaves_distinct
#assert_no_axioms FX1Poly.Core.forkStep_apex_hasTwoDistinctNormalForms
#assert_no_axioms FX1Poly.Core.forkStep_notConfluent

end FX1PolyAudit
