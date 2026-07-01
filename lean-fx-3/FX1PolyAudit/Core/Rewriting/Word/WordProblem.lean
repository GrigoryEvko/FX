import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.Word.WordProblem

/-! # FX1PolyAudit/AuditCoreRewritingWordWordProblem — zero-axiom gate for term-20 (word problem, CAPSTONE)

Per-declaration zero-axiom gate for `FX1Poly/Core/Rewriting/Word/WordProblem.lean`: the word problem +
positive decision (`WordProblem` / `wordProblem_iff_normalFormEq` / `decidableWordProblem_of_convergent`)
and the confluence-necessity boundary witnesses (`ForkCarrier` / `forkStep` / the apex/leaf/normal lemmas /
`forkStep_apex_hasTwoDistinctNormalForms` / `forkStep_notConfluent`).

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The word problem + the positive decision (decidable as a function of convergence)
#assert_no_axioms FX1Poly.Core.WordProblem
#assert_no_axioms FX1Poly.Core.wordProblem_iff_normalFormEq
#assert_no_axioms FX1Poly.Core.decidableWordProblem_of_convergent

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
