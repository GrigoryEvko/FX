import FX1PolyAudit.DependencyAudit
import FX1Poly.Tier0.Term.Codata.CopatternCoverage

/-! # FX1PolyAudit/AuditTier0TermCopatternCoverage — zero-axiom gate for term-15 (copattern coverage)

Per-declaration zero-axiom gate for `FX1Poly/Tier0/Term/Codata/CopatternCoverage.lean`: the copattern trie +
the decidable coverage checker (`CopatternTrie` / `allCovering*` / `isCovering`), the coverage-completeness
theorem (`CoverageResult` / `resolve` / `covering_resolves_without_gap`), the dependent-index coverage
(`DependentCoveringTree` / `DependentObservation` / `resolveDependent` /
`dependentCoverage_leafOrExhaustiveSplit`), and the stream witnesses.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The copattern trie + the decidable coverage checker
#assert_no_axioms FX1Poly.Core.CopatternTrie
#assert_no_axioms FX1Poly.Core.CopatternTrie.allCoveringBelow
#assert_no_axioms FX1Poly.Core.CopatternTrie.allCovering
#assert_no_axioms FX1Poly.Core.CopatternTrie.allCoveringBelow_sound
#assert_no_axioms FX1Poly.Core.CopatternTrie.allCovering_sound
#assert_no_axioms FX1Poly.Core.CopatternTrie.isCovering

-- Coverage completeness: a covering trie resolves every observation without a gap
#assert_no_axioms FX1Poly.Core.CoverageResult
#assert_no_axioms FX1Poly.Core.CopatternTrie.resolve
#assert_no_axioms FX1Poly.Core.covering_resolves_without_gap

-- Coverage with dependent indices
#assert_no_axioms FX1Poly.Core.DependentCoveringTree
#assert_no_axioms FX1Poly.Core.DependentObservation
#assert_no_axioms FX1Poly.Core.DependentCoveringTree.resolveDependent
#assert_no_axioms FX1Poly.Core.dependentCoverage_leafOrExhaustiveSplit

-- The stream witnesses (covering vs incomplete)
#assert_no_axioms FX1Poly.Core.streamCoveringTrie
#assert_no_axioms FX1Poly.Core.streamCoveringTrie_isCovering
#assert_no_axioms FX1Poly.Core.incompleteStreamTrie
#assert_no_axioms FX1Poly.Core.incompleteStreamTrie_notCovering

end FX1PolyAudit
