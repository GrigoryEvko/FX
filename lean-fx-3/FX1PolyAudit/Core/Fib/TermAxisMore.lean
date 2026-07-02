import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Fib.TermAxis

/-! # FX1PolyAudit/Core/Fib/TermAxisMore — zero-axiom gate for `term-0` (part 2 of 2)

Per-declaration zero-axiom gate for the term-axis ledger (`FX1Poly/Tier0/Term/TermAxis.lean`), continued
from `TermAxis.lean`: `term-13` (meaningless-terms / genericity) through `term-27` (parallel-fold ↔ SSC
reconciliation), plus the honest deferred markers for the structural / coinductive / semantics frontier.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

-- The term-13 meaningless-terms / genericity core + the Böhm-approximant domain
#assert_no_axioms FX1Poly.Tier0.fxTerm_hasMeaninglessGenericity
#assert_no_axioms FX1Poly.Tier0.fxTerm_meaninglessGenericity_isBacked

-- The term-14 mixed inductive-coinductive μ/ν parity (induction + coinduction + finiteness/unboundedness)
#assert_no_axioms FX1Poly.Tier0.fxTerm_hasMixedFixpointParity
#assert_no_axioms FX1Poly.Tier0.fxTerm_mixedFixpointParity_isBacked

-- The term-15 copattern coverage checker (completeness + dependent-index coverage)
#assert_no_axioms FX1Poly.Tier0.fxTerm_hasCopatternCoverage
#assert_no_axioms FX1Poly.Tier0.fxTerm_copatternCoverage_isBacked

-- The term-16 Church-Rosser modulo an equational theory (rewriting modulo AC)
#assert_no_axioms FX1Poly.Tier0.fxTerm_hasRewritingModulo
#assert_no_axioms FX1Poly.Tier0.fxTerm_rewritingModulo_isBacked

-- The term-17 free strict ω-category on the term polygraph + Gray tensor (free-category UP + strict interchange)
#assert_no_axioms FX1Poly.Tier0.fxTerm_hasFreeStrictOmegaCategory
#assert_no_axioms FX1Poly.Tier0.fxTerm_freeStrictOmegaCategory_isBacked

-- The term-18 marked/complicial structure (the equivalence marking + stratification axioms + 2-triviality)
#assert_no_axioms FX1Poly.Tier0.fxTerm_hasMarkedComplicial
#assert_no_axioms FX1Poly.Tier0.fxTerm_markedComplicial_isBacked

-- The term-19 exact SN boundary (persistence + the SN-not-modular necessity counterexample)
#assert_no_axioms FX1Poly.Tier0.fxTerm_hasModularPersistentSN
#assert_no_axioms FX1Poly.Tier0.fxTerm_modularPersistentSN_isBacked

-- The term-20 CAPSTONE word problem (decidable Conv as a function of convergence + the convergence boundary)
#assert_no_axioms FX1Poly.Tier0.fxTerm_hasWordProblemBoundary
#assert_no_axioms FX1Poly.Tier0.fxTerm_wordProblemBoundary_isBacked

-- The term-21 denotational domain / Kleene least-fixpoint core (recursion = least fixpoint)
#assert_no_axioms FX1Poly.Tier0.fxTerm_hasDenotationalDomainFixpoint
#assert_no_axioms FX1Poly.Tier0.fxTerm_denotationalDomainFixpoint_isBacked

-- The term-22 intersection types: BCD subtyping (meet-semilattice + top) + the ω-complete filter model
#assert_no_axioms FX1Poly.Tier0.fxTerm_hasIntersectionFilterModel
#assert_no_axioms FX1Poly.Tier0.fxTerm_intersectionFilterModel_isBacked

-- The term-23 geometry of interaction: the deterministic token machine + execution determinacy + the wire
#assert_no_axioms FX1Poly.Tier0.fxTerm_hasGeometryOfInteraction
#assert_no_axioms FX1Poly.Tier0.fxTerm_geometryOfInteraction_isBacked

-- The term-24 game semantics: deterministic strategies (strategy = function of Opponent's moves) + duality
#assert_no_axioms FX1Poly.Tier0.fxTerm_hasGameSemantics
#assert_no_axioms FX1Poly.Tier0.fxTerm_gameSemantics_isBacked

-- The term-25 differential λ-calculus: derivations (linearity + Leibniz) + linear substitution
#assert_no_axioms FX1Poly.Tier0.fxTerm_hasDifferentialLambda
#assert_no_axioms FX1Poly.Tier0.fxTerm_differentialLambda_isBacked

-- The term-26 single-substitution calculus: single weaken/subst0 + the characteristic SSC equations
#assert_no_axioms FX1Poly.Tier0.fxTerm_hasSingleSubstitutionCalculus
#assert_no_axioms FX1Poly.Tier0.fxTerm_singleSubstitutionCalculus_isBacked

-- The term-27 parallel-fold ↔ SSC reconciliation: single ops = parallel fold specialized + fusion/identity
#assert_no_axioms FX1Poly.Tier0.fxTerm_hasParallelFoldSscBridge
#assert_no_axioms FX1Poly.Tier0.fxTerm_parallelFoldSscBridge_isBacked

-- The honest deferred markers (structural / semantics frontier)
#assert_no_axioms FX1Poly.Tier0.fxTerm_hasKnuthBendixCompletion
#assert_no_axioms FX1Poly.Tier0.fxTerm_hasDenotationalAdequacy

end FX1PolyAudit
