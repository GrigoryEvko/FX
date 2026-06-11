import FX1PolyAudit.AuditGen
-- Sole import: the OPT-1 cell-category module transitively loads OPT-0
-- (OptimizationCell), COST-4 (CostAwareEquivalence), and the generic
-- Conv-congruence lifter, so every gated declaration below is loaded.
import FX1Poly.Typed.OptimizationCellCategory

/-! # FX1PolyAudit/AuditOptimizationCellCategory
    — zero-axiom gates for the extensional-equivalence optimization-cell CATEGORY (OPT-1)

Per-declaration `#assert_no_axioms` gates for every theorem/def in
`FX1Poly.Typed.OptimizationCellCategory`, plus a namespace sweep over
`FX1Poly.Typed` to catch any leak in a transitively-loaded sibling.
The category laws, the equivalence-half context congruence, the honest
cost-congruence pin, the composition demo, and the verdict ledger are
all propext/Quot.sound/Classical/sorry-free. -/

-- THE THREE CATEGORY LAWS (strict cell equalities, by proof irrelevance):
-- left/right identity unit + associativity.  The cell's only data fields
-- are its two program subjects; both composition operations project them
-- definitionally and every remaining field is Prop-valued, so each law is
-- `cases; rfl`.  The category is STRICT, not up-to-isomorphism.
#assert_no_axioms FX1Poly.Typed.OptimizationCell.compose_identity_left
#assert_no_axioms FX1Poly.Typed.OptimizationCell.compose_identity_right
#assert_no_axioms FX1Poly.Typed.OptimizationCell.compose_assoc

-- COST-COMPOSITION SEMANTICS: a cell carries a `≤` BOUND, not a delta;
-- composition is the transitivity of the COST-4 `Improves` preorder, and
-- the composite's cost datum is again one chained bound (no addition).
#assert_no_axioms FX1Poly.Typed.OptimizationCell.compose_improves
#assert_no_axioms FX1Poly.Typed.OptimizationCell.compose_costCertificate_isBound

-- CONTEXT CONGRUENCE, EQUIVALENCE HALF (unconditional, via Conv.ofChildren):
-- a cell's extensional certificate lifts through app-function, app-argument,
-- and lam-body contexts.
#assert_no_axioms FX1Poly.Typed.OptimizationCell.extensionalCongruence_inAppFunction
#assert_no_axioms FX1Poly.Typed.OptimizationCell.extensionalCongruence_inAppArgument
#assert_no_axioms FX1Poly.Typed.extensionalCongruence_inLamBody

-- CONTEXT CONGRUENCE, COST HALF (pinned honestly): the lifted application
-- cell takes the enclosing cost comparison as an EXPLICIT hypothesis
-- (`congruenceCellInAppFunction`), and the pin witnesses the constructor
-- genuinely consumes it (`pinCostCongruenceIsNotFree`) — there is no shipped
-- lemma deriving the enclosing cost bound from the cell's sub-bound.
#assert_no_axioms FX1Poly.Typed.OptimizationCell.congruenceCellInAppFunction
#assert_no_axioms FX1Poly.Typed.OptimizationCell.pinCostCongruenceIsNotFree

-- THE COMPOSITION DEMO: the OPT-0 β-rewrite demonstrator composed with an
-- identity cell, and with the universal normalizer, each staying STRICTLY
-- cost-decreasing (first-leg strictness propagation).
#assert_no_axioms FX1Poly.Typed.betaRewriteThenIdentity
#assert_no_axioms FX1Poly.Typed.betaRewriteThenIdentity_isStrict
#assert_no_axioms FX1Poly.Typed.betaRewriteThenNormalize
#assert_no_axioms FX1Poly.Typed.betaRewriteThenNormalize_isStrict

-- THE VERDICT / COVERAGE LEDGER: status enum + Bool classifiers + the
-- ledger list + the kernel-computed count pin (9 cells: 8 proven, 1
-- pinned-conditional) + the capstone backing witness.
#assert_no_axioms FX1Poly.Typed.OptimizationCellCategoryStatus.isProvenB
#assert_no_axioms FX1Poly.Typed.OptimizationCellCategoryStatus.isPinnedB
#assert_no_axioms FX1Poly.Typed.optimizationCellCategoryLedger
#assert_no_axioms FX1Poly.Typed.optimizationCellCategoryLedger_counts
#assert_no_axioms FX1Poly.Typed.optimizationCellCategory_isBacked
