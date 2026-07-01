import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Rewriting.Confluence.KnuthBendixCompletion

/-! # FX1PolyAudit.Polygraph.Rewriting.Confluence.KnuthBendixCompletion

Zero-axiom audit shard mirroring kernel module `FX1Poly.Polygraph.Rewriting.Confluence.KnuthBendixCompletion`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Knuth-Bendix: the convergence criterion + orientation soundness (KnuthBendixCompletion.lean), the
-- abstract core that justifies completion.  EquationalTheory (⟷*, the equivalence closure) +
-- churchRosser_of_confluent (CONFLUENT ⟹ ⟷* = joinability, the Church-Rosser theorem) +
-- knuthBendixConvergenceCriterion (terminating + locally confluent ⟹ decides the theory, via newman) +
-- equationalTheory_orientationInvariant (orienting preserves the theory — completion soundness) +
-- the one-rule {true↦false} non-vacuity witness.  The completion PROCEDURE / fairness / term-level critical
-- pairs are NOT here (FX is orthogonal, needs no completion).  Zero-axiom (free-index inductive inductions).
#assert_no_axioms FX1Poly.Core.EquationalTheory

#assert_no_axioms FX1Poly.Core.EquationalTheory.ofReduction

#assert_no_axioms FX1Poly.Core.EquationalTheory.ofJoinable

#assert_no_axioms FX1Poly.Core.churchRosser_of_confluent

#assert_no_axioms FX1Poly.Core.knuthBendixConvergenceCriterion

#assert_no_axioms FX1Poly.Core.equationalTheory_orientationInvariant

#assert_no_axioms FX1Poly.Core.OneRuleStep

#assert_no_axioms FX1Poly.Core.oneRuleStep_terminating

#assert_no_axioms FX1Poly.Core.oneRuleStep_weaklyConfluent

#assert_no_axioms FX1Poly.Core.oneRuleConvergent

-- Knuth-Bendix PAYOFF: a convergent presentation DECIDES its word problem.  normalForm_blocks_reduction
-- (a normal form only reduces to itself) + ConvergentNormalizer (the NF function as data, since
-- WellFounded.fix can't build it zero-axiom) + joinable_iff (↓ = NF-equality, the 3-fold confluence) +
-- equationalTheory_iff (⟷* = NF-equality, the decision criterion) + normalize_isCanonical (unique NFs) +
-- decidableEquationalTheory + knuthBendixDecidesWordProblem (terminating + WCR + normalizer ⟹ Decidable).
#assert_no_axioms FX1Poly.Core.normalForm_blocks_reduction

#assert_no_axioms FX1Poly.Core.ConvergentNormalizer

#assert_no_axioms FX1Poly.Core.ConvergentNormalizer.joinable_iff

#assert_no_axioms FX1Poly.Core.ConvergentNormalizer.equationalTheory_iff

#assert_no_axioms FX1Poly.Core.ConvergentNormalizer.normalize_isCanonical

#assert_no_axioms FX1Poly.Core.ConvergentNormalizer.decidableEquationalTheory

#assert_no_axioms FX1Poly.Core.knuthBendixDecidesWordProblem

end FX1PolyAudit
