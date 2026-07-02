import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationBridge

/-! # FX1PolyAudit/Core/Metatheory/Normalization/StrongNorm/StrongNormalizationBridge — zero-axiom gate

Per-declaration zero-axiom gate for the headline F1 bridge: the `reductWitnessOperator`, the two
directions of the SN coincidence plus the `↔`
(`inductiveClosure_reductWitnessOperator_iff_isStronglyNormalizing` — strong normalization IS the
inductive fixpoint), and the reducibility-candidate-on-the-coinductive-side lemmas.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega` — in particular the `Acc`-recursion in the backward direction must not leak `propext`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Invertibility.reductWitnessOperator
#assert_no_axioms FX1Poly.Polygraph.Invertibility.isStronglyNormalizing_of_inductiveClosure
#assert_no_axioms FX1Poly.Polygraph.Invertibility.inductiveClosure_of_isStronglyNormalizing
#assert_no_axioms FX1Poly.Polygraph.Invertibility.inductiveClosure_reductWitnessOperator_iff_isStronglyNormalizing
#assert_no_axioms FX1Poly.Polygraph.Invertibility.reducibilityCandidate_isPostFixed_reductWitnessOperator
#assert_no_axioms FX1Poly.Polygraph.Invertibility.reducibilityCandidate_subset_coinductiveClosure
#assert_no_axioms FX1Poly.Polygraph.Invertibility.reductWitnessOperator_applyFromGuard
#assert_no_axioms FX1Poly.Polygraph.Invertibility.coinductiveClosure_reductWitnessOperator_collapses_of_wellFounded

end FX1PolyAudit
