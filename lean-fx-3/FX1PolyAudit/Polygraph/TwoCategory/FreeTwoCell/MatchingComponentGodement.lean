import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.MatchingComponentGodement

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/MatchingComponentGodement — zero-axiom gate

Per-declaration zero-axiom gate for the freshness-conditioned component-level Godement chain: the
reachable-state conditions package with its initial / step / spine / cell instances, the corrected residual
chain Props with their reductions, the conditioned Godement-step invariance, the re-gated trace induction,
the soundness packagings, and the two honesty markers.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Tier0.MatchingSwapStateConditions
#assert_no_axioms FX1Poly.Tier0.matchingSwapStateConditions_initial
#assert_no_axioms FX1Poly.Tier0.matchingSwapStateConditions_stepAtom
#assert_no_axioms FX1Poly.Tier0.matchingSwapStateConditions_processSpine
#assert_no_axioms FX1Poly.Tier0.matchingSwapStateConditions_runMatchingCell
#assert_no_axioms FX1Poly.Tier0.MatchingGodementComponentCoreSwap
#assert_no_axioms FX1Poly.Tier0.MatchingGodementComponentSwapRenameable
#assert_no_axioms FX1Poly.Tier0.matchingGodementComponentSwapRenameable_of_coreSwap
#assert_no_axioms FX1Poly.Tier0.MatchingGodementComponentCommute
#assert_no_axioms FX1Poly.Tier0.matchingGodementComponentCommute_of_swapRenameable
#assert_no_axioms FX1Poly.Tier0.matchingGodementInvariant_of_componentCommute
#assert_no_axioms FX1Poly.Tier0.traceInvariant_of_conditionedGodementInvariant
#assert_no_axioms FX1Poly.Tier0.matchingOf_sound_of_conditionedGodementInvariant
#assert_no_axioms FX1Poly.Tier0.matchingOf_sound_of_componentCoreSwap
#assert_no_axioms FX1Poly.Tier0.fxMode_hasMatchingComponentGodementChain
#assert_no_axioms FX1Poly.Tier0.fxMode_hasMatchingComponentCoreSwapWitness

end FX1PolyAudit
