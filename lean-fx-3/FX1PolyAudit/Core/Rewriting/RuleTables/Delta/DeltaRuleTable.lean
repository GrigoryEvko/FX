import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Rewriting.RuleTables.Delta.DeltaRuleTable

/-! # FX1PolyAudit.Core.Rewriting.RuleTables.Delta.DeltaRuleTable

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Rewriting.RuleTables.Delta.DeltaRuleTable`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.RawTerm.weakenClosed

#assert_no_axioms FX1Poly.Core.RawTerm.weakenClosed_zero

#assert_no_axioms FX1Poly.Core.DeltaRuleDesc

#assert_no_axioms FX1Poly.Core.unitDefiniens

#assert_no_axioms FX1Poly.Core.hyperrealDefiniens

#assert_no_axioms FX1Poly.Core.hyperrealDeltaRow

#assert_no_axioms FX1Poly.Core.qubitDeltaRow

#assert_no_axioms FX1Poly.Core.deltaRuleTable

#assert_no_axioms FX1Poly.Core.deltaRuleTable_length

#assert_no_axioms FX1Poly.Core.StepDeltaOverTable

#assert_no_axioms FX1Poly.Core.StepDeltaOverTableChildren

#assert_no_axioms FX1Poly.Core.StepDeltaTable

#assert_no_axioms FX1Poly.Core.StepDeltaOverTable.monotone

#assert_no_axioms FX1Poly.Core.StepDeltaOverTableChildren.monotone

#assert_no_axioms FX1Poly.Core.StepDeltaOverTable.invertOrCong

#assert_no_axioms FX1Poly.Core.hyperrealDeltaRow_memTable

#assert_no_axioms FX1Poly.Core.qubitDeltaRow_memTable

#assert_no_axioms FX1Poly.Core.hyperrealDeltaRow_fires

#assert_no_axioms FX1Poly.Core.qubitDeltaRow_fires

#assert_no_axioms FX1Poly.Core.StepDeltaOverTable.invert_headNotConstant

#assert_no_axioms FX1Poly.Core.unitValue_noDeltaStep

#assert_no_axioms FX1Poly.Core.stepDeltaTable_congSmoke

#assert_no_axioms FX1Poly.Core.DeltaRuleDesc.tableConstantHeads

#assert_no_axioms FX1Poly.Core.RawTerm.deltaConstantCount

#assert_no_axioms FX1Poly.Core.RawTermChildren.deltaConstantCount

#assert_no_axioms FX1Poly.Core.deltaConstantCount_hyperrealCell

#assert_no_axioms FX1Poly.Core.deltaConstantCount_unitDefiniens

#assert_no_axioms FX1Poly.Core.hyperrealDeltaStep_strictlyDecreasesCount

#assert_no_axioms FX1Poly.Core.DeltaRuleDesc.hasDeltaFreeDefiniens

#assert_no_axioms FX1Poly.Core.deltaTableIsAcyclic

#assert_no_axioms FX1Poly.Core.hyperrealSubTable_isAcyclic

#assert_no_axioms FX1Poly.Core.deltaRuleTable_isNotAcyclic

#assert_no_axioms FX1Poly.Core.StepDeltaStarOverTable

#assert_no_axioms FX1Poly.Core.StepDeltaStar

#assert_no_axioms FX1Poly.Core.StepDeltaStarOverTable.ofStep

#assert_no_axioms FX1Poly.Core.qubitDeltaStar_reachesUnit

#assert_no_axioms FX1Poly.Core.unitValue_deltaStarIsRefl

end FX1PolyAudit
