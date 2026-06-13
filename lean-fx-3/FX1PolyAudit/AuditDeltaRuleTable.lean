import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.DeltaRuleTable

/-! # FX1PolyAudit/AuditDeltaRuleTable — RW-4 audit shard

Per-declaration zero-axiom gate for the δ-rule (defined-constant
unfolding) schema: the `weakenClosed` closed-term re-instantiation
engine with its scope-0 identity pin, the `DeltaRuleDesc` descriptor,
the two smoke rows and the table with its length guard, the standalone
`StepDeltaOverTable` relation with its uniform child congruence, the
monotonicity pair, the freed-subject inversion, the row memberships,
the per-row firing pins, and the conservativity facts (the generic
head-not-a-constant inversion + the closed δ-free `unit` no-step +
the congruence non-vacuity smoke).  Every declaration below must be
free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## The closed-term weakening engine -/

#assert_no_axioms FX1Poly.Core.RawTerm.weakenClosed
#assert_no_axioms FX1Poly.Core.RawTerm.weakenClosed_zero

/-! ## The descriptor + smoke table -/

#assert_no_axioms FX1Poly.Core.DeltaRuleDesc
#assert_no_axioms FX1Poly.Core.unitDefiniens
#assert_no_axioms FX1Poly.Core.hyperrealDefiniens
#assert_no_axioms FX1Poly.Core.hyperrealDeltaRow
#assert_no_axioms FX1Poly.Core.qubitDeltaRow
#assert_no_axioms FX1Poly.Core.deltaRuleTable
#assert_no_axioms FX1Poly.Core.deltaRuleTable_length

/-! ## The standalone relation -/

#assert_no_axioms FX1Poly.Core.StepDeltaOverTable
#assert_no_axioms FX1Poly.Core.StepDeltaOverTableChildren
#assert_no_axioms FX1Poly.Core.StepDeltaTable

/-! ## Monotonicity + inversion -/

#assert_no_axioms FX1Poly.Core.StepDeltaOverTable.monotone
#assert_no_axioms FX1Poly.Core.StepDeltaOverTableChildren.monotone
#assert_no_axioms FX1Poly.Core.StepDeltaOverTable.invertOrCong

/-! ## Row memberships + firing pins -/

#assert_no_axioms FX1Poly.Core.hyperrealDeltaRow_memTable
#assert_no_axioms FX1Poly.Core.qubitDeltaRow_memTable
#assert_no_axioms FX1Poly.Core.hyperrealDeltaRow_fires
#assert_no_axioms FX1Poly.Core.qubitDeltaRow_fires

/-! ## Conservativity + non-vacuity -/

#assert_no_axioms FX1Poly.Core.StepDeltaOverTable.invert_headNotConstant
#assert_no_axioms FX1Poly.Core.unitValue_noDeltaStep
#assert_no_axioms FX1Poly.Core.stepDeltaTable_congSmoke

/-! ## The δ-constant-occurrence measure + the acyclicity tier -/

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

/-! ## The δ multi-step relation -/

#assert_no_axioms FX1Poly.Core.StepDeltaStarOverTable
#assert_no_axioms FX1Poly.Core.StepDeltaStar
#assert_no_axioms FX1Poly.Core.StepDeltaStarOverTable.ofStep
#assert_no_axioms FX1Poly.Core.qubitDeltaStar_reachesUnit
#assert_no_axioms FX1Poly.Core.unitValue_deltaStarIsRefl

end FX1PolyAudit
