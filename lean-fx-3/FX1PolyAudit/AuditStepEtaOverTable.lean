import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.StepEtaOverTable

/-! # FX1PolyAudit/AuditStepEtaOverTable — ETA-T1 audit shard
(increment A)

Per-declaration zero-axiom gate for the table-driven eta relation, its
monotonicity and freed-subject inversion, the row memberships, the
symbolic contraction equations, the forward relation arms, the gating
STRICTNESS ledger (bespoke fires raw / table refuses), and the
congruence smoke.  Every declaration below must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## The relation + monotonicity + inversion -/

#assert_no_axioms FX1Poly.Core.StepEtaOverTable
#assert_no_axioms FX1Poly.Core.StepEtaOverTableChildren
#assert_no_axioms FX1Poly.Core.StepEtaOverTable.monotone
#assert_no_axioms FX1Poly.Core.StepEtaOverTableChildren.monotone
#assert_no_axioms FX1Poly.Core.StepEtaOverTable.invertOrCong

/-! ## Row memberships -/

#assert_no_axioms FX1Poly.Core.etaLamRow_memTable
#assert_no_axioms FX1Poly.Core.etaPairRow_memTable
#assert_no_axioms FX1Poly.Core.etaPathLamRow_memTable
#assert_no_axioms FX1Poly.Core.etaModIntroRow_memTable
#assert_no_axioms FX1Poly.Core.etaGlueIntroRow_memTable

/-! ## The symbolic contraction equations -/

#assert_no_axioms FX1Poly.Core.etaLamRow_contractsOnSource
#assert_no_axioms FX1Poly.Core.etaPathLamRow_contractsOnSource
#assert_no_axioms FX1Poly.Core.etaPairRow_contractsOnSource

/-! ## The forward relation arms -/

#assert_no_axioms FX1Poly.Core.Step.eta.etaLamToTableStep
#assert_no_axioms FX1Poly.Core.Step.eta.etaPairToTableStep
#assert_no_axioms FX1Poly.Core.Step.eta.etaPathLamToTableStep

/-! ## The gating STRICTNESS ledger -/

#assert_no_axioms FX1Poly.Core.etaModIntro_bespokeFiresRaw
#assert_no_axioms FX1Poly.Core.etaModIntro_tableRefusesRaw
#assert_no_axioms FX1Poly.Core.etaGlueIntro_bespokeFiresRaw
#assert_no_axioms FX1Poly.Core.etaGlueIntro_tableRefusesRaw

/-! ## Non-vacuity -/

#assert_no_axioms FX1Poly.Core.stepEtaTable_congSmoke

end FX1PolyAudit
