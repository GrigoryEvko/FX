import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.StepOverBundle

/-! # FX1PolyAudit/AuditStepOverBundle — RW-5 audit shard

Per-declaration zero-axiom gate for the ONE parameterized reduction
relation `StepOver` over a `RuleTableBundle`: the relation + its spine
companion, monotonicity, freed-subject inversion, both adequacy
directions (iota-only ↔ `StepOverTable`, eta-only ↔ `StepEtaOverTable`),
the core-`Step` pin, and the βιη liveness pins on `fxBundle`.  Every
declaration must be free of `propext`, `Quot.sound`, `Classical.choice`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

/-! ## The bundle + relation -/

#assert_no_axioms FX1Poly.Core.RuleTableBundle
#assert_no_axioms FX1Poly.Core.StepOver
#assert_no_axioms FX1Poly.Core.StepOverChildren
#assert_no_axioms FX1Poly.Core.fxIotaBundle
#assert_no_axioms FX1Poly.Core.fxBundle

/-! ## Monotonicity + inversion -/

#assert_no_axioms FX1Poly.Core.StepOver.monotone
#assert_no_axioms FX1Poly.Core.StepOverChildren.monotone
#assert_no_axioms FX1Poly.Core.StepOver.invertOrCong

/-! ## Adequacy 1 — iota-only bundle ↔ iota table -/

#assert_no_axioms FX1Poly.Core.StepOver.toStepOverTable_iotaOnly
#assert_no_axioms FX1Poly.Core.StepOverChildren.toStepOverTableChildren_iotaOnly
#assert_no_axioms FX1Poly.Core.StepOverTable.toStepOver_iotaOnly
#assert_no_axioms FX1Poly.Core.StepOverTableChildren.toStepOverChildren_iotaOnly
#assert_no_axioms FX1Poly.Core.stepOver_iotaOnly_iff_stepOverTable

/-! ## Adequacy 2 — eta-only bundle ↔ eta table -/

#assert_no_axioms FX1Poly.Core.StepOver.toStepEtaOverTable_etaOnly
#assert_no_axioms FX1Poly.Core.StepOverChildren.toStepEtaOverTableChildren_etaOnly
#assert_no_axioms FX1Poly.Core.StepEtaOverTable.toStepOver_etaOnly
#assert_no_axioms FX1Poly.Core.StepEtaOverTableChildren.toStepOverChildren_etaOnly
#assert_no_axioms FX1Poly.Core.stepOver_etaOnly_iff_stepEtaOverTable

/-! ## The core-Step pin -/

#assert_no_axioms FX1Poly.Core.step_iff_stepOver_fxIotaBundle

/-! ## βιη liveness on fxBundle -/

#assert_no_axioms FX1Poly.Core.StepOver.fxBundlePathBetaFires
#assert_no_axioms FX1Poly.Core.StepOver.fxBundleEtaLamFires
#assert_no_axioms FX1Poly.Core.StepOver.fxBundleEtaPairFires

end FX1PolyAudit
