import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.StepOverBundleConv

/-! # FX1PolyAudit/AuditStepOverBundleConv — RW-6 (b) audit shard

Per-declaration zero-axiom gate for the no-regression decidable
conversion: the closure-level bridge, `ConvOver`, the iff against raw
`Conv`, the NF-witnessed decider, and the SN-fragment decider that runs
the normalizer to supply those witnesses.  Free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.reflTransClosure_fxIotaBundle_iff_stepStar
#assert_no_axioms FX1Poly.Core.ConvOver
#assert_no_axioms FX1Poly.Core.convOver_fxIotaBundle_iff_conv
#assert_no_axioms FX1Poly.Core.Conv.decidableOverFxIotaBundleOfNormalForms
#assert_no_axioms FX1Poly.Core.Conv.decidableOverFxIotaBundleOfStronglyNormalizing

end FX1PolyAudit
