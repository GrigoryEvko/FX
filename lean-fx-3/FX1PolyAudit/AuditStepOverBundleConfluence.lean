import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.StepOverBundleConfluence

/-! # FX1PolyAudit/AuditStepOverBundleConfluence — RW-6 (a) audit shard

Per-declaration zero-axiom gate for the no-regression confluence
transport: the generic relation-iff helpers and the iota-only-bundle
confluence headline.  Free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.ReflTransClosure.mapForward
#assert_no_axioms FX1Poly.Core.Confluent.ofRelIff
#assert_no_axioms FX1Poly.Core.StepOver.fxIotaBundleConfluent

end FX1PolyAudit
