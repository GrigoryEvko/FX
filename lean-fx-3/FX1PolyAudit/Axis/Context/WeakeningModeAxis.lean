import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Context.WeakeningModeAxis

/-! # FX1PolyAudit.Axis.Context.WeakeningModeAxis — zero-axiom gate (fib-3 #3)

Per-declaration zero-axiom gate for the first NON-trivial `ContextAxis.lockOn` instantiation: the weakening mode
theory, the weakening context axis, and the wiring / non-triviality theorems certifying the abstract lock slot
carries the real weakening endofunctor `A ↦ A + K`.  Must be free of `propext`, `Quot.sound`, `Classical`,
`sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Axis.weakeningModeData
#assert_no_axioms FX1Poly.Axis.fxWeakeningContextAxis
#assert_no_axioms FX1Poly.Axis.fxWeakeningContextAxis_substMode
#assert_no_axioms FX1Poly.Axis.fxWeakeningContextAxis_fireTriangleLeg
#assert_no_axioms FX1Poly.Axis.fxWeakeningContextAxis_lockOn_eq_weakeningLock
#assert_no_axioms FX1Poly.Axis.fxWeakeningContextAxis_lockOn_id_eq_weakeningLockZero
#assert_no_axioms FX1Poly.Axis.fxWeakeningContextAxis_lockOn_mapObject
#assert_no_axioms FX1Poly.Axis.fxWeakeningContextAxis_lockOn_one_isNonTrivial

end FX1PolyAudit
