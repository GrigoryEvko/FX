import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Context.Context

/-! # FX1PolyAudit/AuditAxisContextRoot — zero-axiom gate for the context-0 axis root

Per-declaration zero-axiom gate for the `context-0` design-lock
(`FX1Poly/Axis/Context/Context.lean`): the abstract mode interface, the raw
endofunctor lock-slot vehicle, the `ContextAxis` bundle, and the L0 witness
`fxContextAxis` wiring the shipped renaming RMC + substitution category + both
global-sections functors.  Every declaration below must be free of `propext`,
`Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Axis.RawEndofunctor.identity
#assert_no_axioms FX1Poly.Axis.trivialMode
#assert_no_axioms FX1Poly.Axis.fxContextAxis
#assert_no_axioms FX1Poly.Axis.fxContextAxis_renamingMode
#assert_no_axioms FX1Poly.Axis.fxContextAxis_substMode
#assert_no_axioms FX1Poly.Axis.fxContextAxis_fireTriangleLeg
#assert_no_axioms FX1Poly.Axis.fxContextAxis_trivialLock_isIdentity

end FX1PolyAudit
