import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcCupDropAndAppend

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcCupDropAndAppend — zero-axiom gate

Per-declaration zero-axiom gate for the back-append congruence of the trace equivalence: the
atomic-granularity back-append and its block-level image.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.atomicTraceEquiv_backAppendCongr
#assert_no_axioms FX1Poly.Polygraph.spineTraceEquiv_backAppendCongr

end FX1PolyAudit
