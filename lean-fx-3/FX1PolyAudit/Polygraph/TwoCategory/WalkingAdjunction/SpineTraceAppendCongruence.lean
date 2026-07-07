import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.SpineTraceAppendCongruence

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/SpineTraceAppendCongruence — zero-axiom gate

Per-declaration zero-axiom gate for the two-sided append congruence of the trace equivalence: the
list-suffix atomic back-append, its block-level image, the list prefix congruence, and the two-sided
combination.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.atomicTraceEquiv_backAppendListCongr
#assert_no_axioms FX1Poly.Polygraph.spineTraceEquiv_backAppendListCongr
#assert_no_axioms FX1Poly.Polygraph.spineTraceEquiv_prefixListCongr
#assert_no_axioms FX1Poly.Polygraph.spineTraceEquiv_appendCongr

end FX1PolyAudit
