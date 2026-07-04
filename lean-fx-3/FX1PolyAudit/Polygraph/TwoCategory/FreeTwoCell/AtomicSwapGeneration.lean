import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.AtomicSwapGeneration

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/AtomicSwapGeneration — zero-axiom gate

Per-declaration zero-axiom gate for the block move, the Godement step's atomicity, the
trace-equivalence inclusion, and the closure identification.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.AtomicTraceEquiv.blockMovePastCell
#assert_no_axioms FX1Poly.Polygraph.SpineGodementStep.toAtomicTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.SpineTraceEquiv.toAtomicTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.spineTraceEquiv_iff_atomicTraceEquiv

end FX1PolyAudit
