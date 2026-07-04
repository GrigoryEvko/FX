import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.OrientedAtomSwap

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/OrientedAtomSwap — zero-axiom gate

Per-declaration zero-axiom gate for the keyed trace-vector measure, the lexicographic
prefix transport, the oriented atomic swap step with its soundness, the measure descent,
the termination theorem, and the honesty marker.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.spineTraceVector
#assert_no_axioms FX1Poly.Polygraph.lexListStep_prependTriple
#assert_no_axioms FX1Poly.Polygraph.OrientedAtomStep.toAtomicTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.OrientedAtomStep.decreasesTraceVector
#assert_no_axioms FX1Poly.Polygraph.orientedAtomStep_isTerminating
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasOrientedAtomSwapTermination

end FX1PolyAudit
