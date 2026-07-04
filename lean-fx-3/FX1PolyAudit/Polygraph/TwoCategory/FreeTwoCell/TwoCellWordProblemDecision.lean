import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.TwoCellWordProblemDecision

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/TwoCellWordProblemDecision — zero-axiom gate

Per-declaration zero-axiom gate for the FREE 2-cell word-problem decision: the composed
characterization, the gated and Option-valued deciders, and the cell-level canonical
trace invariance.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.twoCellConvFull_iff_atomicTraceEquiv
#assert_no_axioms FX1Poly.Polygraph.decideTwoCellConvFullViaSaturation
#assert_no_axioms FX1Poly.Polygraph.decideTwoCellConvFull?
#assert_no_axioms FX1Poly.Polygraph.cellCanonicalTrace_isConvInvariant

end FX1PolyAudit
