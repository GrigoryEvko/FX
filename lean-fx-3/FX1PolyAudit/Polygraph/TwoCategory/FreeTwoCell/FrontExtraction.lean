import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.FrontExtraction

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/FrontExtraction — zero-axiom gate

Per-declaration zero-axiom gate for the trace-length invariance and the certified
front-extraction enumeration.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.AtomicTraceEquiv.lengthEq
#assert_no_axioms FX1Poly.Polygraph.FrontExtraction.lengthEq
#assert_no_axioms FX1Poly.Polygraph.frontExtractions

end FX1PolyAudit
