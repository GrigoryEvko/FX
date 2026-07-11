import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringDispatcherConcreteFiring

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringDispatcherConcreteFiring — zero-axiom gate (FC-3 r13, B4)

Per-declaration zero-axiom gate for the case-(a) dispatcher concrete firing
(`stringCaseADispatcher_firesOnConcreteValleyPair`) and the marker.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringCaseADispatcher_firesOnConcreteValleyPair
#assert_no_axioms FX1Poly.Polygraph.fxString_hasDispatcherConcreteFiring

end FX1PolyAudit
