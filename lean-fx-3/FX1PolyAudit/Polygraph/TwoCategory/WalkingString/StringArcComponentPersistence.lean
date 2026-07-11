import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringArcComponentPersistence

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringArcComponentPersistence — zero-axiom gate
(FC-3 r19, THE CAP-HEAD DISCHARGE PORT — LOCATE substrate)

Per-declaration zero-axiom gate for the ported component-persistence set: whole-spine persistence and the four
folded head-seed joins (cup event-to-leg / leg pair, cap event-to-wire / consumed pair).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringIsSameComponent_processArcSpine_ofBase
#assert_no_axioms FX1Poly.Polygraph.stringArcCupHeadFolded_eventLegLinked
#assert_no_axioms FX1Poly.Polygraph.stringArcCupHeadFolded_legsLinked
#assert_no_axioms FX1Poly.Polygraph.stringArcCapHeadFolded_eventWireLinked
#assert_no_axioms FX1Poly.Polygraph.stringArcCapHeadFolded_consumedPairLinked
#assert_no_axioms FX1Poly.Polygraph.fxString_hasArcComponentPersistence

end FX1PolyAudit
