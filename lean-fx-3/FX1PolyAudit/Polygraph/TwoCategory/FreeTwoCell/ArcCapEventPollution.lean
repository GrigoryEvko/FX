import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcCapEventPollution

/-! # FX1PolyAudit/Polygraph/TwoCategory/FreeTwoCell/ArcCapEventPollution — zero-axiom gate

Per-declaration zero-axiom gate for the cap-event pollution substrate: cap-event membership
monotonicity through the fold, the cap's own recorded event, the cap's two component joins,
the one- and two-event count bounds, and the partner pin reader.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.mem_capEventNodes_stepArcAtom
#assert_no_axioms FX1Poly.Polygraph.mem_capEventNodes_processArcSpine
#assert_no_axioms FX1Poly.Polygraph.stepCapArc_newEventMem
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_stepCapArc_eventFirstRead
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_stepCapArc_consumedReads
#assert_no_axioms FX1Poly.Polygraph.countEventsInRoot_ge_one_ofMember
#assert_no_axioms FX1Poly.Polygraph.countEventsInRoot_ge_two_ofDistinctMembers
#assert_no_axioms FX1Poly.Polygraph.isSameComponent_ofPartnerIndexOfHit
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcCapEventPollutionSubstrate

end FX1PolyAudit
