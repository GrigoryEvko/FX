import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingAdjunction.ArcPairSeatedDescent

/-! # FX1PolyAudit/Polygraph/TwoCategory/WalkingAdjunction/ArcPairSeatedDescent — zero-axiom gate

Per-declaration zero-axiom gate for the backward seating descent: an adjacent seed-port
pair after one arc step was adjacent before it, with the cup's splice-into-seat case
killed by freshness and the cap's gap-closing case killed by tip/base parity.

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.ArcPairSeated
#assert_no_axioms FX1Poly.Polygraph.arcPairSeated_beforeCupStep
#assert_no_axioms FX1Poly.Polygraph.arcPairSeated_beforeCapStep
#assert_no_axioms FX1Poly.Polygraph.arcPairSeated_beforeCapStep_ofTipParities
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasArcPairSeatedDescent

end FX1PolyAudit
