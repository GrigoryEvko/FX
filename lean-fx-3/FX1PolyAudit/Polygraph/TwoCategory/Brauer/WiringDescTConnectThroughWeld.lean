import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescTConnectThroughWeld

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescTConnectThroughWeld — zero-axiom gate (BRAUER r28 THROUGH weld)

Per-declaration zero-axiom gate for the THROUGH five-phase node-survival weld: the shared post-cap width
(`capChainS2Width`), the P2 cap-survival read (`throughCapSurvival`), the P4 cup-survival read (`throughCupSurvival`),
their monster / 3-through firings, and the honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.capChainS2Width
#assert_no_axioms FX1Poly.Polygraph.throughCapSurvival
#assert_no_axioms FX1Poly.Polygraph.throughCupSurvival
#assert_no_axioms FX1Poly.Polygraph.throughCapSurvival_firesMonster
#assert_no_axioms FX1Poly.Polygraph.throughCapSurvival_firesThreeThrough
#assert_no_axioms FX1Poly.Polygraph.throughCupSurvival_firesMonster
#assert_no_axioms FX1Poly.Polygraph.throughCupSurvival_firesThreeThrough
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasThroughSurvivalSeams
#assert_no_axioms FX1Poly.Polygraph.cupChainS4Width
#assert_no_axioms FX1Poly.Polygraph.throughMiddleTracker
#assert_no_axioms FX1Poly.Polygraph.throughTopTracker
#assert_no_axioms FX1Poly.Polygraph.throughMiddleTracker_firesMonster
#assert_no_axioms FX1Poly.Polygraph.throughTopTracker_firesMonster
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasThroughTrackerSeams

end FX1PolyAudit
