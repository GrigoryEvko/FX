import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescPortReconnection

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescPortReconnection — zero-axiom gate (KEYSTONE11 ingredient)

Per-declaration zero-axiom gate for the PORT-RECONNECTION ingredient + the whisker assembly bridge: the second-
endpoint single-join converse (`isSameComponent_unionFindJoin_eq_ofSecondDisconnected`), the crossing's transposition
reconnection at the links level (`stepWiring_crossing_reconnects`), the `relationAgrees` extraction
(`relationAgrees_of_matchingComponentRenameRel`), the `BrauerConv` bridge
(`brauerConv_of_matchingComponentRenameRel`), and the honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.isSameComponent_unionFindJoin_eq_ofSecondDisconnected
#assert_no_axioms FX1Poly.Polygraph.stepWiring_crossing_reconnects
#assert_no_axioms FX1Poly.Polygraph.relationAgrees_of_matchingComponentRenameRel
#assert_no_axioms FX1Poly.Polygraph.brauerConv_of_matchingComponentRenameRel

#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasSecondEndpointJoinConverse
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCrossingPortReconnection
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasPortReconnectionAssemblyBridge
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasBrauerSoundnessPortReconnectionResidual

end FX1PolyAudit
