import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Brauer.WiringDescCrossingInvolution

/-! # FX1PolyAudit.Polygraph.TwoCategory.Brauer.WiringDescCrossingInvolution — zero-axiom gate (KEYSTONE12 ingredient)

Per-declaration zero-axiom gate for the R2 net-identity port reconnection: the prefix-take helper
(`natListSliceAt_prefixAll`), the same-position splice surgery (`natListSliceAt_spliceSame`), the second-crossing
input identification (`stepWiring_crossing_secondInputs`), the two-crossing net-identity reconnection
(`stepWiring_crossing_involution_reconnects`), and the honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.natListSliceAt_prefixAll
#assert_no_axioms FX1Poly.Polygraph.natListSliceAt_spliceSame
#assert_no_axioms FX1Poly.Polygraph.stepWiring_crossing_secondInputs
#assert_no_axioms FX1Poly.Polygraph.stepWiring_crossing_involution_reconnects

#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasSamePositionSpliceSurgery
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCrossingInvolutionReconnection
#assert_no_axioms FX1Poly.Polygraph.fxBrauer_hasCrossingInvolutionReconnectionFlipsSoundness

end FX1PolyAudit
