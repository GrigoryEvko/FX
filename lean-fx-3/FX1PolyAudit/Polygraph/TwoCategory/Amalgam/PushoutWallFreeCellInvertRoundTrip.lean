import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWallFreeCellInvertRoundTrip

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutWallFreeCellInvertRoundTrip — zero-axiom gate for the
wall-free CELL converse's BACKWARD round-trip (`mapCellAlong inclRight ∘ wallFreeCellInvert = castBoundary .. cell`,
the fuel assembly + the two cast-fusion step theorems + the gen full round-trip + the dim-2 bijection, WP-AMALG-2 r13)

Per-declaration zero-axiom gate for the pushout gen transport cast, the double-transport index lemma, the gen-case
full round-trip, the two whisker cast-fusion step theorems, the cell-size fuel assembly and its instantiation, the
four truth probes, and the dim-2 bijection.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutGenTransportCast
#assert_no_axioms FX1Poly.Polygraph.Amalgam.reconTwoCellPushout_doubleTransport_val
#assert_no_axioms FX1Poly.Polygraph.Amalgam.wallFreeGenInvert_onTwoCell_full
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mapCellAlongWallFreeInvertWhiskerLeftStep
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mapCellAlongWallFreeInvertWhiskerRightStep
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mapCellAlongWallFreeInvertFueled
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mapCellAlong_inclRight_wallFreeCellInvert
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mapCellAlongWallFreeInvert_whiskerLeftProbe
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mapCellAlongWallFreeInvert_whiskerRightProbe
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mapCellAlongWallFreeInvert_vcompProbe
#assert_no_axioms FX1Poly.Polygraph.Amalgam.mapCellAlongWallFreeInvert_unitProbe
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutCellRoundTripBijection
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasCellConverseBackwardRoundTrip

end FX1PolyAudit
