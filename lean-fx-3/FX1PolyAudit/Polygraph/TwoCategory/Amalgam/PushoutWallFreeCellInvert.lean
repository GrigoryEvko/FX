import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutWallFreeCellInvert

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutWallFreeCellInvert — zero-axiom gate for the wall-free CELL
converse `wallFreeCellInvert` (the generator reseat crux + the four-case structural recursion, WP-AMALG-2 r12)

Per-declaration zero-axiom gate for the monad singleton, the 2-generator retract and its get-alignment, the
interpreter converse, the generator reseat crux, and the truth probes.

Every declaration below must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`,
`omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadModeUnique
#assert_no_axioms FX1Poly.Polygraph.Amalgam.retractRightTwoGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.embedRight_retractRight
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutGetRetract
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutGetLhsWord
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutGetRhsWord
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadInterpOfPushoutInterp
#assert_no_axioms FX1Poly.Polygraph.Amalgam.wallFreeGenInvert
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutMonadMult
#assert_no_axioms FX1Poly.Polygraph.Amalgam.wallFreeGenInvert_unit_index
#assert_no_axioms FX1Poly.Polygraph.Amalgam.wallFreeGenInvert_mult_index

end FX1PolyAudit
