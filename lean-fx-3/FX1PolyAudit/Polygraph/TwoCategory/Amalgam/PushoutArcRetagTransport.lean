import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutArcRetagTransport

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutArcRetagTransport — zero-axiom gate (WP-AMALG)

Per-declaration zero-axiom gate for the arc retag transport: the cross-signature arc-step
congruence, the joint spine recursion, THE RETAG TRANSPORT (`runArcCell_mapCellAlong`), the
turnback-class functor-stability, and the double-adjunction fire.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.
Registered in `AuditAll` (paired with the independent `#print axioms` witness). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.stepArcAtom_crossSignatureCongr
#assert_no_axioms FX1Poly.Polygraph.Amalgam.processArcSpine_mapCellAlong
#assert_no_axioms FX1Poly.Polygraph.Amalgam.runArcCell_mapCellAlong
#assert_no_axioms FX1Poly.Polygraph.Amalgam.isTurnbackOnly_castBoundary
#assert_no_axioms FX1Poly.Polygraph.Amalgam.isTurnbackOnly_mapCellAlong
#assert_no_axioms FX1Poly.Polygraph.Amalgam.adjunctionComputadBaseMode
#assert_no_axioms FX1Poly.Polygraph.Amalgam.adjunctionComputadNilBase
#assert_no_axioms FX1Poly.Polygraph.Amalgam.adjunctionComputadUnitCupCell
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arcRetagFireSeed
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arcRetagTransport_firedOnDoubleAdjunction
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arcRetagTransport_fireData
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasPushoutArcRetagTransport

end FX1PolyAudit
