import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFlatReading

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutFlatReading — zero-axiom gate (WP-AMALG)

Per-declaration zero-axiom gate for the run reading structure with its transports, the id/gen arms, the flat identity collapse, and the head-absorption engines.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.
Registered in `AuditAll` (paired with the independent `#print axioms` witness). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.RunReading
#assert_no_axioms FX1Poly.Polygraph.Amalgam.RunReading.mapConv
#assert_no_axioms FX1Poly.Polygraph.Amalgam.RunReading.castTransport
#assert_no_axioms FX1Poly.Polygraph.Amalgam.allRunsWallFree_head
#assert_no_axioms FX1Poly.Polygraph.Amalgam.allRunsWallFree_tail
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idSlotsOfRuns
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idSlotsOfRuns_gapDom
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idSlotsOfRuns_gapCod
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idHeadSlot
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idSlots_flatDom_eq_flatCod
#assert_no_axioms FX1Poly.Polygraph.Amalgam.flatIdCollapse
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idSlots_flatDom
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idSlots_flatCod
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idConvOfCollapse
#assert_no_axioms FX1Poly.Polygraph.Amalgam.idReading
#assert_no_axioms FX1Poly.Polygraph.Amalgam.genSourceWallFree
#assert_no_axioms FX1Poly.Polygraph.Amalgam.genTargetWallFree
#assert_no_axioms FX1Poly.Polygraph.Amalgam.genReading
#assert_no_axioms FX1Poly.Polygraph.Amalgam.hcompIdNilLeftConv
#assert_no_axioms FX1Poly.Polygraph.Amalgam.whiskerLeftHcompFuse
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasFlatReadingBaseArms

end FX1PolyAudit
