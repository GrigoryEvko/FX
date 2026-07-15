import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFlatVcompZip

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutFlatVcompZip — zero-axiom gate (WP-AMALG)

Per-declaration zero-axiom gate for the vcomp payload zip, the vcomp arm, and the total flat reader over all five constructors.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.
Registered in `AuditAll` (paired with the independent `#print axioms` witness). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.castBoundary_hcomp_distribute
#assert_no_axioms FX1Poly.Polygraph.Amalgam.vcomp_castBoundary_merge
#assert_no_axioms FX1Poly.Polygraph.Amalgam.consAlign_head
#assert_no_axioms FX1Poly.Polygraph.Amalgam.consAlign_tail
#assert_no_axioms FX1Poly.Polygraph.Amalgam.SaturatedConvOver.ofCellEq
#assert_no_axioms FX1Poly.Polygraph.Amalgam.RunReading.cellEqTransport
#assert_no_axioms FX1Poly.Polygraph.Amalgam.zipHeadSlot
#assert_no_axioms FX1Poly.Polygraph.Amalgam.zipTailSlots
#assert_no_axioms FX1Poly.Polygraph.Amalgam.zipTailSlots_gapDom
#assert_no_axioms FX1Poly.Polygraph.Amalgam.zipTailSlots_gapCod
#assert_no_axioms FX1Poly.Polygraph.Amalgam.flatAlignEq
#assert_no_axioms FX1Poly.Polygraph.Amalgam.zipReading
#assert_no_axioms FX1Poly.Polygraph.Amalgam.vcompReading
#assert_no_axioms FX1Poly.Polygraph.Amalgam.readCellFueled
#assert_no_axioms FX1Poly.Polygraph.Amalgam.readCellIntoSlots
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasVcompPayloadZip

end FX1PolyAudit
