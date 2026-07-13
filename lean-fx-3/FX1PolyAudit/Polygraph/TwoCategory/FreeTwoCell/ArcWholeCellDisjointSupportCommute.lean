import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.FreeTwoCell.ArcWholeCellDisjointSupportCommute

/-! # FX1PolyAudit.Polygraph.TwoCategory.FreeTwoCell.ArcWholeCellDisjointSupportCommute — zero-axiom gate (MODE-COMMUTE r28)

Per-declaration zero-axiom gate for the r28 Godement-inner-shape packaging + four-pin
adjudication: the packaged whole-cell commutation, its cap-bearing fire, the `:234`
verbatim-shape refutation on gen cells with its byte-identity counterpart, the shipped marker,
and the five adjudication pins.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.
Registered in `AuditAll` (paired with the independent `#print axioms` witness). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.arcGodementInnerSwapSimCount
#assert_no_axioms FX1Poly.Polygraph.arcGodementInnerSwap_firedOnCounitInstance
#assert_no_axioms FX1Poly.Polygraph.unitCupCell
#assert_no_axioms FX1Poly.Polygraph.arcWhiskerSupportListEquality_refutedOnGenCells
#assert_no_axioms FX1Poly.Polygraph.arcWhiskerSupportGenCells_linksLiterallyEqual
#assert_no_axioms FX1Poly.Polygraph.fxMode_hasWholeCellDisjointSupportCommute
#assert_no_axioms FX1Poly.Polygraph.arcWholeCellCommute_disjointWhiskerSupport_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcWholeCellCommute_swapRenameableProof2_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcWholeCellCommute_partitionCommute_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcWholeCellCommute_samePartitionFresh_stays_false
#assert_no_axioms FX1Poly.Polygraph.arcWholeCellCommute_blockCommute_stays_false

end FX1PolyAudit
