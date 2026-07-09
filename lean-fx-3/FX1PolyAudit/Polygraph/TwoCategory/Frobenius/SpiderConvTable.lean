import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Frobenius.SpiderConvTable

/-! # FX1PolyAudit.Polygraph.TwoCategory.Frobenius.SpiderConvTable — zero-axiom gate (WP-FROB r5, FROB-5)

Per-declaration zero-axiom gate for the DECIDED seed-view table (the thirteen `frobXSeedView_ordered` facts), the
GATE-FREE contextual congruence `SpiderConvTable` + its embedding / soundness, the non-vacuity witnesses, and the
honesty markers.  The private firing-discipline / seed witnesses are transitively covered by the public consumers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- FROB-5: the decided per-row seed-view table (raw `decide`, closed fixed-width)
#assert_no_axioms FX1Poly.Polygraph.frobAssocSeedView_ordered
#assert_no_axioms FX1Poly.Polygraph.frobUnitLeftSeedView_ordered
#assert_no_axioms FX1Poly.Polygraph.frobUnitRightSeedView_ordered
#assert_no_axioms FX1Poly.Polygraph.frobCoassocSeedView_ordered
#assert_no_axioms FX1Poly.Polygraph.frobCounitLeftSeedView_ordered
#assert_no_axioms FX1Poly.Polygraph.frobCounitRightSeedView_ordered
#assert_no_axioms FX1Poly.Polygraph.frobLeftSeedView_ordered
#assert_no_axioms FX1Poly.Polygraph.frobRightSeedView_ordered
#assert_no_axioms FX1Poly.Polygraph.frobCommMultSeedView_ordered
#assert_no_axioms FX1Poly.Polygraph.frobCommComultSeedView_ordered
#assert_no_axioms FX1Poly.Polygraph.frobCrossingInvolutionSeedView_ordered
#assert_no_axioms FX1Poly.Polygraph.frobYangBaxterSeedView_ordered
#assert_no_axioms FX1Poly.Polygraph.frobSpecialSeedView_ordered

-- FROB-5: the gate-free contextual congruence + its embedding / soundness
#assert_no_axioms FX1Poly.Polygraph.SpiderConvTable
#assert_no_axioms FX1Poly.Polygraph.spiderConvTable_toSpiderConvSyntactic
#assert_no_axioms FX1Poly.Polygraph.spiderConvTable_toSpiderConv
#assert_no_axioms FX1Poly.Polygraph.spiderConvTable_partitionSound

-- FROB-5: non-vacuity — the sentinel through the gate-free constructor + the composed identification
#assert_no_axioms FX1Poly.Polygraph.spiderConvTable_special_afterIdentityPrefix
#assert_no_axioms FX1Poly.Polygraph.spiderConvTable_special_identifies_distinct
#assert_no_axioms FX1Poly.Polygraph.spiderConvTable_special_partitionAgrees
#assert_no_axioms FX1Poly.Polygraph.spiderConvTable_frobLeft_frobRight_lhs
#assert_no_axioms FX1Poly.Polygraph.spiderConvTable_frobLeft_frobRight_identifies_distinct
#assert_no_axioms FX1Poly.Polygraph.spiderConvTable_H_not_identity

-- FROB-5: the honesty markers (shipped gate-free table + walled two-sided residuals)
#assert_no_axioms FX1Poly.Polygraph.fxFrob_hasSpiderSeedViewTable
#assert_no_axioms FX1Poly.Polygraph.fxFrob_hasSpiderConvTable
#assert_no_axioms FX1Poly.Polygraph.fxFrob_hasSpiderSuffixCongruence
#assert_no_axioms FX1Poly.Polygraph.fxFrob_hasSpiderBoundaryChangingPrefix

end FX1PolyAudit
