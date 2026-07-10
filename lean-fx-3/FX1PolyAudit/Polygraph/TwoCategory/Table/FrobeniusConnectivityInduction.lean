import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Table.FrobeniusConnectivityInduction

/-! # FX1PolyAudit.Polygraph.TwoCategory.Table.FrobeniusConnectivityInduction — zero-axiom gate for the
connectivity induction over the canonical-spider union-find fold + the general-arity connected realization
(FROB-SEED-MERGE r1, #2250, closing #2017's realization node).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.connRangeLoopLength
#assert_no_axioms FX1Poly.Polygraph.connRangeLength
#assert_no_axioms FX1Poly.Polygraph.connListLengthAppend
#assert_no_axioms FX1Poly.Polygraph.connGetAtMem
#assert_no_axioms FX1Poly.Polygraph.connAllMemAppend
#assert_no_axioms FX1Poly.Polygraph.connFanLenArith
#assert_no_axioms FX1Poly.Polygraph.stepWiringArcs_connects_arc
#assert_no_axioms FX1Poly.Polygraph.stepWiring_connects_arc
#assert_no_axioms FX1Poly.Polygraph.stepWiring_mult_head
#assert_no_axioms FX1Poly.Polygraph.stepWiring_comult_head
#assert_no_axioms FX1Poly.Polygraph.mergeToOne_succ_eq_replicate
#assert_no_axioms FX1Poly.Polygraph.mergeFold_connects_all
#assert_no_axioms FX1Poly.Polygraph.mergeToOne_result
#assert_no_axioms FX1Poly.Polygraph.fanFold_connects
#assert_no_axioms FX1Poly.Polygraph.canonicalSpiderFold_connected
#assert_no_axioms FX1Poly.Polygraph.canonicalSpider_finalOpenLength
#assert_no_axioms FX1Poly.Polygraph.canonicalSpiderConnectivity
#assert_no_axioms FX1Poly.Polygraph.extraSpiderDiagramOf_canonicalSpider
#assert_no_axioms FX1Poly.Polygraph.canonicalSpiderRealization_2_2
#assert_no_axioms FX1Poly.Polygraph.canonicalSpiderRealization_3_2
#assert_no_axioms FX1Poly.Polygraph.canonicalSpiderRealization_4_3

end FX1PolyAudit
