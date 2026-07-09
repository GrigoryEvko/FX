import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Frobenius.SpiderConv

/-! # FX1PolyAudit.Polygraph.TwoCategory.Frobenius.SpiderConv — zero-axiom gate (WP-FROB r3, FROB-3)

Per-declaration zero-axiom gate for the partition-sound convertibility relation over the special-Frobenius
presentation: the field-determination helpers, the block-label read-off congruence, the forget-extract
connectivity-view lemma, the `SpiderConv` inductive, its partition-soundness proof, the non-vacuity witnesses
(distinct-word identification, the partition separation, the proper-relation refutation, the in-context whisker),
and the honesty markers.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

-- FROB-3: the field-determination helpers + block-label congruence + the connectivity-view lemma
#assert_no_axioms FX1Poly.Polygraph.spiderPartitionType_eq_of_fields
#assert_no_axioms FX1Poly.Polygraph.spiderDiagramType_eq_of_fields
#assert_no_axioms FX1Poly.Polygraph.firstIndexWithRoot_congr
#assert_no_axioms FX1Poly.Polygraph.extractSpiderDiagram_forget_eq_of_connectivityView

-- FROB-3: the convertibility relation + its partition-soundness
#assert_no_axioms FX1Poly.Polygraph.SpiderConv
#assert_no_axioms FX1Poly.Polygraph.spiderConv_partitionSound

-- FROB-3: the non-vacuity witnesses
#assert_no_axioms FX1Poly.Polygraph.spiderConv_frobLeft
#assert_no_axioms FX1Poly.Polygraph.spiderConv_frobLeft_identifies_distinct
#assert_no_axioms FX1Poly.Polygraph.extraSpiderDiagram_H_ne_identity
#assert_no_axioms FX1Poly.Polygraph.spiderConv_H_not_identity
#assert_no_axioms FX1Poly.Polygraph.spiderConv_whisker_commComult_inContext
#assert_no_axioms FX1Poly.Polygraph.spiderConv_whisker_inContext_distinct

-- FROB-3: the honesty markers
#assert_no_axioms FX1Poly.Polygraph.fxFrob_hasSpiderConvSoundness
#assert_no_axioms FX1Poly.Polygraph.fxFrob_hasSpiderConvContextualInterchange

end FX1PolyAudit
