import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingOperad.OperadTreeDecision

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingOperad.OperadTreeDecision — zero-axiom gate (the right-comb decision)

Per-declaration zero-axiom gate for WP-OPERAD brick 2, the walking monoid operad tree-pasting word problem
decided via the RIGHT-COMB normal form: the builder `reify` and its equation / section smokes
(`arityOf_reify`), the normalizer `operadNF`, SOUNDNESS in NF shape (`operadNF_congr_of_conv`), the completeness
crux `reify_mulOp_append`, the reconstruction `conv_toReify`, completeness (`operadTreeConv_of_arity_eq` /
`conv_of_operadNF_eq`), the characterization `operadConv_iff_nf_eq`, the total decider + instance, the sample
trees, the non-vacuity witnesses / decider smokes, and the established marker.

Two independent mechanisms per the AuditAll-semantics rule: the fuel-based `#assert_no_axioms` gate (one per
declaration, throws on any axiom) and a separate `#print axioms` cross-check over the completeness theorem and
the decider.  Each must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.reify
#assert_no_axioms FX1Poly.Polygraph.reify_zero
#assert_no_axioms FX1Poly.Polygraph.reify_succ
#assert_no_axioms FX1Poly.Polygraph.reify_one
#assert_no_axioms FX1Poly.Polygraph.reify_two
#assert_no_axioms FX1Poly.Polygraph.arityOf_reify
#assert_no_axioms FX1Poly.Polygraph.operadNF
#assert_no_axioms FX1Poly.Polygraph.operadNF_eq
#assert_no_axioms FX1Poly.Polygraph.operadNF_leaf
#assert_no_axioms FX1Poly.Polygraph.operadNF_unitOp
#assert_no_axioms FX1Poly.Polygraph.operadNF_congr_of_conv
#assert_no_axioms FX1Poly.Polygraph.reify_mulOp_append
#assert_no_axioms FX1Poly.Polygraph.conv_toReify
#assert_no_axioms FX1Poly.Polygraph.operadTreeConv_of_arity_eq
#assert_no_axioms FX1Poly.Polygraph.conv_of_operadNF_eq
#assert_no_axioms FX1Poly.Polygraph.operadConv_iff_nf_eq
#assert_no_axioms FX1Poly.Polygraph.decideOperadTreeConv
#assert_no_axioms FX1Poly.Polygraph.instDecidableOperadTreeConv
#assert_no_axioms FX1Poly.Polygraph.operadMixedUnitTree
#assert_no_axioms FX1Poly.Polygraph.operadTwoLeaves
#assert_no_axioms FX1Poly.Polygraph.operadConv_mixedUnit_twoLeaves
#assert_no_axioms FX1Poly.Polygraph.operadDecide_true_on_assoc
#assert_no_axioms FX1Poly.Polygraph.operadDecide_true_on_unitLeft
#assert_no_axioms FX1Poly.Polygraph.operadDecide_true_on_unitRight
#assert_no_axioms FX1Poly.Polygraph.operadDecide_true_on_mixedUnit
#assert_no_axioms FX1Poly.Polygraph.operadDecide_false_on_twoLeaves_leaf
#assert_no_axioms FX1Poly.Polygraph.operadDecide_false_on_unitOp_leaf
#assert_no_axioms FX1Poly.Polygraph.fxOperad_hasRightCombDecision

/-! ## Independent `#print axioms` cross-check — the completeness theorem and the decider -/

#print axioms FX1Poly.Polygraph.reify_mulOp_append
#print axioms FX1Poly.Polygraph.conv_toReify
#print axioms FX1Poly.Polygraph.operadTreeConv_of_arity_eq
#print axioms FX1Poly.Polygraph.conv_of_operadNF_eq
#print axioms FX1Poly.Polygraph.operadConv_iff_nf_eq
#print axioms FX1Poly.Polygraph.decideOperadTreeConv
#print axioms FX1Poly.Polygraph.instDecidableOperadTreeConv
#print axioms FX1Poly.Polygraph.fxOperad_hasRightCombDecision

end FX1PolyAudit
