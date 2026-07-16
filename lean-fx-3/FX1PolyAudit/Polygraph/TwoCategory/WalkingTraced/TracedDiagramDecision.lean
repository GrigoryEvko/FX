import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingTraced.TracedDiagramDecision

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingTraced.TracedDiagramDecision — zero-axiom gate (the fragment decision)

Per-declaration zero-axiom gate for WP-TRACED brick 2, the shipped 3-axiom traced fragment word problem
decided via the smart-constructor normal form: the 1-trace smart constructor `contractTraceOne` and its
definitional-arm smokes (headlined by the opaque-children tightening equation), the payload dispatch
`dispatchTrace`, the normalizer `tracedNF` and its defining equations, the reconstruction
(`conv_toContractTraceOne` / `conv_toDispatchTrace` / `conv_toTracedNF`), SOUNDNESS
(`tracedNF_congr_of_conv`), completeness (`conv_of_tracedNF_eq`), the characterization
(`tracedConv_iff_nf_eq`), the hand-rolled `tracedDiagramDecEq` + instance, the total decider + instance,
the sample diagrams, the positive/negative decider pins, the discharged seed honesty witness
(`tracedNotConv_swap_tensorIdWireIdWire`) and scalar separations, the trace-free collapse corollary, and the
two markers (the decision recorded; the full-JSV wall moved, not erased).

Two independent mechanisms per the AuditAll-semantics rule: the fuel-based `#assert_no_axioms` gate (one per
declaration, throws on any axiom) and a separate `#print axioms` cross-check over the completeness theorem,
the soundness theorem, and the decider.  Each must be free of `propext`, `Quot.sound`, `Classical`, `sorry`,
`native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.contractTraceOne
#assert_no_axioms FX1Poly.Polygraph.contractTraceOne_swap
#assert_no_axioms FX1Poly.Polygraph.contractTraceOne_tightening
#assert_no_axioms FX1Poly.Polygraph.contractTraceOne_box
#assert_no_axioms FX1Poly.Polygraph.contractTraceOne_tensor
#assert_no_axioms FX1Poly.Polygraph.contractTraceOne_seqSwapLeft
#assert_no_axioms FX1Poly.Polygraph.contractTraceOne_seqTensorBoxRight
#assert_no_axioms FX1Poly.Polygraph.contractTraceOne_traceN
#assert_no_axioms FX1Poly.Polygraph.dispatchTrace
#assert_no_axioms FX1Poly.Polygraph.dispatchTrace_zero
#assert_no_axioms FX1Poly.Polygraph.dispatchTrace_one
#assert_no_axioms FX1Poly.Polygraph.dispatchTrace_twoPlus
#assert_no_axioms FX1Poly.Polygraph.tracedNF
#assert_no_axioms FX1Poly.Polygraph.tracedNF_empty
#assert_no_axioms FX1Poly.Polygraph.tracedNF_idWire
#assert_no_axioms FX1Poly.Polygraph.tracedNF_box
#assert_no_axioms FX1Poly.Polygraph.tracedNF_swap
#assert_no_axioms FX1Poly.Polygraph.tracedNF_seq
#assert_no_axioms FX1Poly.Polygraph.tracedNF_tensor
#assert_no_axioms FX1Poly.Polygraph.tracedNF_traceN
#assert_no_axioms FX1Poly.Polygraph.conv_toContractTraceOne
#assert_no_axioms FX1Poly.Polygraph.conv_toDispatchTrace
#assert_no_axioms FX1Poly.Polygraph.conv_toTracedNF
#assert_no_axioms FX1Poly.Polygraph.tracedNF_congr_of_conv
#assert_no_axioms FX1Poly.Polygraph.conv_of_tracedNF_eq
#assert_no_axioms FX1Poly.Polygraph.tracedConv_iff_nf_eq
#assert_no_axioms FX1Poly.Polygraph.tracedDiagramDecEq
#assert_no_axioms FX1Poly.Polygraph.instDecidableEqTracedDiagram
#assert_no_axioms FX1Poly.Polygraph.decideTracedDiagramConv
#assert_no_axioms FX1Poly.Polygraph.instDecidableTracedDiagramConv
#assert_no_axioms FX1Poly.Polygraph.tracedTwoAxiomChainLeft
#assert_no_axioms FX1Poly.Polygraph.tracedTwoAxiomChainRight
#assert_no_axioms FX1Poly.Polygraph.tracedLoopScalar
#assert_no_axioms FX1Poly.Polygraph.tracedBoxScalar
#assert_no_axioms FX1Poly.Polygraph.tracedDoubleTighteningLeft
#assert_no_axioms FX1Poly.Polygraph.tracedDoubleTighteningRight
#assert_no_axioms FX1Poly.Polygraph.tracedConv_twoAxiomChain
#assert_no_axioms FX1Poly.Polygraph.tracedDecide_true_on_yanking
#assert_no_axioms FX1Poly.Polygraph.tracedDecide_true_on_vanishingUnit
#assert_no_axioms FX1Poly.Polygraph.tracedDecide_true_on_tightening
#assert_no_axioms FX1Poly.Polygraph.tracedDecide_true_on_twoAxiomChain
#assert_no_axioms FX1Poly.Polygraph.tracedDecide_true_on_nestedVanishingYanking
#assert_no_axioms FX1Poly.Polygraph.tracedDecide_true_on_doubleTightening
#assert_no_axioms FX1Poly.Polygraph.tracedNotConv_swap_tensorIdWireIdWire
#assert_no_axioms FX1Poly.Polygraph.tracedNotConv_loopScalar_idWire
#assert_no_axioms FX1Poly.Polygraph.tracedNotConv_boxScalar_box
#assert_no_axioms FX1Poly.Polygraph.tracedDecide_false_on_swap_tensorIdWires
#assert_no_axioms FX1Poly.Polygraph.tracedDecide_false_on_loopScalar_idWire
#assert_no_axioms FX1Poly.Polygraph.tracedDecide_false_on_boxScalar_box
#assert_no_axioms FX1Poly.Polygraph.isTraceFree
#assert_no_axioms FX1Poly.Polygraph.isTraceFree_seq
#assert_no_axioms FX1Poly.Polygraph.isTraceFree_tensor
#assert_no_axioms FX1Poly.Polygraph.tracedNF_fixed_of_traceFree
#assert_no_axioms FX1Poly.Polygraph.tracedConv_collapses_on_traceFree
#assert_no_axioms FX1Poly.Polygraph.fxTraced_hasFragmentDecision
#assert_no_axioms FX1Poly.Polygraph.fxTraced_hasFullJsvTraceAxiomsDecided

/-! ## Independent `#print axioms` cross-check — soundness, completeness, and the decider -/

#print axioms FX1Poly.Polygraph.conv_toContractTraceOne
#print axioms FX1Poly.Polygraph.conv_toTracedNF
#print axioms FX1Poly.Polygraph.tracedNF_congr_of_conv
#print axioms FX1Poly.Polygraph.conv_of_tracedNF_eq
#print axioms FX1Poly.Polygraph.tracedConv_iff_nf_eq
#print axioms FX1Poly.Polygraph.tracedDiagramDecEq
#print axioms FX1Poly.Polygraph.decideTracedDiagramConv
#print axioms FX1Poly.Polygraph.instDecidableTracedDiagramConv
#print axioms FX1Poly.Polygraph.tracedNotConv_swap_tensorIdWireIdWire
#print axioms FX1Poly.Polygraph.tracedConv_collapses_on_traceFree
#print axioms FX1Poly.Polygraph.fxTraced_hasFragmentDecision

end FX1PolyAudit
