import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingInvolution.InvolutionDecision

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingInvolution.InvolutionDecision — zero-axiom gate (completeness + the total decision)

Per-declaration zero-axiom gate for the walking-involution decision: the parity normal form, the reconstruction
(completeness), the total decider and its instance, the non-vacuity witnesses / decider smokes, and the
established marker.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.parityNF
#assert_no_axioms FX1Poly.Polygraph.consCongr_parityNF
#assert_no_axioms FX1Poly.Polygraph.conv_toParityNF_ofLength
#assert_no_axioms FX1Poly.Polygraph.conv_toParityNF
#assert_no_axioms FX1Poly.Polygraph.involutionOneCellConv_of_parity_eq
#assert_no_axioms FX1Poly.Polygraph.decideInvolutionOneCellConv
#assert_no_axioms FX1Poly.Polygraph.instDecidableInvolutionOneCellConv
#assert_no_axioms FX1Poly.Polygraph.involutionConv_double_nil
#assert_no_axioms FX1Poly.Polygraph.involutionNotConv_single_nil
#assert_no_axioms FX1Poly.Polygraph.involutionDecide_true_on_double
#assert_no_axioms FX1Poly.Polygraph.involutionDecide_false_on_single
#assert_no_axioms FX1Poly.Polygraph.fxInvolution_hasOneCellWordProblemDecided

end FX1PolyAudit
