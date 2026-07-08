import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingInvolution.InvolutionOneCellConv

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingInvolution.InvolutionOneCellConv — zero-axiom gate (the `s.s = id` convertibility)

Per-declaration zero-axiom gate for the walking-involution 1-cell convertibility: the `InvolutionOneCellConv`
relation and its three law / congruence witnesses.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.InvolutionOneCellConv
#assert_no_axioms FX1Poly.Polygraph.involutionLawHolds
#assert_no_axioms FX1Poly.Polygraph.involutionTripleReducesToSingle
#assert_no_axioms FX1Poly.Polygraph.involutionLawWhiskeredHolds

end FX1PolyAudit
