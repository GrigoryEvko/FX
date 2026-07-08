import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingInvolution.InvolutionSeed

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingInvolution.InvolutionSeed — zero-axiom gate (the walking-involution seed)

Per-declaration zero-axiom gate for the walking-involution seed: the mode / modality generators, the quiver, the
`id` and `s` free 1-cells, the degenerate 2-signature (free on nothing), and the freeness / degeneracy smokes.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.InvolutionMode
#assert_no_axioms FX1Poly.Polygraph.InvolutionModality
#assert_no_axioms FX1Poly.Polygraph.involutionGraph
#assert_no_axioms FX1Poly.Polygraph.involutionNil
#assert_no_axioms FX1Poly.Polygraph.involutionS
#assert_no_axioms FX1Poly.Polygraph.involutionModeSignature
#assert_no_axioms FX1Poly.Polygraph.involutionS_length
#assert_no_axioms FX1Poly.Polygraph.involutionSThenS_length
#assert_no_axioms FX1Poly.Polygraph.involution_no_two_generators

end FX1PolyAudit
