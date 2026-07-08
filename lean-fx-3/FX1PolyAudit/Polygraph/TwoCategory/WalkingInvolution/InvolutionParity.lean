import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingInvolution.InvolutionParity

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingInvolution.InvolutionParity — zero-axiom gate (the Z/2 model + soundness)

Per-declaration zero-axiom gate for the walking-involution Z/2 model: double-negation, `natParity`, the parity
invariant, its defining equations / smokes, and the SOUNDNESS of the parity under convertibility.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.involutionBoolNotNot
#assert_no_axioms FX1Poly.Polygraph.natParity
#assert_no_axioms FX1Poly.Polygraph.involutionParityOf
#assert_no_axioms FX1Poly.Polygraph.involutionParityOf_nil
#assert_no_axioms FX1Poly.Polygraph.involutionParityOf_cons
#assert_no_axioms FX1Poly.Polygraph.involutionParityOf_involutionS
#assert_no_axioms FX1Poly.Polygraph.involutionParityOf_involutionSThenS
#assert_no_axioms FX1Poly.Polygraph.involutionParityOf_congr_of_conv

end FX1PolyAudit
