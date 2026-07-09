import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingString.StringMatchingReconstructionDescent

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingString.StringMatchingReconstructionDescent — zero-axiom gate

Per-declaration zero-axiom gate for the FC-6 P2 reconstruction descent kit: the matchingOf-preservation lemmas for
CANCEL (all four colours) and EXTEND, the reconstruction-target descent lemmas for the same, the pure-CANCEL
satisfiability witness, and the two honesty markers.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.stringCancelSnakeF_preservesMatchingOf
#assert_no_axioms FX1Poly.Polygraph.stringCancelSnakeGlo_preservesMatchingOf
#assert_no_axioms FX1Poly.Polygraph.stringCancelSnakeGhi_preservesMatchingOf
#assert_no_axioms FX1Poly.Polygraph.stringCancelSnakeH_preservesMatchingOf
#assert_no_axioms FX1Poly.Polygraph.stringExtendByIdentity_preservesMatchingOf
#assert_no_axioms FX1Poly.Polygraph.stringCancelSnakeF_convDescent
#assert_no_axioms FX1Poly.Polygraph.stringCancelSnakeGlo_convDescent
#assert_no_axioms FX1Poly.Polygraph.stringCancelSnakeGhi_convDescent
#assert_no_axioms FX1Poly.Polygraph.stringCancelSnakeH_convDescent
#assert_no_axioms FX1Poly.Polygraph.stringExtendByIdentity_convDescent
#assert_no_axioms FX1Poly.Polygraph.stringSnakeStackF_reconstructsToIdentityF
#assert_no_axioms FX1Poly.Polygraph.fxString_hasReconstructionDescentKit
#assert_no_axioms FX1Poly.Polygraph.fxString_hasReconstructionDescentDriver

end FX1PolyAudit
