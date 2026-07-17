import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Frobenius.MultiBlockSpiderRealization

/-! # FX1PolyAudit.Polygraph.TwoCategory.Frobenius.MultiBlockSpiderRealization — zero-axiom gate for the
block-diagonal multi-block spider readback + the single-block base reuse (WP-FROBMONAD, #2070).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`.
The `blockSpiderReadback` / `sumInputs` / `sumOutputs` definitions are covered transitively through the theorems;
the `decide` firing instances are covered by their own gates. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.multiBlockAppendNil
#assert_no_axioms FX1Poly.Polygraph.multiBlockAppendAssoc
#assert_no_axioms FX1Poly.Polygraph.shiftBrauerWord_append
#assert_no_axioms FX1Poly.Polygraph.blockSpiderReadback_append
#assert_no_axioms FX1Poly.Polygraph.blockSpiderReadback_singleton_eq
#assert_no_axioms FX1Poly.Polygraph.blockSpiderReadback_realizes_single
#assert_no_axioms FX1Poly.Polygraph.blockSpiderReadback_realizes_2_1_and_1_2
#assert_no_axioms FX1Poly.Polygraph.blockSpiderReadback_realizes_1_1_and_1_1
#assert_no_axioms FX1Poly.Polygraph.blockSpiderReadback_realizes_1_0_and_0_1
#assert_no_axioms FX1Poly.Polygraph.blockSpiderReadback_realizes_three_blocks
#assert_no_axioms FX1Poly.Polygraph.fxFrob_hasBlockDiagonalMultiBlockReadback

end FX1PolyAudit
