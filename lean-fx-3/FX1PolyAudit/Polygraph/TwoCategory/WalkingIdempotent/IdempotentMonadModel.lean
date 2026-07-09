import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingIdempotent.IdempotentMonadModel

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingIdempotent.IdempotentMonadModel — zero-axiom gate (the chain model + boundary soundness)

Per-declaration zero-axiom gate for the walking-idempotent-monad `{0 ≤ 1}` chain model: the width bit / collapse,
the chain order, the four generator validations, the boundary image, and its (degenerate) soundness.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.natWidthBit
#assert_no_axioms FX1Poly.Polygraph.monadWidthCollapse
#assert_no_axioms FX1Poly.Polygraph.idempotentInhabited
#assert_no_axioms FX1Poly.Polygraph.idempotentInhabited_unit
#assert_no_axioms FX1Poly.Polygraph.idempotentInhabited_mul
#assert_no_axioms FX1Poly.Polygraph.idempotentInhabited_idempotenceFaces
#assert_no_axioms FX1Poly.Polygraph.idempotentInhabited_no_collapse_to_identity
#assert_no_axioms FX1Poly.Polygraph.idempotentBoundaryOf
#assert_no_axioms FX1Poly.Polygraph.idempotentBoundaryOf_congr_of_conv
#assert_no_axioms FX1Poly.Polygraph.idempotentBoundaryOf_idempotenceFaces
#assert_no_axioms FX1Poly.Polygraph.idempotentBoundaryOf_idempotenceFaces_value
#assert_no_axioms FX1Poly.Polygraph.fxIdempotentMonad_hasChainModelBoundarySound

end FX1PolyAudit
