import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingIdempotent.IdempotentMonadMuInvertible

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingIdempotent.IdempotentMonadMuInvertible — zero-axiom gate (the mu-iso crux)

Per-declaration zero-axiom gate for the walking-idempotent-monad mu-invertibility crux: the free-move lift
helpers, the cell-level rigidity + empty-hom thinness, the mu-iso arc (naturality of `eta` at `mu`,
well-pointedness whiskered, the Godement collapse, the right inverse, invertibility packaging), the `t.t ⇒ t.t`
representative collapse, the honest thinness reduction, the smokes, and the honesty markers.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.idempotentConvOfStep
#assert_no_axioms FX1Poly.Polygraph.idempotentConvOfFull
#assert_no_axioms FX1Poly.Polygraph.rawCell_targetLenZero_impliesSourceLenZero
#assert_no_axioms FX1Poly.Polygraph.noRawCellFromTIntoIdentity
#assert_no_axioms FX1Poly.Polygraph.emptyHom_isThin
#assert_no_axioms FX1Poly.Polygraph.mulThenUnitRightWhisker
#assert_no_axioms FX1Poly.Polygraph.godementUnitMul
#assert_no_axioms FX1Poly.Polygraph.mulThenUnitRightWhisker_conv_godement
#assert_no_axioms FX1Poly.Polygraph.unitRightWhiskerSquare_conv_unitLeftWhisker
#assert_no_axioms FX1Poly.Polygraph.godementUnitMul_conv_identity
#assert_no_axioms FX1Poly.Polygraph.idempotentMulRightInverse
#assert_no_axioms FX1Poly.Polygraph.idempotentMulRightInverse_leftWhisker
#assert_no_axioms FX1Poly.Polygraph.idempotentMulInvertible
#assert_no_axioms FX1Poly.Polygraph.idempotentHomTThenTToTThenT_thinOnRepresentatives
#assert_no_axioms FX1Poly.Polygraph.idempotentThinness_ofNormalize
#assert_no_axioms FX1Poly.Polygraph.mulThenUnitRightWhisker_size
#assert_no_axioms FX1Poly.Polygraph.godementUnitMul_size
#assert_no_axioms FX1Poly.Polygraph.fxIdempotentMonad_hasMulInvertible
#assert_no_axioms FX1Poly.Polygraph.fxIdempotentMonad_hasCellRigidity
#assert_no_axioms FX1Poly.Polygraph.fxIdempotentMonad_hasGeneralThinnessNormalizer

end FX1PolyAudit
