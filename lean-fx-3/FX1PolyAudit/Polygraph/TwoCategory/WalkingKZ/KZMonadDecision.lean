import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingKZ.KZMonadDecision

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingKZ.KZMonadDecision — zero-axiom gate (soundness, KZ-equality decision, order modulo)

Per-declaration zero-axiom gate for the walking-KZ decision: the four soundness congruence helpers, the soundness
theorem, the strict non-vacuity pair, the antisymmetric-core equality (`kzEq_iff_mapEq`) and its TOTAL decision
`decideKZEq`, the order decision modulo the named `KZOrderCompleteness` residual, and the honesty markers.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.kzSound_vcompLeft
#assert_no_axioms FX1Poly.Polygraph.kzSound_vcompRight
#assert_no_axioms FX1Poly.Polygraph.kzSound_whiskerLeft
#assert_no_axioms FX1Poly.Polygraph.kzSound_whiskerRight
#assert_no_axioms FX1Poly.Polygraph.kzLE_sound
#assert_no_axioms FX1Poly.Polygraph.kz_strict
#assert_no_axioms FX1Poly.Polygraph.kzLE_ofMapEq
#assert_no_axioms FX1Poly.Polygraph.kzEq_iff_mapEq
#assert_no_axioms FX1Poly.Polygraph.decideKZEq
#assert_no_axioms FX1Poly.Polygraph.decideKZEq_yes_assoc
#assert_no_axioms FX1Poly.Polygraph.decideKZEq_no_faces
#assert_no_axioms FX1Poly.Polygraph.KZOrderCompleteness
#assert_no_axioms FX1Poly.Polygraph.decideKZLE
#assert_no_axioms FX1Poly.Polygraph.kzOrderWordProblemModuloCompleteness
#assert_no_axioms FX1Poly.Polygraph.fxKZ_hasKZOrderSoundnessAndStrictness
#assert_no_axioms FX1Poly.Polygraph.fxKZ_hasKZEqualityDecisionClosed
#assert_no_axioms FX1Poly.Polygraph.fxKZ_hasKZOrderDecisionModuloCompleteness
#assert_no_axioms FX1Poly.Polygraph.fxKZ_hasWalkingKZOrderCompleteness

end FX1PolyAudit
