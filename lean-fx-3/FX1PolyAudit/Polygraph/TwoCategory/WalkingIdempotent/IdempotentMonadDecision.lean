import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingIdempotent.IdempotentMonadDecision

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingIdempotent.IdempotentMonadDecision — zero-axiom gate (thinness + decision modulo it)

Per-declaration zero-axiom gate for the walking-idempotent-monad decision: the thinness Prop, the local-posetality
package, the decision assembly, the genuine hom-`t ⇒ t` thinness instances, and the honesty markers.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.IdempotentMonadThinness
#assert_no_axioms FX1Poly.Polygraph.IdempotentMonadLocalPosetality
#assert_no_axioms FX1Poly.Polygraph.decideIdempotentConvViaThinness
#assert_no_axioms FX1Poly.Polygraph.idempotentSaturatedWordProblemModuloPosetality
#assert_no_axioms FX1Poly.Polygraph.idempotentLeftUnitConvIdT
#assert_no_axioms FX1Poly.Polygraph.idempotentRightUnitConvIdT
#assert_no_axioms FX1Poly.Polygraph.idempotentLeftUnitConvRightUnit_viaIdempotence
#assert_no_axioms FX1Poly.Polygraph.idempotentHomTToT_thinOnRepresentatives
#assert_no_axioms FX1Poly.Polygraph.decideIdempotent_isTrue_ofPosetality
#assert_no_axioms FX1Poly.Polygraph.fxIdempotentMonad_hasDecisionAssemblyModuloThinness
#assert_no_axioms FX1Poly.Polygraph.fxIdempotentMonad_hasLocalPosetalityCollapse

end FX1PolyAudit
