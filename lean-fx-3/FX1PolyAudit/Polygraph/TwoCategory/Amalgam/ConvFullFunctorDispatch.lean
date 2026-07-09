import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.ConvFullFunctorDispatch

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.ConvFullFunctorDispatch — zero-axiom gate for the UNCONDITIONAL
saturated-conv soundness lift (WP-AMALG r5, P1 wiring)

Per-declaration zero-axiom gate for: the unconditional soundness lift `mapCellAlong_preservesConvUnconditional`
(the r4 conditional `mapCellAlong_preservesConv` with `fullPreserved := mapTwoCellConvFull`), and the two
pushout coprojection convertibility lifts (`pushoutPreservesConvLeft` / `pushoutPreservesConvRight`).

Every declaration must be free of `propext`, `Quot.sound`, `Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.mapCellAlong_preservesConvUnconditional
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutPreservesConvLeft
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutPreservesConvRight
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasUnconditionalSoundnessLift

end FX1PolyAudit
