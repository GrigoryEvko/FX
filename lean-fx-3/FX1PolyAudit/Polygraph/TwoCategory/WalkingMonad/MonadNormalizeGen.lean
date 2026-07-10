import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadNormalizeGen

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingMonad.MonadNormalizeGen — zero-axiom gate
(POLY-TAB r6 monad re-founding WAVE 2, Brick C: the born-generic normalize + the bespoke-free native decider)

Per-declaration zero-axiom gate for the completeness flip: the whisker/vcomp `normalizeCell` cases, the fueled
recursion, `monadNormalizeGen`, the `convOfMapEqGen` reduction, the bespoke-free canonicalization + native decider,
and the regression ties.  Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadNormalize_whiskerLeftGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadNormalize_whiskerRightGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadNormalize_vcompGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadNormalizeCellFueledGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadNormalizeGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadConvOfMapEqGen_ofNormalizeGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadSaturatedCanonicalizationGenNative
#assert_no_axioms FX1Poly.Polygraph.Amalgam.decideSaturatedConvOverMonadNative
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadNativeDecidesTrue_assoc_holds
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadNativeDecidesFalse_faces_holds
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadNativeAgreesOnRegression_holds
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxMonad_hasMonadNormalizeGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxMonad_hasGenericNativeDeciderComplete

end FX1PolyAudit
