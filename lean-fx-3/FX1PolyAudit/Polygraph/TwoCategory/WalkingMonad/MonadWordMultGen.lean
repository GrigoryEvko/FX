import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadWordMultGen

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingMonad.MonadWordMultGen — zero-axiom gate
(POLY-TAB r6 monad re-founding WAVE 2, Brick A: whisker/horizontal word multiplicativity, generic carrier)

Per-declaration zero-axiom gate for the generic-carrier whisker + horizontal word-multiplicativity port.  Must be
free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.SaturatedConvOver.ofEq
#assert_no_axioms FX1Poly.Polygraph.Amalgam.SaturatedConvOver.hcompCongrLeft
#assert_no_axioms FX1Poly.Polygraph.Amalgam.SaturatedConvOver.hcompCongrRight
#assert_no_axioms FX1Poly.Polygraph.Amalgam.wordFromCounts_monadOnes_succ_convGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.wordFromCounts_monadOnes_convGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.wordFromCounts_consOne_convGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.wordMul_whiskerLeftGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.wordMul_hcompGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.wordMul_whiskerRightGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxMonad_hasWordMultGen

end FX1PolyAudit
