import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingMonad.MonadNormalizeCasesGen

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingMonad.MonadNormalizeCasesGen — zero-axiom gate
(POLY-TAB r6 monad re-founding WAVE 2, Brick A: the base + id `normalize` cases, generic carrier)

Per-declaration zero-axiom gate for the generic-carrier generator base cases + the `id` case. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadNormalize_genEtaGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadNormalize_genMuGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.monadNormalize_idGen
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxMonad_hasNormalizeBaseCasesGen

end FX1PolyAudit
