import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.WalkingCohesionQuadruple.QuadrupleSeed

/-! # FX1PolyAudit.Polygraph.TwoCategory.WalkingCohesionQuadruple.QuadrupleSeed — zero-axiom gate (the quadruple seed)

Per-declaration zero-axiom gate for the walking-cohesion-quadruple seed: the mode / functor / two-cell generator
inductives, the 1-cell generators and their length-2 endo-composites, the signature, and the freeness smokes.
Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.QuadCohesionMode
#assert_no_axioms FX1Poly.Polygraph.QuadCohesionModality
#assert_no_axioms FX1Poly.Polygraph.quadCohesionGraph
#assert_no_axioms FX1Poly.Polygraph.quadPi0
#assert_no_axioms FX1Poly.Polygraph.quadDisc
#assert_no_axioms FX1Poly.Polygraph.quadGamma
#assert_no_axioms FX1Poly.Polygraph.quadCodisc
#assert_no_axioms FX1Poly.Polygraph.quadPi0Disc
#assert_no_axioms FX1Poly.Polygraph.quadDiscPi0
#assert_no_axioms FX1Poly.Polygraph.quadDiscGamma
#assert_no_axioms FX1Poly.Polygraph.quadGammaDisc
#assert_no_axioms FX1Poly.Polygraph.quadGammaCodisc
#assert_no_axioms FX1Poly.Polygraph.quadCodiscGamma
#assert_no_axioms FX1Poly.Polygraph.QuadCohesionTwoCell
#assert_no_axioms FX1Poly.Polygraph.quadCohesionModeSignature
#assert_no_axioms FX1Poly.Polygraph.quadPi0Disc_length
#assert_no_axioms FX1Poly.Polygraph.quadGammaDisc_length
#assert_no_axioms FX1Poly.Polygraph.quadGammaCodisc_length
#assert_no_axioms FX1Poly.Polygraph.quadCodiscGamma_length
#assert_no_axioms FX1Poly.Polygraph.quadPi0_ne_gamma
#assert_no_axioms FX1Poly.Polygraph.quadDisc_ne_codisc
#assert_no_axioms FX1Poly.Polygraph.quadPi0Disc_ne_gammaDisc

end FX1PolyAudit
