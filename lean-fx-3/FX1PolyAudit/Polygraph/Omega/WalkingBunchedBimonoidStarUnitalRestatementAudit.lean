import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidStarUnitalRestatement

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidStarUnitalRestatementAudit — zero-axiom gate for the unital re-statement: the four matrix-sound (co)unit rows, the widened Lafont scope, the monotone embedding, the re-stated target, the closure fires, and the honest owner (named, NOT proven). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidLeftUnitLawLeftLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidLeftCounitLawLeftLeg
#assert_no_axioms FX1Poly.Polygraph.Omega.BunchedBimonoidUnitCounitRow
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidUnitCounitRowMatrixSound
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidUnitalStarCongruenceScope
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStarConvEmbedsIntoUnital
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStarStatementDimTwoCanonicalGensUnital
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidUnitPairConvertsUnital
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidCounitPairConvertsUnital
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidUnitRowBreaksAffineInvariant
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_starUnitalRestatementShipped
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_dimTwoCanonicalGensUnitalStarStillOpen

-- Independent (non-fuel) axiom prints on the spine.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStarStatementDimTwoCanonicalGensUnital
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidUnitPairConvertsUnital
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_dimTwoCanonicalGensUnitalStarStillOpen

end FX1PolyAudit
