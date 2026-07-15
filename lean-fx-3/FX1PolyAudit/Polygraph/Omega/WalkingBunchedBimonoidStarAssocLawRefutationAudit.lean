-- TODO: DELETE THIS GARBAGE -- defective bunchedBimonoid star (refuted r29/r30/r31); superseded by the LafontProp re-founding
import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidStarAssocLawRefutation

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidStarAssocLawRefutationAudit — zero-axiom gate for the r31 decision: the unital star refuted through the missing (co)associativity laws — the association pair passes all seven premises, the plain AND affine invariants are blind, the bracket magma separates. -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidLeftAssocAdditive
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRightAssocAdditive
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidLeftAssocWellTyped
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRightAssocWellTyped
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidLeftAssocCanonical
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRightAssocCanonical
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAssocPairMatricesEqual
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAssocPairAugValuesEqual
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidLeftAssocClean
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidRightAssocClean
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAssocPairBracketSeparates
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAssocPairNotConvUnital
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStarStatementDimTwoCanonicalGensUnitalRefuted
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidPentagonIsInterchangeInstance
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_dimTwoCanonicalGensUnitalStarDecidedFalse
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_unitalStarScopeLacksAssociativity

-- Independent (non-fuel) axiom prints on the spine.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStarStatementDimTwoCanonicalGensUnitalRefuted
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAssocPairNotConvUnital
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAssocPairBracketSeparates
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidAssocPairAugValuesEqual

end FX1PolyAudit
