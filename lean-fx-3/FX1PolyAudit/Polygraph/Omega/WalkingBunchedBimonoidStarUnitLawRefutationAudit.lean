-- TODO: DELETE THIS GARBAGE -- defective bunchedBimonoid star (refuted r29/r30/r31); superseded by the LafontProp re-founding
import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.Omega.WalkingBunchedBimonoidStarUnitLawRefutation

/-! # FX1PolyAudit.Polygraph.Omega.WalkingBunchedBimonoidStarUnitLawRefutationAudit — zero-axiom gate for the r30 DECISION: the r29 corrected dim-2-canonical star is REFUTED through the missing (co)unit laws (the unit-into-multiplication pair, the affine-offset separation, the non-convertibility, the negated star). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidUnitIntoMuCell
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidIdentityStrandCell
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidUnitIntoMuAdditive
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidIdentityStrandAdditive
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidUnitIntoMuWellTyped
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidIdentityStrandWellTyped
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidUnitIntoMuCanonical
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidIdentityStrandCanonical
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidUnitIntoMuMatrixEqualsIdentityStrand
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidUnitIntoMuClean
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidIdentityStrandClean
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidUnitIntoMuAugValueSeparates
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidUnitIntoMuNotConvToIdentityStrand
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStarStatementDimTwoCanonicalGensRefuted
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDeltaIntoCounitCell
#assert_no_axioms FX1Poly.Polygraph.Omega.bunchedBimonoidDeltaIntoCounitMatrixBlind
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_dimTwoCanonicalGensStarDecidedFalse
#assert_no_axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_starScopeLacksUnitCounitLaws

-- Independent (non-fuel) axiom prints on the spine.
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidUnitIntoMuNotConvToIdentityStrand
#print axioms FX1Poly.Polygraph.Omega.bunchedBimonoidStarStatementDimTwoCanonicalGensRefuted
#print axioms FX1Poly.Polygraph.Omega.fxBunchedBimonoid_dimTwoCanonicalGensStarDecidedFalse

end FX1PolyAudit
