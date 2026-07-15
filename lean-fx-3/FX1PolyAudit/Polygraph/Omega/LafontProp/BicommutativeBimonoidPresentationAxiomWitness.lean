import FX1Poly.Polygraph.Omega.LafontProp.MatNatSemantics
import FX1Poly.Polygraph.Omega.LafontProp.BicommutativeBimonoidPresentation

/-! # FX1PolyAudit.Polygraph.Omega.LafontProp.BicommutativeBimonoidPresentationAxiomWitness —
independent #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the fuel-based
`#assert_no_axioms` gates in the per-file twins) over the headline declarations of the LAFONT-PROP
re-founding: the kit smoke fires (including the machine-checked failure of the Z2-specific relation over
N), THE RELATION-DIFF GATE, the syntactic bare-identity pins, all 18 per-row matrix-soundness fires, and
THE DEFENSIVE FIRES (the exact r30 refuted unit and associativity pairs, now convertible, plus the
derived chain).  Each must print "does not depend on any axioms".  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.Omega.LafontProp.swapComposeSwapAgreesWithIdentity
#print axioms FX1Poly.Polygraph.Omega.LafontProp.copyThenAddDoublesNotIdentity
#print axioms FX1Poly.Polygraph.Omega.LafontProp.zSpecificRelationFailsOverNat
#print axioms FX1Poly.Polygraph.Omega.LafontProp.identityComposeAddAgreesWithAdd
#print axioms FX1Poly.Polygraph.Omega.LafontProp.directSumOfIdentitiesAgreesWithIdentity
#print axioms FX1Poly.Polygraph.Omega.LafontProp.addAssociativityRow_isSoundOverMatrices
#print axioms FX1Poly.Polygraph.Omega.LafontProp.addLeftUnitRow_isSoundOverMatrices
#print axioms FX1Poly.Polygraph.Omega.LafontProp.addRightUnitRow_isSoundOverMatrices
#print axioms FX1Poly.Polygraph.Omega.LafontProp.addCommutativityRow_isSoundOverMatrices
#print axioms FX1Poly.Polygraph.Omega.LafontProp.copyCoassociativityRow_isSoundOverMatrices
#print axioms FX1Poly.Polygraph.Omega.LafontProp.copyLeftCounitRow_isSoundOverMatrices
#print axioms FX1Poly.Polygraph.Omega.LafontProp.copyRightCounitRow_isSoundOverMatrices
#print axioms FX1Poly.Polygraph.Omega.LafontProp.copyCocommutativityRow_isSoundOverMatrices
#print axioms FX1Poly.Polygraph.Omega.LafontProp.copyAfterAddBimonoidRow_isSoundOverMatrices
#print axioms FX1Poly.Polygraph.Omega.LafontProp.copyAfterZeroBimonoidRow_isSoundOverMatrices
#print axioms FX1Poly.Polygraph.Omega.LafontProp.discardAfterAddBimonoidRow_isSoundOverMatrices
#print axioms FX1Poly.Polygraph.Omega.LafontProp.discardAfterZeroBimonoidRow_isSoundOverMatrices
#print axioms FX1Poly.Polygraph.Omega.LafontProp.swapInvolutionRow_isSoundOverMatrices
#print axioms FX1Poly.Polygraph.Omega.LafontProp.swapYangBaxterRow_isSoundOverMatrices
#print axioms FX1Poly.Polygraph.Omega.LafontProp.swapPastAddNaturalityRow_isSoundOverMatrices
#print axioms FX1Poly.Polygraph.Omega.LafontProp.swapPastZeroNaturalityRow_isSoundOverMatrices
#print axioms FX1Poly.Polygraph.Omega.LafontProp.copyPastSwapNaturalityRow_isSoundOverMatrices
#print axioms FX1Poly.Polygraph.Omega.LafontProp.discardPastSwapNaturalityRow_isSoundOverMatrices
#print axioms FX1Poly.Polygraph.Omega.LafontProp.relationDiffGatePasses
#print axioms FX1Poly.Polygraph.Omega.LafontProp.unitRowRightSidesAreBareIdentity
#print axioms FX1Poly.Polygraph.Omega.LafontProp.refutedUnitPairMatchesAddRightUnitRow
#print axioms FX1Poly.Polygraph.Omega.LafontProp.refutedUnitPairIsNowConvertible
#print axioms FX1Poly.Polygraph.Omega.LafontProp.refutedUnitPairHasEqualMatrices
#print axioms FX1Poly.Polygraph.Omega.LafontProp.mirrorUnitPairIsNowConvertible
#print axioms FX1Poly.Polygraph.Omega.LafontProp.refutedAssociativityPairMatchesRow
#print axioms FX1Poly.Polygraph.Omega.LafontProp.refutedAssociativityPairIsNowConvertible
#print axioms FX1Poly.Polygraph.Omega.LafontProp.refutedAssociativityPairHasEqualMatrices
#print axioms FX1Poly.Polygraph.Omega.LafontProp.derivedZeroThenLeftUnitChainConverts

end FX1PolyAudit
