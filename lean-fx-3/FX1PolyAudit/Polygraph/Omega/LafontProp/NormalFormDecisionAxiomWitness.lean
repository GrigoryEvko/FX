import FX1Poly.Polygraph.Omega.LafontProp.DiagramDecisionFires

/-! # FX1PolyAudit.Polygraph.Omega.LafontProp.NormalFormDecisionAxiomWitness —
independent #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the
fuel-based `#assert_no_axioms` gates in the per-file twins) over the headline declarations of
the LAFONT-PROP r2 round: the ladder and canonical-form soundness theorems, THE REDUCTION
THEOREM (completeness reduces to the canonical-reduction residual), THE CONGRUENCE SOUNDNESS
THEOREM (residual 1 discharged), the decision procedure's three-way status, all decision fires
(including the equal-normal-form kernel pins), and the machine-checked NON-convertibility of
the Z2-only pair.  Each must print "does not depend on any axioms".  Registered in
`AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.Omega.LafontProp.mergeColumnFanDenotesWithin
#print axioms FX1Poly.Polygraph.Omega.LafontProp.canonicalDiagramDenotesEntriesWithin
#print axioms FX1Poly.Polygraph.Omega.LafontProp.canonicalFormIsSoundOverMatrices
#print axioms FX1Poly.Polygraph.Omega.LafontProp.normalFormPreservesDenotation
#print axioms FX1Poly.Polygraph.Omega.LafontProp.equalMatricesGiveEqualNormalForms
#print axioms FX1Poly.Polygraph.Omega.LafontProp.completenessReducesToCanonicalReduction
#print axioms FX1Poly.Polygraph.Omega.LafontProp.canonicalFormOfSwapMatrixIsSound
#print axioms FX1Poly.Polygraph.Omega.LafontProp.canonicalFormOfDoublingMatrixIsSound
#print axioms FX1Poly.Polygraph.Omega.LafontProp.normalFormOfBimonoidSquareLeftSideIsSound
#print axioms FX1Poly.Polygraph.Omega.LafontProp.convertibleDiagramsDenoteEqualMatrices
#print axioms FX1Poly.Polygraph.Omega.LafontProp.convertibilityMatrixSoundnessHolds
#print axioms FX1Poly.Polygraph.Omega.LafontProp.notConvertibleOfDistinctMatrices
#print axioms FX1Poly.Polygraph.Omega.LafontProp.derivedChainMatricesAgreeViaSoundness
#print axioms FX1Poly.Polygraph.Omega.LafontProp.decisionRefutesConvertibility
#print axioms FX1Poly.Polygraph.Omega.LafontProp.decisionIsImpliedByConvertibility
#print axioms FX1Poly.Polygraph.Omega.LafontProp.decisionAffirmsConvertibilityGivenCanonicalReduction
#print axioms FX1Poly.Polygraph.Omega.LafontProp.unitPairDecisionFires
#print axioms FX1Poly.Polygraph.Omega.LafontProp.unitPairNormalFormsCoincide
#print axioms FX1Poly.Polygraph.Omega.LafontProp.unitPairDecisionAgreesWithConversion
#print axioms FX1Poly.Polygraph.Omega.LafontProp.associativityPairDecisionFires
#print axioms FX1Poly.Polygraph.Omega.LafontProp.associativityPairNormalFormsCoincide
#print axioms FX1Poly.Polygraph.Omega.LafontProp.spiderDenotesTripling
#print axioms FX1Poly.Polygraph.Omega.LafontProp.spiderPairDecisionFires
#print axioms FX1Poly.Polygraph.Omega.LafontProp.spiderPairIsConvertible
#print axioms FX1Poly.Polygraph.Omega.LafontProp.spiderPairNormalFormsCoincide
#print axioms FX1Poly.Polygraph.Omega.LafontProp.tripleSwapDecisionFires
#print axioms FX1Poly.Polygraph.Omega.LafontProp.tripleSwapIsConvertibleToSwap
#print axioms FX1Poly.Polygraph.Omega.LafontProp.tripleSwapNormalFormsCoincide
#print axioms FX1Poly.Polygraph.Omega.LafontProp.yangBaxterDecisionFires
#print axioms FX1Poly.Polygraph.Omega.LafontProp.yangBaxterNormalFormsCoincide
#print axioms FX1Poly.Polygraph.Omega.LafontProp.bimonoidSquareDecisionFires
#print axioms FX1Poly.Polygraph.Omega.LafontProp.bimonoidSquareNormalFormsCoincide
#print axioms FX1Poly.Polygraph.Omega.LafontProp.zSpecificPairDecisionRefutes
#print axioms FX1Poly.Polygraph.Omega.LafontProp.zSpecificPairIsNotConvertible

end FX1PolyAudit
