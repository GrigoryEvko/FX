import FX1Poly.Polygraph.Omega.Quantale.WeightedQuantaleProp

/-! # FX1PolyAudit.Polygraph.Omega.Quantale.WeightedQuantalePropAxiomWitness —
independent #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the
fuel-based `#assert_no_axioms` gates in the per-file twin) over the headline declarations of the
WP-QUANTALE round: the finite quantale carrier and its tensor/distributivity laws, the
quantale-matrix denotation, the weighted-composition and special-Frobenius row soundness, the full
congruence-closure soundness lift, the decision procedure and its negative direction, the walled
quantale presentation-completeness owner marker, and the ground fires.  Each must print "does not
depend on any axioms". -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.Omega.QuantaleProp.QuantaleThree
#print axioms FX1Poly.Polygraph.Omega.QuantaleProp.joinQ
#print axioms FX1Poly.Polygraph.Omega.QuantaleProp.tensorQ
#print axioms FX1Poly.Polygraph.Omega.QuantaleProp.tensorAssocQ
#print axioms FX1Poly.Polygraph.Omega.QuantaleProp.tensorJoinDistribLeftQ
#print axioms FX1Poly.Polygraph.Omega.QuantaleProp.denoteQEntries
#print axioms FX1Poly.Polygraph.Omega.QuantaleProp.weightComposeRowIsSound
#print axioms FX1Poly.Polygraph.Omega.QuantaleProp.specialFrobeniusRowIsSound
#print axioms FX1Poly.Polygraph.Omega.QuantaleProp.convertibleWeightedDiagramsDenoteEqualQMatrices
#print axioms FX1Poly.Polygraph.Omega.QuantaleProp.decideWeightedConvBool
#print axioms FX1Poly.Polygraph.Omega.QuantaleProp.decisionIsImpliedByWeightedConv
#print axioms FX1Poly.Polygraph.Omega.QuantaleProp.notWeightedConvOfDistinctQMatrices
#print axioms FX1Poly.Polygraph.Omega.QuantaleProp.quantaleCompletenessStatement
#print axioms FX1Poly.Polygraph.Omega.QuantaleProp.qwmHasQuantalePresentationCompleteness
#print axioms FX1Poly.Polygraph.Omega.QuantaleProp.fireWeightMidMatrix
#print axioms FX1Poly.Polygraph.Omega.QuantaleProp.fireWeightTopThenMidDecidesTrue
#print axioms FX1Poly.Polygraph.Omega.QuantaleProp.fireMidVersusTopWeightDecidesFalse
#print axioms FX1Poly.Polygraph.Omega.QuantaleProp.fireMidWeightNotConvertibleToTopWeight
#print axioms FX1Poly.Polygraph.Omega.QuantaleProp.fireTensorDistributesOverJoin
#print axioms FX1Poly.Polygraph.Omega.QuantaleProp.fireSpecialFrobeniusDecidesTrue

end FX1PolyAudit
