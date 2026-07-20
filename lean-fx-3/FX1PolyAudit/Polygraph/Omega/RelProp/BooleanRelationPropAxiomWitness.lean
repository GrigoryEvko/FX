import FX1Poly.Polygraph.Omega.RelProp.BooleanRelationProp

/-! # FX1PolyAudit.Polygraph.Omega.RelProp.BooleanRelationPropAxiomWitness —
independent #print axioms

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the
fuel-based `#assert_no_axioms` gates in the per-file twin) over the headline declarations of the
WP-REL round: the Boolean-matrix denotation, the SPECIAL FROBENIUS soundness (the rig-flip
`copy;merge = id`), the full congruence-closure soundness lift, the decision procedure and its
negative direction, the walled Carboni-Walters completeness owner marker, and the four ground fires.
Each must print "does not depend on any axioms". -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.Omega.RelProp.denoteBoolEntries
#print axioms FX1Poly.Polygraph.Omega.RelProp.copyThenMergeIsIdentityEntry
#print axioms FX1Poly.Polygraph.Omega.RelProp.specialFrobeniusRowIsSound
#print axioms FX1Poly.Polygraph.Omega.RelProp.convertibleRelDiagramsDenoteEqualBoolMatrices
#print axioms FX1Poly.Polygraph.Omega.RelProp.decideRelConvBool
#print axioms FX1Poly.Polygraph.Omega.RelProp.decisionIsImpliedByRelConv
#print axioms FX1Poly.Polygraph.Omega.RelProp.notRelConvOfDistinctBoolMatrices
#print axioms FX1Poly.Polygraph.Omega.RelProp.carboniWaltersCompletenessStatement
#print axioms FX1Poly.Polygraph.Omega.RelProp.rcwHasCarboniWaltersCompleteness
#print axioms FX1Poly.Polygraph.Omega.RelProp.fireCopyBoolMatrix
#print axioms FX1Poly.Polygraph.Omega.RelProp.fireCapBoolMatrixAndDefinition
#print axioms FX1Poly.Polygraph.Omega.RelProp.fireSpecialFrobeniusDecidesTrue
#print axioms FX1Poly.Polygraph.Omega.RelProp.fireIdentityVersusSwapDecidesFalse
#print axioms FX1Poly.Polygraph.Omega.RelProp.fireIdentityNotConvertibleToSwap

end FX1PolyAudit
