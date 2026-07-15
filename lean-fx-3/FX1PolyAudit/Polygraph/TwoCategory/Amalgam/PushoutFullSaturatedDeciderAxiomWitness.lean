import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFullSaturatedDecider

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutFullSaturatedDeciderAxiomWitness — independent #print axioms (WP-AMALG)

An INDEPENDENT `#print axioms` cross-check (a separate mechanism and a separate file from the
fuel-based `#assert_no_axioms` gate in the per-file twin) over every declaration of the completeness, the total two-sided decider, and the real-relation saturated dispatch inhabitant.
Each must print "does not depend on any axioms".  Registered in `AuditAll`. -/

namespace FX1PolyAudit

#print axioms FX1Poly.Polygraph.Amalgam.conv_uncast
#print axioms FX1Poly.Polygraph.Amalgam.arityFold_castBoundary
#print axioms FX1Poly.Polygraph.Amalgam.arityFold_wallFreeCellInvert
#print axioms FX1Poly.Polygraph.Amalgam.wallFreePayload_conv_of_foldEq
#print axioms FX1Poly.Polygraph.Amalgam.slotDomRuns_aligned_of_lengths
#print axioms FX1Poly.Polygraph.Amalgam.slotCodRuns_aligned_of_lengths
#print axioms FX1Poly.Polygraph.Amalgam.flatDom_slots_aligned
#print axioms FX1Poly.Polygraph.Amalgam.flatCod_slots_aligned
#print axioms FX1Poly.Polygraph.Amalgam.castBoundary_hcomp_distribute_both
#print axioms FX1Poly.Polygraph.Amalgam.flatSlotsDom_congr
#print axioms FX1Poly.Polygraph.Amalgam.flatSlotsCod_congr
#print axioms FX1Poly.Polygraph.Amalgam.flatConv_of_aligned
#print axioms FX1Poly.Polygraph.Amalgam.pushoutConvOfFoldEq
#print axioms FX1Poly.Polygraph.Amalgam.pushoutFullSaturatedDecider
#print axioms FX1Poly.Polygraph.Amalgam.involutionMonadGeneratorsDisjoint
#print axioms FX1Poly.Polygraph.Amalgam.involutionMonadRealSaturatedDispatch
#print axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasRealRelationSaturatedDispatchInhabitant

end FX1PolyAudit
