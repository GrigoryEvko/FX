import FX1PolyAudit.DependencyAudit
import FX1Poly.Polygraph.TwoCategory.Amalgam.PushoutFullSaturatedDecider

/-! # FX1PolyAudit.Polygraph.TwoCategory.Amalgam.PushoutFullSaturatedDecider — zero-axiom gate (WP-AMALG)

Per-declaration zero-axiom gate for the completeness, the total two-sided decider, and the real-relation saturated dispatch inhabitant.

Must be free of `propext`, `Quot.sound`, `Classical`, `sorry`, `native_decide`, `omega`.
Registered in `AuditAll` (paired with the independent `#print axioms` witness). -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Polygraph.Amalgam.conv_uncast
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityFold_castBoundary
#assert_no_axioms FX1Poly.Polygraph.Amalgam.arityFold_wallFreeCellInvert
#assert_no_axioms FX1Poly.Polygraph.Amalgam.wallFreePayload_conv_of_foldEq
#assert_no_axioms FX1Poly.Polygraph.Amalgam.slotDomRuns_aligned_of_lengths
#assert_no_axioms FX1Poly.Polygraph.Amalgam.slotCodRuns_aligned_of_lengths
#assert_no_axioms FX1Poly.Polygraph.Amalgam.flatDom_slots_aligned
#assert_no_axioms FX1Poly.Polygraph.Amalgam.flatCod_slots_aligned
#assert_no_axioms FX1Poly.Polygraph.Amalgam.castBoundary_hcomp_distribute_both
#assert_no_axioms FX1Poly.Polygraph.Amalgam.flatSlotsDom_congr
#assert_no_axioms FX1Poly.Polygraph.Amalgam.flatSlotsCod_congr
#assert_no_axioms FX1Poly.Polygraph.Amalgam.flatConv_of_aligned
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutConvOfFoldEq
#assert_no_axioms FX1Poly.Polygraph.Amalgam.pushoutFullSaturatedDecider
#assert_no_axioms FX1Poly.Polygraph.Amalgam.involutionMonadGeneratorsDisjoint
#assert_no_axioms FX1Poly.Polygraph.Amalgam.involutionMonadRealSaturatedDispatch
#assert_no_axioms FX1Poly.Polygraph.Amalgam.fxAmalg_hasRealRelationSaturatedDispatchInhabitant

end FX1PolyAudit
