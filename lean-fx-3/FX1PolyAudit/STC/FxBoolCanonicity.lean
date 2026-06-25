import FX1PolyAudit.DependencyAudit
import FX1Poly.STC.FxBoolCanonicity

/-! # FX1PolyAudit.STC.FxBoolCanonicity — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.STC.ClosedTypedBool
#assert_no_axioms FX1Poly.STC.ReachesCanonicalBool
#assert_no_axioms FX1Poly.STC.fxStcBoolRelation
#assert_no_axioms FX1Poly.STC.canonicityViaSTC
#assert_no_axioms FX1Poly.STC.canonicityViaSTC_extracts
#assert_no_axioms FX1Poly.STC.canonicityViaSTC_semantic_isKernelWitness
#assert_no_axioms FX1Poly.STC.grownOnlyBoolGlue_isVacuous
#assert_no_axioms FX1Poly.STC.closedTypedBool_grownArm_isVacuous
#assert_no_axioms FX1Poly.STC.boolTrueClosedTyped
#assert_no_axioms FX1Poly.STC.canonicityViaSTC_boolTrue_nonVacuous

end FX1PolyAudit
