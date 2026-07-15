import FX1PolyAudit.DependencyAudit
import FX1Poly.Axis.Term.Subst.RawTermOccurrenceSubstLift

/-! # FX1PolyAudit.Axis.Term.Subst.RawTermOccurrenceSubstLift — zero-axiom gate (mirror shard, region-D restructure) -/

namespace FX1PolyAudit

#assert_no_axioms FX1Poly.Core.occurrenceCountAt_var_of_ne
#assert_no_axioms FX1Poly.Core.occurrenceCountAt_var_succ_eq
#assert_no_axioms FX1Poly.Core.RawTermSubst.lift_hitProfile_succ
#assert_no_axioms FX1Poly.Core.iterateLiftRaw_hitProfile_raised
#assert_no_axioms FX1Poly.Core.RawTerm.occurrenceCountAt_subst_hitProfile
#assert_no_axioms FX1Poly.Core.RawTermChildren.occurrenceCountAt_subst_hitProfile
#assert_no_axioms FX1Poly.Core.RawTermSubst.lift_hitsExactlyAt_zero
#assert_no_axioms FX1Poly.Core.RawTerm.occurrenceCountAt_subst_lift_zeroPosition

end FX1PolyAudit
