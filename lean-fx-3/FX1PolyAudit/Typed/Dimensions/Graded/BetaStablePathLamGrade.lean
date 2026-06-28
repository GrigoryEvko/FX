import FX1PolyAudit.DependencyAudit
import FX1Poly.Typed.Dimensions.Graded.BetaStablePathLamGrade

/-! # FX1PolyAudit.Typed.Dimensions.Graded.BetaStablePathLamGrade — zero-axiom gate (mirror shard)

The per-declaration `#assert_no_axioms` gate for the beta-stable `pathLam` dimension-usage grade
foundation: the count master equation (the weighted-profile generalization + its instantiation), the
semiring-hom completion (`natToUsageGrade_mulHom`), the omega-scaling arithmetic, the monotonicity
bridge, the beta-stable dimension grade + its premise, and the graded substitution lemma (unconditional
+ parameterized master + omega-blowup witness + ghost instance). -/

namespace FX1PolyAudit

-- The count master equation (Core structural metatheory)
#assert_no_axioms FX1Poly.Core.addExchangeFourWay
#assert_no_axioms FX1Poly.Core.natRightDistribByWeight
#assert_no_axioms FX1Poly.Core.RawTermSubst.hitsWithWeight
#assert_no_axioms FX1Poly.Core.RawTermSubst.lift_hitsWithWeight_succ
#assert_no_axioms FX1Poly.Core.iterateLiftRaw_hitsWithWeight_raised
#assert_no_axioms FX1Poly.Core.RawTerm.occurrenceCountAt_subst_weightProfile
#assert_no_axioms FX1Poly.Core.RawTermChildren.occurrenceCountAt_subst_weightProfile
#assert_no_axioms FX1Poly.Core.RawTermSubst.singleton_hitsWithWeight
#assert_no_axioms FX1Poly.Core.RawTerm.occurrenceCountAt_subst0

-- The grade arithmetic + beta-stable dimension grade (Typed)
#assert_no_axioms FX1Poly.Typed.natToUsageGrade_mulHom
#assert_no_axioms FX1Poly.Typed.UsageGrade.omega_mul_one_eq_omega
#assert_no_axioms FX1Poly.Typed.UsageGrade.one_mul_omega_eq_omega
#assert_no_axioms FX1Poly.Typed.UsageGrade.omega_not_le_one
#assert_no_axioms FX1Poly.Typed.natToUsageGrade_monotone
#assert_no_axioms FX1Poly.Typed.RawTerm.dimensionUsageGrade
#assert_no_axioms FX1Poly.Typed.RawTerm.bodyBinderUsageGrade
#assert_no_axioms FX1Poly.Typed.RawTerm.affineBinderGradePremise
#assert_no_axioms FX1Poly.Typed.affineBinderGradePremise_iff_gradedBinderChecks
#assert_no_axioms FX1Poly.Typed.dimensionUsageGrade_subst0_master
#assert_no_axioms FX1Poly.Typed.dimensionUsageGrade_subst0
#assert_no_axioms FX1Poly.Typed.dimensionUsageGrade_subst0_omegaBlowup
#assert_no_axioms FX1Poly.Typed.dimensionUsageGrade_subst0_ghost

end FX1PolyAudit
