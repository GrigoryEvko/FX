import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.BetaRedexStrongNormalization

/-! # FX1PolyAudit.Core.Metatheory.Normalization.StrongNorm.BetaRedexStrongNormalization

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Metatheory.Normalization.StrongNorm.BetaRedexStrongNormalization`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Single-contractum beta-redex SN (neutral arm of the member weak-head beta-expansion, the denote
-- lambda-arm engine): app (lam body) arg is SN given lam body, arg, and the single contractum subst0 body arg
-- are SN (body free to step).  Unlike the appLam family that fixes a normal body or demands a uniform
-- contractum-SN over all reducts, this needs only the single contractum, recovering the body-reduct contractums
-- by descendStepStar along StepStar.subst0Body.  stepStarLamInversion (a StepStar chain out of a lambda lands
-- on a lambda, body chain recovered) is the reusable supporting substrate.
#assert_no_axioms FX1Poly.Core.stepStarLamInversion

#assert_no_axioms FX1Poly.Core.stepStarLamBodyChain

#assert_no_axioms FX1Poly.Core.appLam_isStronglyNormalizing_of_contractum

end FX1PolyAudit
