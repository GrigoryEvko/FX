import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationMatch

/-! # FX1PolyAudit.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationMatch

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationMatch`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Non-recursive applied-branch eliminator iota-redex SN (optionMatch / eitherMatch): the three one-child
-- value subterm-SN lemmas (value of an SN optionSome/eitherInl/eitherInr is SN), and the two conditional
-- firing-case redex SN (normal branches + the applied `app branch value` contractum SN for every SN value
-- implies the matcher redex with an SN scrutinee is SN).  Covers the firing-case eliminator SN across
-- passive/recursive/applied-non-recursive shapes.
#assert_no_axioms FX1Poly.Core.StepStar.value_isStronglyNormalizing_of_optionSome

#assert_no_axioms FX1Poly.Core.StepStar.value_isStronglyNormalizing_of_eitherInl

#assert_no_axioms FX1Poly.Core.StepStar.value_isStronglyNormalizing_of_eitherInr

#assert_no_axioms FX1Poly.Core.StepStar.optionMatch_isStronglyNormalizing_of_normal_branches

#assert_no_axioms FX1Poly.Core.StepStar.eitherMatch_isStronglyNormalizing_of_normal_branches

-- The SN-from-SN-branches form for the optionMatch/eitherMatch closed-membership: the branches need only be
-- SN (members), not normal, as the Tait/data-candidate eliminator argument requires.  Triple nested
-- accessibility induction; the applied-branch contractum SN hypothesis (for all value, SN value implies
-- SN (app branch value)) is threaded through the branch induction, updated under branch-congruence via
-- app-head Step.cong + IsStronglyNormalizing.inv.  eitherMatch threads both left and right contractums.
#assert_no_axioms FX1Poly.Core.StepStar.optionMatch_isStronglyNormalizing_of_strongly_normalizing_branches

#assert_no_axioms FX1Poly.Core.StepStar.eitherMatch_isStronglyNormalizing_of_strongly_normalizing_branches

end FX1PolyAudit
