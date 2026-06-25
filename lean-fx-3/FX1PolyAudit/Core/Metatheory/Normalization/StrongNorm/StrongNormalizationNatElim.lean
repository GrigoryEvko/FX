import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationNatElim

/-! # FX1PolyAudit.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationNatElim

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationNatElim`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Recursive-eliminator iota-redex SN: the natSucc one-child subterm-SN lemma (predecessor of an SN natSucc
-- is SN), and the conditional natElim successor-case redex SN (normal branches + the succ-contractum SN for
-- every SN predecessor implies the natElim redex with an SN scrutinee is SN).  The succ-contractum hypothesis
-- is the IH-carrying premise the numeral WF-recursion supplies.
#assert_no_axioms FX1Poly.Core.StepStar.predecessor_isStronglyNormalizing_of_natSucc

#assert_no_axioms FX1Poly.Core.StepStar.natElim_isStronglyNormalizing_of_normal_branches

-- natRec (dependent recursor) firing-case twin, completing the Nat recursor pair.
#assert_no_axioms FX1Poly.Core.StepStar.natRec_isStronglyNormalizing_of_normal_branches

-- The SN-from-SN-branches form for the recursor closed-membership: the branches need only be SN (members),
-- not normal, as the Tait/data-candidate recursor argument requires.  Triple nested accessibility induction on
-- (scrutinee, zeroBranch, succBranch); the succ-contractum SN hypothesis is threaded through both branch
-- inductions.  The recursive analogue of the matcher SN-from-SN-branches: the succ iota-contractum contains a
-- recursive natElim/natRec call, and the succ branch occurs twice (in app succBranch pred and the recursive
-- call), so its update under succ-congruence is two app/natElim-cong + IsStronglyNormalizing.inv hops.
#assert_no_axioms FX1Poly.Core.StepStar.natElim_isStronglyNormalizing_of_strongly_normalizing_branches

#assert_no_axioms FX1Poly.Core.StepStar.natRec_isStronglyNormalizing_of_strongly_normalizing_branches

end FX1PolyAudit
