import FX1PolyAudit.DependencyAudit
import FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationListElim

/-! # FX1PolyAudit.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationListElim

Zero-axiom audit shard mirroring kernel module `FX1Poly.Core.Metatheory.Normalization.StrongNorm.StrongNormalizationListElim`.
Each declaration below must be free of `propext`, `Quot.sound`,
`Classical.choice`, `sorry`, `native_decide`, `omega`. -/

namespace FX1PolyAudit

-- Recursive-eliminator iota-redex SN, second data type (List): the two listCons subterm-SN projections
-- (head/tail of an SN cons are SN) and the conditional listElim cons-case redex SN (normal branches + the
-- triple-app cons-contractum SN for every SN head/tail implies the listElim redex with an SN scrutinee is SN).
-- Same IH-carrying contractum premise as natElim; the cons scrutinee is 2-child.
#assert_no_axioms FX1Poly.Core.StepStar.headValue_isStronglyNormalizing_of_listCons

#assert_no_axioms FX1Poly.Core.StepStar.tailValue_isStronglyNormalizing_of_listCons

#assert_no_axioms FX1Poly.Core.StepStar.listElim_isStronglyNormalizing_of_normal_branches

-- The SN-from-SN-branches form for the listElim closed-membership: the list twin of the natElim
-- SN-from-SN-branches recursor.  Triple nested accessibility induction; the cons-contractum SN hypothesis (over
-- head + tail) is threaded through both branch inductions: nilBranch one hop (recursive listElim), consBranch
-- two hops (app (app consBranch head) tail, three app layers deep, and the recursive listElim).
#assert_no_axioms FX1Poly.Core.StepStar.listElim_isStronglyNormalizing_of_strongly_normalizing_branches

end FX1PolyAudit
