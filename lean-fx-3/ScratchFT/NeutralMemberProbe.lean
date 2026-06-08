import FX1Poly.Core.CanonicalFormsCandidate
import FX1Poly.Core.NeutralStepClosure
import FX1Poly.Core.StrongNormalizationLeaves

namespace FX1Poly.Core
open StepStar

/-- A strongly-normalizing NEUTRAL term is a member of every canonical-forms candidate. -/
theorem CanonicalFormsPredicate.memberOfStronglyNormalizingNeutral {scope : Nat}
    {isValue : RawTerm scope → Prop} {term : RawTerm scope}
    (termStronglyNormalizing : IsStronglyNormalizing term)
    (termIsNeutral : IsNeutral term) :
    CanonicalFormsPredicate isValue term := by
  revert termIsNeutral
  induction termStronglyNormalizing with
  | intro currentTerm _accessibility inductiveHypothesis =>
      intro currentIsNeutral
      exact CanonicalFormsPredicate.neutralExpansion currentIsNeutral
        (fun reduct stepToReduct =>
          inductiveHypothesis reduct stepToReduct (currentIsNeutral.closedUnderStep stepToReduct))

-- smoke: the generic lemma re-derives containsVariable
example {scope : Nat} {isValue : RawTerm scope → Prop} (index : Fin scope) :
    CanonicalFormsPredicate isValue (.mkGen .gen_var index .childNil) :=
  CanonicalFormsPredicate.memberOfStronglyNormalizingNeutral
    (var_isStronglyNormalizing index) (IsNeutral.var index)

#print axioms CanonicalFormsPredicate.memberOfStronglyNormalizingNeutral

end FX1Poly.Core
