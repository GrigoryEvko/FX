import FX1Poly.Core.CanonicalFormsCandidate

namespace FX1Poly.Core

open StepStar

-- Value-reaching weak-head expansion for the data candidate: a term stepping to a value-reaching
-- contractum, itself SN, is a member via the reduces-to-value disjunct.
theorem weakHeadExpansionOfValueReaching_probe {scope : Nat} {isValue : RawTerm scope → Prop}
    {redexTerm contractum : RawTerm scope}
    (redexStepsToContractum : Step redexTerm contractum)
    (redexStronglyNormalizing : IsStronglyNormalizing redexTerm)
    (contractumReachesValue : ∃ value : RawTerm scope, StepStar contractum value ∧ isValue value) :
    CanonicalFormsPredicate isValue redexTerm := by
  obtain ⟨value, contractumToValue, valueIsValue⟩ := contractumReachesValue
  exact ⟨redexStronglyNormalizing,
    Or.inr ⟨value, StepStar.trans redexStepsToContractum contractumToValue, valueIsValue⟩⟩

-- StepStar (multi-step) version — the reusable form (redex reduces-to contractum by any chain).
theorem ofStepStarReachingValue_probe {scope : Nat} {isValue : RawTerm scope → Prop}
    {redexTerm contractum : RawTerm scope}
    (redexReachesContractum : StepStar redexTerm contractum)
    (redexStronglyNormalizing : IsStronglyNormalizing redexTerm)
    (contractumReachesValue : ∃ value : RawTerm scope, StepStar contractum value ∧ isValue value) :
    CanonicalFormsPredicate isValue redexTerm := by
  obtain ⟨value, contractumToValue, valueIsValue⟩ := contractumReachesValue
  exact ⟨redexStronglyNormalizing,
    Or.inr ⟨value, redexReachesContractum.trans_compose contractumToValue, valueIsValue⟩⟩

-- Member-shaped form: a step to a member contractum that is not neutral lifts to the redex.
theorem weakHeadExpansionOfMemberNotNeutral_probe {scope : Nat} {isValue : RawTerm scope → Prop}
    {redexTerm contractum : RawTerm scope}
    (redexStepsToContractum : Step redexTerm contractum)
    (redexStronglyNormalizing : IsStronglyNormalizing redexTerm)
    (contractumMember : CanonicalFormsPredicate isValue contractum)
    (contractumNotNeutral : ¬ IsNeutral contractum) :
    CanonicalFormsPredicate isValue redexTerm := by
  rcases contractumMember.2 with contractumIsNeutral | contractumReachesValue
  · exact (contractumNotNeutral contractumIsNeutral).elim
  · exact weakHeadExpansionOfValueReaching_probe redexStepsToContractum
      redexStronglyNormalizing contractumReachesValue

end FX1Poly.Core

#print axioms FX1Poly.Core.weakHeadExpansionOfValueReaching_probe
#print axioms FX1Poly.Core.ofStepStarReachingValue_probe
#print axioms FX1Poly.Core.weakHeadExpansionOfMemberNotNeutral_probe
