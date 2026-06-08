import FX1Poly.Typed.SimplyTypedConvDecision

/-! Scratch probe: Milestone A0 defensible-kernel artifact over the unconditional simply-typed fragment.
    (1) extract the bare-closed SN as a standalone reusable lemma (currently only inline in the decider);
    (2) name the unconditional decidable Conv as the A0 headline. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe StepStar

theorem simplyTypedBareClosedStronglyNormalizing {profile : PolyProfile}
    {term type : RawTerm 0}
    (typed : SimplyTypedTermLF (TypingContext.empty : TypingContext profile 0) term type) :
    IsStronglyNormalizing term :=
  StepStar.stronglyNormalizing_of_subst emptyClosingSubst term
    (typed.stronglyNormalizingClosed emptyClosingSubst)

def milestoneA0SimplyTypedConvDecidable {profile : PolyProfile}
    {firstTerm firstType secondTerm secondType : RawTerm 0}
    (firstTyped : SimplyTypedTermLF (TypingContext.empty : TypingContext profile 0) firstTerm firstType)
    (secondTyped : SimplyTypedTermLF (TypingContext.empty : TypingContext profile 0) secondTerm secondType) :
    Decidable (Conv firstTerm secondTerm) :=
  Conv.decidableOfSimplyTypedBareClosed firstTyped secondTyped

#print axioms simplyTypedBareClosedStronglyNormalizing
#print axioms milestoneA0SimplyTypedConvDecidable

end FX1Poly.Typed
