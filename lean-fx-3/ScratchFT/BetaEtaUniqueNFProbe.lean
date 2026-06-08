import FX1Poly.Typed.OpenStronglyNormalizingBetaEta
import FX1Poly.Core.StepBetaEtaConfluence

namespace FX1Poly.Core.Spike2

/-- βη star-rigidity: a βη-star chain out of a term with no βη-step is trivial. -/
theorem eq_of_noBetaEtaStep {scope : Nat} {startTerm endTerm : RawTerm scope}
    (noStep : ∀ reduct, ¬ Step.betaEta startTerm reduct)
    (chain : Step.betaEtaStar startTerm endTerm) :
    startTerm = endTerm := by
  cases chain with
  | refl => rfl
  | trans firstStep _ => exact absurd firstStep (noStep _)

end FX1Poly.Core.Spike2

namespace FX1Poly.Typed.Spike2
open FX1Poly.Core

theorem subjectBetaEtaConfluenceOfWfContext {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (contextWellFormed : WfContext context)
    (typed : HasTypeDescPi profile context subject classifier)
    {leftReduct rightReduct : RawTerm scope}
    (subjectToLeft : Step.betaEtaStar subject leftReduct)
    (subjectToRight : Step.betaEtaStar subject rightReduct) :
    Step.betaEtaStar.Join leftReduct rightReduct :=
  Step.betaEtaStar.confluence_of_localJoin_and_accessible
    (HasTypeDescPi.betaEtaStronglyNormalizingOfWfContext contextWellFormed typed)
    subjectToLeft subjectToRight

theorem uniqueBetaEtaNormalFormOfWfContext {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (contextWellFormed : WfContext context)
    (typed : HasTypeDescPi profile context subject classifier)
    {normalFormLeft normalFormRight : RawTerm scope}
    (subjectToLeft : Step.betaEtaStar subject normalFormLeft)
    (leftNoStep : ∀ reduct, ¬ Step.betaEta normalFormLeft reduct)
    (subjectToRight : Step.betaEtaStar subject normalFormRight)
    (rightNoStep : ∀ reduct, ¬ Step.betaEta normalFormRight reduct) :
    normalFormLeft = normalFormRight := by
  obtain ⟨apex, leftToApex, rightToApex⟩ :=
    subjectBetaEtaConfluenceOfWfContext contextWellFormed typed subjectToLeft subjectToRight
  have leftEqApex : normalFormLeft = apex := FX1Poly.Core.Spike2.eq_of_noBetaEtaStep leftNoStep leftToApex
  have rightEqApex : normalFormRight = apex := FX1Poly.Core.Spike2.eq_of_noBetaEtaStep rightNoStep rightToApex
  exact leftEqApex.trans rightEqApex.symm

end FX1Poly.Typed.Spike2

#print axioms FX1Poly.Core.Spike2.eq_of_noBetaEtaStep
#print axioms FX1Poly.Typed.Spike2.uniqueBetaEtaNormalFormOfWfContext
