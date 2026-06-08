import FX1Poly.Typed.OpenStronglyNormalizingBetaEta
import FX1Poly.Core.StepBetaEtaConfluence

namespace FX1Poly.Typed.Spike
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

end FX1Poly.Typed.Spike

#print axioms FX1Poly.Typed.Spike.subjectBetaEtaConfluenceOfWfContext
