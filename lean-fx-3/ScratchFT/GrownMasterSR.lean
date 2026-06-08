import FX1Poly.Typed.HasTypeDescPiSubjectReductionArms
import FX1Poly.Typed.HasTypeDescPiSubjectReductionInlineArms
import FX1Poly.Typed.HasTypeDescSubjectReduction
import FX1Poly.Typed.HasTypeDescPiFormationCodomainReTyping
import FX1Poly.Core.StepInversion

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

/-- Probe: the grown master SR dispatcher, conditional on a global grown codomain re-typing. -/
theorem HasTypeDescPi.subjectReductionProbe {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {subject classifier : RawTerm scope}
    (codomainReTyping : ∀ {innerScope : Nat} {innerContext : TypingContext profile innerScope}
        {domainCode domainReduct : RawTerm innerScope} {codomainCode : RawTerm (innerScope + 1)}
        {codomainLevel : LevelExpr} {codomainFlag : UniverseFlag},
      Step domainCode domainReduct →
        HasTypeDescPi profile (innerContext.cons domainCode) codomainCode
            (universeCodeCell codomainLevel codomainFlag) →
          HasTypeDescPi profile (innerContext.cons domainReduct) codomainCode
            (universeCodeCell codomainLevel codomainFlag))
    (derivation : HasTypeDescPi profile context subject classifier) :
    ∀ (reduct : RawTerm scope), Step subject reduct →
      HasTypeDescPi profile context reduct classifier :=
  match derivation with
  | .ofFormation formationTyped => fun _reduct step =>
      (formationTyped.subjectAdmitsNoStep _ step).elim
  | .conv levelExpr flag typed converts reclassifierTyped => fun reduct step =>
      HasTypeDescPi.conv levelExpr flag
        (HasTypeDescPi.subjectReductionProbe codomainReTyping typed reduct step) converts
        reclassifierTyped
  | .piIntro domainLevel codomainLevel flag domainTyped codomainTyped bodyTyped =>
      fun _reduct step =>
        HasTypeDescPi.subjectReductionPiIntroArm domainTyped codomainTyped step
          (fun bodyStep =>
            HasTypeDescPi.subjectReductionProbe codomainReTyping bodyTyped _ bodyStep)
  | .piElim functionTyped argumentTyped => fun _reduct step => by
      sorry
  | .genFormationPi context generator payload children levels flag rule isFormation premises =>
      fun _reduct step => by
      sorry

end FX1Poly.Typed
