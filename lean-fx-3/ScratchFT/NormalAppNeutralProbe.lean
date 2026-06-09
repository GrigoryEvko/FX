import FX1Poly.Typed.NeutralClassifierUnique
import FX1Poly.Typed.PinnedReflectionPiElimDispatcher

/-! Probe: E2.7 app-arm closure — a NORMAL grown-typed application is NEUTRAL (its function is
λ-or-neutral by the wf-free canonical forms; λ would make the app a β-redex, contradicting
normality), so classifier-class uniqueness extends from neutrals to ALL normal applications. -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

theorem HasTypeDescPi.normalAppIsNeutral {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {functionTerm argument classifier : RawTerm scope}
    (typed : HasTypeDescPi profile context (appCell functionTerm argument) classifier)
    (normal : RawTerm.isStepNormalForm (appCell functionTerm argument)) :
    IsNeutral (appCell functionTerm argument) := by
  obtain ⟨domainCode, codomainCode, functionTyped, _argumentTyped, _classifierConv⟩ :=
    HasTypeDescPi.invertApp typed
  have functionNormal : RawTerm.isStepNormalForm functionTerm :=
    appNormal_functionNormal functionTerm argument normal
  rcases HasTypeDescPi.normalFunctionIsLambdaOrNeutralOfTyping functionTyped functionNormal with
    ⟨body, bodyEq⟩ | functionNeutral
  · rw [bodyEq] at normal
    exact (RawTerm.not_isStepNormalForm_beta_smoke body argument normal).elim
  · exact IsNeutral.app functionNeutral

theorem HasTypeDescPi.normalAppClassifierUnique {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope} {functionTerm argument : RawTerm scope}
    {firstClassifier secondClassifier : RawTerm scope}
    (normal : RawTerm.isStepNormalForm (appCell functionTerm argument))
    (firstTyped : HasTypeDescPi profile context (appCell functionTerm argument) firstClassifier)
    (secondTyped :
      HasTypeDescPi profile context (appCell functionTerm argument) secondClassifier) :
    Conv firstClassifier secondClassifier :=
  HasTypeDescPi.neutralClassifierUnique
    (HasTypeDescPi.normalAppIsNeutral firstTyped normal) firstTyped secondTyped

end FX1Poly.Typed

#print axioms FX1Poly.Typed.HasTypeDescPi.normalAppIsNeutral
#print axioms FX1Poly.Typed.HasTypeDescPi.normalAppClassifierUnique
