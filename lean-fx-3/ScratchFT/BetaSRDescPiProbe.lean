import FX1Poly.Typed.HasTypeDescPiBetaSR
import FX1Poly.Typed.HasTypeDescPiClassifierValidity
import FX1Poly.Typed.HasTypeDescPiSubjectReductionInlineArms

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

-- (1) beta subject reduction over the GROWN well-formedness WfContextDescPi: mechanical swap of the lone
-- WfContext use (classifierIsTypeDesc) to the grown classifierIsTypeDescPi.
theorem HasTypeDescPi.betaSubjectReductionDescPi {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {body : RawTerm (scope + 1)} {argument classifier : RawTerm scope}
    (redexTyped : HasTypeDescPi profile context (appCell (lamCell body) argument) classifier)
    (wellFormed : WfContextDescPi context) :
    HasTypeDescPi profile context (RawTerm.subst0 body argument) classifier := by
  obtain ⟨domainCode, codomainCode, functionTyped, argumentTyped, convClassifierToOutput⟩ :=
    redexTyped.invertApp
  obtain ⟨lamDomainCode, lamCodomainCode, lamDomainLevel, lamCodomainLevel, lamFlag,
      convPiToPi, lamDomainTyped, _lamCodomainTyped, bodyTyped⟩ :=
    functionTyped.invertLam
  obtain ⟨convDomain, convCodomain⟩ := Conv.piTyCode_inj convPiToPi
  have argumentTypedAtLamDomain :
      HasTypeDescPi profile context argument lamDomainCode :=
    HasTypeDescPi.conv lamDomainLevel lamFlag argumentTyped convDomain lamDomainTyped
  have reductTyped :
      HasTypeDescPi profile context (RawTerm.subst0 body argument)
        (RawTerm.subst0 lamCodomainCode argument) :=
    HasTypeDescPi.substituteUnderBinding argument bodyTyped argumentTypedAtLamDomain
  have convReductOutputToClassifier :
      Conv (RawTerm.subst0 lamCodomainCode argument) classifier :=
    Conv.trans (Conv.subst0 convCodomain.sym (Conv.refl argument)) convClassifierToOutput.sym
  obtain ⟨classifierLevel, classifierFlag, classifierTyped⟩ :=
    redexTyped.classifierIsTypeDescPi wellFormed
  exact HasTypeDescPi.conv classifierLevel classifierFlag reductTyped
    convReductOutputToClassifier classifierTyped

-- (2) the dispatcher's piElim SR arm over WfContextDescPi (swaps betaSubjectReduction → DescPi twin and
-- classifierIsTypeDesc → classifierIsTypeDescPi).
theorem HasTypeDescPi.subjectReductionPiElimArmDescPi {profile : PolyProfile} {scope : Nat}
    {context : TypingContext profile scope}
    {functionTerm argument : RawTerm scope}
    {domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    {reduct : RawTerm scope}
    (functionTyped : HasTypeDescPi profile context functionTerm (piTyCodeCell domainCode codomainCode))
    (argumentTyped : HasTypeDescPi profile context argument domainCode)
    (step : Step (appCell functionTerm argument) reduct)
    (functionSR : ∀ {functionReduct : RawTerm scope},
      Step functionTerm functionReduct →
        HasTypeDescPi profile context functionReduct (piTyCodeCell domainCode codomainCode))
    (argumentSR : ∀ {argumentReduct : RawTerm scope},
      Step argument argumentReduct → HasTypeDescPi profile context argumentReduct domainCode)
    (wellFormed : WfContextDescPi context) :
    HasTypeDescPi profile context reduct (RawTerm.subst0 codomainCode argument) := by
  rcases Step.from_app step with ⟨body, functionEq, reductEq⟩ |
      ⟨functionAfter, reductEq, functionStep⟩ | ⟨argumentAfter, reductEq, argumentStep⟩
  · subst functionEq
    subst reductEq
    exact HasTypeDescPi.betaSubjectReductionDescPi
      (HasTypeDescPi.piElim functionTyped argumentTyped) wellFormed
  · subst reductEq
    exact HasTypeDescPi.piElim (functionSR functionStep) argumentTyped
  · subst reductEq
    have rebuilt :
        HasTypeDescPi profile context (appCell functionTerm argumentAfter)
          (RawTerm.subst0 codomainCode argumentAfter) :=
      HasTypeDescPi.piElim functionTyped (argumentSR argumentStep)
    have convMovedOutput :
        Conv (RawTerm.subst0 codomainCode argumentAfter) (RawTerm.subst0 codomainCode argument) :=
      Conv.subst0 (Conv.refl codomainCode)
        ⟨argumentAfter, StepStar.refl _, StepStar.single argumentStep⟩
    obtain ⟨classifierLevel, classifierFlag, classifierTyped⟩ :=
      (HasTypeDescPi.piElim functionTyped argumentTyped).classifierIsTypeDescPi wellFormed
    exact HasTypeDescPi.conv classifierLevel classifierFlag rebuilt convMovedOutput classifierTyped

#print axioms HasTypeDescPi.betaSubjectReductionDescPi
#print axioms HasTypeDescPi.subjectReductionPiElimArmDescPi

end FX1Poly.Typed
