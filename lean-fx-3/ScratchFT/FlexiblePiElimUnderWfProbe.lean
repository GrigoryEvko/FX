import FX1Poly.Typed.HasTypeDescPiContextConversionValidityReduction
import FX1Poly.Typed.HasTypeDescPiSubjectReductionUnconditional

/-! Probe: the FLEXIBLE grown context-conversion piElim arm, UNCONDITIONAL under target well-formedness.
    A faithful copy of `piElimArmFromValidityRespectsReduction` (#1094) with the GLOBAL
    `TypeCodeValidityRespectsReduction` residual replaced by the now-shipped, well-formed-context-carrying
    `typeValiditySurvivesReductionUnderWf` (SR-U4 follow-on). This is the first UNCONDITIONAL discharge of
    the piElim context-conversion arm's residual (modulo the benign target `WfContextDescPi`). -/

namespace FX1Poly.Typed

open FX1Poly.Core FX1Poly.Universe FX1Poly.Foundation

theorem HasTypeDescPi.piElimArmUnderWfTargetProbe {profile : PolyProfile} {scope : Nat}
    {targetContext : TypingContext profile scope}
    {functionTerm argument domainCode : RawTerm scope} {codomainCode : RawTerm (scope + 1)}
    (targetWellFormed : WfContextDescPi targetContext)
    (functionFlexible : ∃ functionClassifier,
      Conv (piTyCodeCell domainCode codomainCode) functionClassifier ∧
        IsTypeDescPi profile targetContext functionClassifier)
    (functionConverted : ∃ functionClassifier,
      Conv (piTyCodeCell domainCode codomainCode) functionClassifier ∧
        HasTypeDescPi profile targetContext functionTerm functionClassifier)
    (argumentConverted : ∃ argumentClassifier,
      Conv domainCode argumentClassifier ∧
        HasTypeDescPi profile targetContext argument argumentClassifier) :
    ∃ classifier', Conv (RawTerm.subst0 codomainCode argument) classifier' ∧
      HasTypeDescPi profile targetContext (appCell functionTerm argument) classifier' := by
  obtain ⟨flexClassifier, convPiToFlex, flexValid⟩ := functionFlexible
  obtain ⟨reductDomain, reductCodomain, flexReducesToPi, convDomainReduct, convCodomainReduct⟩ :=
    Conv.reducesToPiTyCode convPiToFlex.sym
  have piReductValid : IsTypeDescPi profile targetContext
      (piTyCodeCell reductDomain reductCodomain) :=
    HasTypeDescPi.typeValiditySurvivesReductionUnderWf targetWellFormed flexValid flexReducesToPi
  exact HasTypeDescPi.reassembleApplicationFromConvEqualPiValidity functionConverted argumentConverted
    convDomainReduct convCodomainReduct piReductValid

end FX1Poly.Typed

#print axioms FX1Poly.Typed.HasTypeDescPi.piElimArmUnderWfTargetProbe
