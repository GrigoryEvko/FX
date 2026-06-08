import FX1Poly.Typed.UniverseCodeConversion

/-! SCRATCH: conv-injectivity on variables — Conv (var a) (var b) → a = b. -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

theorem variableCellInjOfConvProbe {scope : Nat} {leftIndex rightIndex : Fin scope}
    (conv : Conv (variableCell leftIndex : RawTerm scope) (variableCell rightIndex)) :
    leftIndex = rightIndex := by
  have leftIsNormal : RawTerm.isStepNormalForm (variableCell leftIndex : RawTerm scope) := rfl
  have rightIsNormal : RawTerm.isStepNormalForm (variableCell rightIndex : RawTerm scope) := rfl
  have codesEqual : (variableCell leftIndex : RawTerm scope) = variableCell rightIndex :=
    (Conv.iff_normalForms_eq_of_confluence (StepStar.refl _) leftIsNormal
      (StepStar.refl _) rightIsNormal).mp conv
  injection codesEqual with _generatorEq indexEq

end FX1Poly.Typed

#print axioms FX1Poly.Typed.variableCellInjOfConvProbe
