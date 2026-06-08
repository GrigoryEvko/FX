import FX1Poly.Typed.ConvCodeInjectivity

/-! SCRATCH: former-not-conv-variable rigidity twins (#662 conv-arm dispatch vacuous cases). -/

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

theorem Conv.piTyCode_not_variableCellProbe {scope : Nat}
    {piDomain : RawTerm scope} {piCodomain : RawTerm (scope + 1)} {index : Fin scope}
    (convertibility : Conv (piTyCodeCell piDomain piCodomain) (variableCell index)) :
    False := by
  obtain ⟨commonReduct, leftChain, rightChain⟩ := convertibility
  obtain ⟨_, _, leftCommonEq, _, _⟩ := StepStar.shapeStable_piTyCode leftChain
  have rightCommonEq :=
    StepStar.eq_of_noStep (fun _reduct step => StepStar.noStep_var index step) rightChain
  rw [leftCommonEq] at rightCommonEq
  exact Generator.noConfusion
    (congrArg RawTerm.headGenerator rightCommonEq :
      Generator.gen_piTyCode = Generator.gen_var)

theorem Conv.sigmaTyCode_not_variableCellProbe {scope : Nat}
    {sigmaDomain : RawTerm scope} {sigmaCodomain : RawTerm (scope + 1)} {index : Fin scope}
    (convertibility : Conv (sigmaTyCodeCell sigmaDomain sigmaCodomain) (variableCell index)) :
    False := by
  obtain ⟨commonReduct, leftChain, rightChain⟩ := convertibility
  obtain ⟨_, _, leftCommonEq, _, _⟩ := StepStar.shapeStable_sigmaTyCode leftChain
  have rightCommonEq :=
    StepStar.eq_of_noStep (fun _reduct step => StepStar.noStep_var index step) rightChain
  rw [leftCommonEq] at rightCommonEq
  exact Generator.noConfusion
    (congrArg RawTerm.headGenerator rightCommonEq :
      Generator.gen_sigmaTyCode = Generator.gen_var)

end FX1Poly.Typed

#print axioms FX1Poly.Typed.Conv.piTyCode_not_variableCellProbe
#print axioms FX1Poly.Typed.Conv.sigmaTyCode_not_variableCellProbe
