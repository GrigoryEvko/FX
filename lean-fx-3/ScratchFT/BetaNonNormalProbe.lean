import FX1Poly.Typed.PiTypeFunctionInversion

namespace FX1Poly.Typed
open FX1Poly.Core FX1Poly.Universe

-- Probe 1: does app(lam body, a) compute to non-normal by rfl/simp?
theorem betaNotNormal_probe {scope : Nat} (body : RawTerm (scope + 1)) (argument : RawTerm scope)
    (normal : RawTerm.isStepNormalForm (appCell (lamCell body) argument)) : False := by
  unfold RawTerm.isStepNormalForm at normal
  simp only [] at normal
  exact absurd normal (by decide)

-- Probe 2: subterm-of-normal — app(f,a) normal → f normal
theorem appNormal_functionNormal_probe {scope : Nat} (functionTerm argument : RawTerm scope)
    (normal : RawTerm.isStepNormalForm (appCell functionTerm argument)) :
    RawTerm.isStepNormalForm functionTerm := by
  unfold RawTerm.isStepNormalForm at normal ⊢
  simp only [Bool.and_eq_true] at normal
  exact normal.2.1

end FX1Poly.Typed
